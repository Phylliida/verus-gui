use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::node::Node;
use crate::size::Size;
use core::marker::PhantomData;

verus! {

/// Result of comparing two nodes.
/// T is a phantom type parameter needed for Verus height-based termination.
#[verifier::reject_recursive_types(T)]
pub enum DiffResult<T: OrderedRing> {
    Same,
    PositionChanged,
    SizeChanged,
    ChildCountChanged,
    ChildrenChanged { diffs: Seq<(nat, DiffResult<T>)>, _phantom: PhantomData<T> },
}

/// Compare two nodes, reporting what changed.
pub open spec fn diff_nodes<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    fuel: nat,
) -> DiffResult<T>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        DiffResult::<T>::Same
    } else if !old.x.eqv(new.x) || !old.y.eqv(new.y) {
        DiffResult::<T>::PositionChanged
    } else if !old.size.width.eqv(new.size.width) || !old.size.height.eqv(new.size.height) {
        DiffResult::<T>::SizeChanged
    } else if old.children.len() != new.children.len() {
        DiffResult::<T>::ChildCountChanged
    } else {
        let child_diffs = diff_children::<T>(old, new, old.children.len(), (fuel - 1) as nat);
        if child_diffs.len() == 0 {
            DiffResult::<T>::Same
        } else {
            DiffResult::<T>::ChildrenChanged { diffs: child_diffs, _phantom: PhantomData }
        }
    }
}

/// Diff children [0..count), collecting non-Same diffs.
pub open spec fn diff_children<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    count: nat,
    fuel: nat,
) -> Seq<(nat, DiffResult<T>)>
    decreases fuel, count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let i = (count - 1) as nat;
        let rest = diff_children::<T>(old, new, i, fuel);
        let d = diff_nodes::<T>(old.children[i as int], new.children[i as int], fuel);
        match d {
            DiffResult::Same => rest,
            _ => rest.push((i, d)),
        }
    }
}

/// Diffing a node with itself yields Same (reflexivity).
pub proof fn lemma_diff_reflexive<T: OrderedRing>(node: Node<T>, fuel: nat)
    requires fuel > 0,
    ensures diff_nodes::<T>(node, node, fuel) === DiffResult::<T>::Same,
    decreases fuel, 0nat,
{
    T::axiom_eqv_reflexive(node.x);
    T::axiom_eqv_reflexive(node.y);
    T::axiom_eqv_reflexive(node.size.width);
    T::axiom_eqv_reflexive(node.size.height);
    lemma_diff_children_reflexive::<T>(node, node.children.len(), (fuel - 1) as nat);
}

proof fn lemma_diff_children_reflexive<T: OrderedRing>(
    node: Node<T>,
    count: nat,
    fuel: nat,
)
    requires
        count <= node.children.len(),
    ensures
        diff_children::<T>(node, node, count, fuel).len() == 0,
    decreases fuel, count,
{
    if count > 0 {
        lemma_diff_children_reflexive::<T>(node, (count - 1) as nat, fuel);
        if fuel > 0 {
            lemma_diff_reflexive::<T>(node.children[(count - 1) as int], fuel);
        }
        // When fuel == 0, diff_nodes returns Same by definition
    }
}

/// If diff says Same (with fuel > 0), the top-level fields are actually equivalent.
pub proof fn lemma_diff_same_implies_eqv<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes::<T>(old, new, fuel) === DiffResult::<T>::Same,
    ensures
        old.x.eqv(new.x),
        old.y.eqv(new.y),
        old.size.width.eqv(new.size.width),
        old.size.height.eqv(new.size.height),
        old.children.len() == new.children.len(),
{
    // Verus unfolds diff_nodes. Each non-Same early return contradicts the precondition.
}

/// If diff_children returns empty, every child pair had Same.
proof fn lemma_diff_children_all_same<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    count: nat,
    fuel: nat,
)
    requires
        count <= old.children.len(),
        count <= new.children.len(),
        diff_children::<T>(old, new, count, fuel).len() == 0,
    ensures
        forall|i: nat| i < count ==>
            diff_nodes::<T>(old.children[i as int], new.children[i as int], fuel)
                === DiffResult::<T>::Same,
    decreases count,
{
    if count > 0 {
        // Unfold: result = if d is Same then rest else rest.push(...)
        // Since result.len() == 0, d must be Same and rest.len() == 0
        lemma_diff_children_all_same::<T>(old, new, (count - 1) as nat, fuel);
    }
}

/// Full recursive version: Same implies eqv at top level AND every child is Same.
pub proof fn lemma_diff_same_implies_children_eqv<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes::<T>(old, new, fuel) === DiffResult::<T>::Same,
    ensures
        old.x.eqv(new.x),
        old.y.eqv(new.y),
        old.size.width.eqv(new.size.width),
        old.size.height.eqv(new.size.height),
        old.children.len() == new.children.len(),
        forall|i: int| 0 <= i < old.children.len() ==>
            diff_nodes::<T>(old.children[i], new.children[i], (fuel - 1) as nat)
                === DiffResult::<T>::Same,
    decreases fuel,
{
    lemma_diff_same_implies_eqv::<T>(old, new, fuel);
    lemma_diff_children_all_same::<T>(old, new, old.children.len(), (fuel - 1) as nat);
}

} // verus!
