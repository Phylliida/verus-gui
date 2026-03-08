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

/// Deep equivalence: top-level fields eqv + children recursively eqv to given depth.
pub open spec fn nodes_deeply_eqv<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    depth: nat,
) -> bool
    decreases depth,
{
    a.x.eqv(b.x)
    && a.y.eqv(b.y)
    && a.size.width.eqv(b.size.width)
    && a.size.height.eqv(b.size.height)
    && a.children.len() == b.children.len()
    && (depth > 0 ==> forall|i: int| 0 <= i < a.children.len() ==>
        nodes_deeply_eqv(a.children[i], b.children[i], (depth - 1) as nat))
}

/// diff_nodes returning Same implies deep equivalence to depth fuel-1.
/// (At fuel=f, children are compared with fuel f-1, so field eqv holds to depth f-1.)
pub proof fn lemma_diff_same_implies_deeply_eqv<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes::<T>(old, new, fuel) === DiffResult::<T>::Same,
    ensures
        nodes_deeply_eqv(old, new, (fuel - 1) as nat),
    decreases fuel,
{
    lemma_diff_same_implies_children_eqv::<T>(old, new, fuel);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < old.children.len() implies
            nodes_deeply_eqv(
                old.children[i], new.children[i], (fuel - 2) as nat,
            )
        by {
            // diff_nodes(child_old, child_new, fuel-1) === Same
            lemma_diff_same_implies_deeply_eqv::<T>(
                old.children[i], new.children[i], (fuel - 1) as nat,
            );
        };
    }
}

/// Deep equivalence is reflexive.
pub proof fn lemma_deeply_eqv_reflexive<T: OrderedRing>(node: Node<T>, depth: nat)
    ensures
        nodes_deeply_eqv(node, node, depth),
    decreases depth,
{
    T::axiom_eqv_reflexive(node.x);
    T::axiom_eqv_reflexive(node.y);
    T::axiom_eqv_reflexive(node.size.width);
    T::axiom_eqv_reflexive(node.size.height);
    if depth > 0 {
        assert forall|i: int| 0 <= i < node.children.len() implies
            nodes_deeply_eqv(node.children[i], node.children[i], (depth - 1) as nat)
        by {
            lemma_deeply_eqv_reflexive::<T>(node.children[i], (depth - 1) as nat);
        };
    }
}

/// Deep equivalence is symmetric.
pub proof fn lemma_deeply_eqv_symmetric<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    depth: nat,
)
    requires
        nodes_deeply_eqv(a, b, depth),
    ensures
        nodes_deeply_eqv(b, a, depth),
    decreases depth,
{
    T::axiom_eqv_symmetric(a.x, b.x);
    T::axiom_eqv_symmetric(a.y, b.y);
    T::axiom_eqv_symmetric(a.size.width, b.size.width);
    T::axiom_eqv_symmetric(a.size.height, b.size.height);
    if depth > 0 {
        assert forall|i: int| 0 <= i < b.children.len() implies
            nodes_deeply_eqv(b.children[i], a.children[i], (depth - 1) as nat)
        by {
            lemma_deeply_eqv_symmetric::<T>(
                a.children[i], b.children[i], (depth - 1) as nat,
            );
        };
    }
}

/// Deep equivalence is transitive.
pub proof fn lemma_deeply_eqv_transitive<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    c: Node<T>,
    depth: nat,
)
    requires
        nodes_deeply_eqv(a, b, depth),
        nodes_deeply_eqv(b, c, depth),
    ensures
        nodes_deeply_eqv(a, c, depth),
    decreases depth,
{
    T::axiom_eqv_transitive(a.x, b.x, c.x);
    T::axiom_eqv_transitive(a.y, b.y, c.y);
    T::axiom_eqv_transitive(a.size.width, b.size.width, c.size.width);
    T::axiom_eqv_transitive(a.size.height, b.size.height, c.size.height);
    if depth > 0 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_deeply_eqv(a.children[i], c.children[i], (depth - 1) as nat)
        by {
            lemma_deeply_eqv_transitive::<T>(
                a.children[i], b.children[i], c.children[i], (depth - 1) as nat,
            );
        };
    }
}

// ── Diff Same symmetry ─────────────────────────────────────────

/// If diff_nodes(a, b) is Same, then diff_nodes(b, a) is Same (symmetry).
pub proof fn lemma_diff_symmetric_same<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes::<T>(a, b, fuel) === DiffResult::<T>::Same,
    ensures
        diff_nodes::<T>(b, a, fuel) === DiffResult::<T>::Same,
    decreases fuel, 0nat,
{
    lemma_diff_same_implies_children_eqv::<T>(a, b, fuel);
    // a.x.eqv(b.x), etc. → reverse via symmetric
    T::axiom_eqv_symmetric(a.x, b.x);
    T::axiom_eqv_symmetric(a.y, b.y);
    T::axiom_eqv_symmetric(a.size.width, b.size.width);
    T::axiom_eqv_symmetric(a.size.height, b.size.height);
    // Children: diff_nodes(a.children[i], b.children[i], fuel-1) === Same for all i
    // Need: diff_children(b, a, len, fuel-1).len() == 0
    lemma_diff_children_symmetric_same::<T>(a, b, a.children.len(), (fuel - 1) as nat);
}

/// Helper: if all children diffs a→b are Same, then all children diffs b→a are Same.
proof fn lemma_diff_children_symmetric_same<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    count: nat,
    fuel: nat,
)
    requires
        count <= a.children.len(),
        a.children.len() == b.children.len(),
        forall|i: int| 0 <= i < count ==>
            diff_nodes::<T>(a.children[i], b.children[i], fuel) === DiffResult::<T>::Same,
    ensures
        diff_children::<T>(b, a, count, fuel).len() == 0,
    decreases fuel, count,
{
    if count > 0 {
        lemma_diff_children_symmetric_same::<T>(a, b, (count - 1) as nat, fuel);
        if fuel > 0 {
            lemma_diff_symmetric_same::<T>(
                a.children[(count - 1) as int],
                b.children[(count - 1) as int],
                fuel,
            );
        }
        // When fuel == 0, diff_nodes returns Same by definition
    }
}

// ── Diff Same transitivity ────────────────────────────────────────

/// If diff_nodes(a,b) and diff_nodes(b,c) are both Same, then diff_nodes(a,c) is Same.
pub proof fn lemma_diff_transitive_same<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    c: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes::<T>(a, b, fuel) === DiffResult::<T>::Same,
        diff_nodes::<T>(b, c, fuel) === DiffResult::<T>::Same,
    ensures
        diff_nodes::<T>(a, c, fuel) === DiffResult::<T>::Same,
    decreases fuel, 0nat,
{
    lemma_diff_same_implies_children_eqv::<T>(a, b, fuel);
    lemma_diff_same_implies_children_eqv::<T>(b, c, fuel);
    // Transitivity on fields
    T::axiom_eqv_transitive(a.x, b.x, c.x);
    T::axiom_eqv_transitive(a.y, b.y, c.y);
    T::axiom_eqv_transitive(a.size.width, b.size.width, c.size.width);
    T::axiom_eqv_transitive(a.size.height, b.size.height, c.size.height);
    // Children
    lemma_diff_children_transitive_same::<T>(
        a, b, c, a.children.len(), (fuel - 1) as nat,
    );
}

/// Helper: transitive children Same.
proof fn lemma_diff_children_transitive_same<T: OrderedRing>(
    a: Node<T>,
    b: Node<T>,
    c: Node<T>,
    count: nat,
    fuel: nat,
)
    requires
        count <= a.children.len(),
        a.children.len() == b.children.len(),
        b.children.len() == c.children.len(),
        forall|i: int| 0 <= i < count ==>
            diff_nodes::<T>(a.children[i], b.children[i], fuel) === DiffResult::<T>::Same,
        forall|i: int| 0 <= i < count ==>
            diff_nodes::<T>(b.children[i], c.children[i], fuel) === DiffResult::<T>::Same,
    ensures
        diff_children::<T>(a, c, count, fuel).len() == 0,
    decreases fuel, count,
{
    if count > 0 {
        lemma_diff_children_transitive_same::<T>(a, b, c, (count - 1) as nat, fuel);
        if fuel > 0 {
            lemma_diff_transitive_same::<T>(
                a.children[(count - 1) as int],
                b.children[(count - 1) as int],
                c.children[(count - 1) as int],
                fuel,
            );
        }
    }
}

} // verus!
