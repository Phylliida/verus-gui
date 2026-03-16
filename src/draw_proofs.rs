use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::size::Size;
use crate::node::Node;
use crate::draw::*;

verus! {

// ── Count preservation ────────────────────────────────────────────────

/// Flattening a node produces exactly node_count draw commands.
pub proof fn lemma_flatten_preserves_count<T: OrderedRing>(
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    ensures
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel).len()
            == node_count::<T>(node, fuel),
    decreases fuel, 0nat,
{
    if fuel == 0 {
        // Base case: single draw command, node_count = 1
    } else {
        let abs_x = offset_x.add(node.x);
        let abs_y = offset_y.add(node.y);
        lemma_flatten_children_preserves_count(
            node.children, abs_x, abs_y, depth + 1, (fuel - 1) as nat, 0);
    }
}

/// Flattening children produces children_node_count draw commands.
pub proof fn lemma_flatten_children_preserves_count<T: OrderedRing>(
    children: Seq<Node<T>>,
    parent_abs_x: T,
    parent_abs_y: T,
    start_depth: nat,
    fuel: nat,
    from: nat,
)
    ensures
        flatten_children_to_draws(children, parent_abs_x, parent_abs_y, start_depth, fuel, from).len()
            == children_node_count::<T>(children, fuel, from),
    decreases fuel, children.len() - from,
{
    if from >= children.len() {
        // Empty: both are 0
    } else {
        lemma_flatten_preserves_count(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let first_draws = flatten_node_to_draws(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let next_depth = start_depth + first_draws.len();
        lemma_flatten_children_preserves_count(
            children, parent_abs_x, parent_abs_y, next_depth, fuel, from + 1);
    }
}

// ── Depth ordering ────────────────────────────────────────────────────

/// The first draw command in a flattened node has the given depth.
pub proof fn lemma_flatten_first_depth<T: OrderedRing>(
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    ensures
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel).len() > 0,
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel)[0].depth == depth,
{
    // Both fuel==0 and fuel>0 cases produce a first element with the given depth
}

// ── Structural identity ──────────────────────────────────────────────

/// If two nodes are structurally identical, their draw command
/// sequences are identical.
pub proof fn lemma_same_node_same_draws<T: OrderedRing>(
    node1: Node<T>,
    node2: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    requires
        node1 === node2,
    ensures
        flatten_node_to_draws(node1, offset_x, offset_y, depth, fuel)
            === flatten_node_to_draws(node2, offset_x, offset_y, depth, fuel),
{
    // Trivially true: node1 === node2 implies identical function application
}

} // verus!
