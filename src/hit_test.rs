use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::node::Node;

verus! {

/// Whether a point (px, py) lies within the node's bounds [0, size].
pub open spec fn point_in_node<T: OrderedRing>(node: Node<T>, px: T, py: T) -> bool {
    T::zero().le(px) && px.le(node.size.width)
    && T::zero().le(py) && py.le(node.size.height)
}

/// Scan children in reverse [0..index) looking for a hit.
/// `depth` bounds the recursion depth for descending into children.
pub open spec fn hit_test_scan<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    index: nat,
    depth: nat,
) -> Option<Seq<nat>>
    decreases depth, index,
{
    if index == 0 || depth == 0 {
        None
    } else {
        let i = (index - 1) as nat;
        if i >= node.children.len() {
            None
        } else {
            let child = node.children[i as int];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            // Recurse into child: uses (depth-1, child.children.len()) < (depth, index)
            let result = hit_test_inner(child, local_x, local_y, (depth - 1) as nat);
            match result {
                Some(sub_path) => Some(Seq::empty().push(i).add(sub_path)),
                // Try next child: uses (depth, i) < (depth, index) since i < index
                None => hit_test_scan(node, px, py, i, depth),
            }
        }
    }
}

/// Inner hit-test on a single node (checks bounds, then scans children).
pub open spec fn hit_test_inner<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    depth: nat,
) -> Option<Seq<nat>>
    decreases depth, node.children.len() + 1,
{
    if !point_in_node(node, px, py) {
        None
    } else {
        // depth >= 0; scan children with full depth budget
        let child_hit = hit_test_scan(node, px, py, node.children.len(), depth);
        match child_hit {
            Some(path) => Some(path),
            None => Some(Seq::empty()),
        }
    }
}

/// Top-level hit-test. fuel bounds the tree depth explored.
pub open spec fn hit_test<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
) -> Option<Seq<nat>> {
    hit_test_inner(node, px, py, fuel)
}

/// If no children exist, hit_test returns Some(empty) for points in bounds.
pub proof fn lemma_hit_test_leaf<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        node.children.len() == 0,
        point_in_node(node, px, py),
    ensures
        hit_test(node, px, py, fuel) == Some(Seq::<nat>::empty()),
{
}

} // verus!
