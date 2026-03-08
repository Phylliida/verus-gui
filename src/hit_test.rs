use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::node::Node;
use crate::size::Size;

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

/// If the point is outside the node bounds, hit_test returns None.
pub proof fn lemma_hit_test_none_outside<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        !point_in_node(node, px, py),
    ensures
        hit_test(node, px, py, fuel) == None::<Seq<nat>>,
{
}

/// If hit_test returns Some, the point must be within the node bounds.
pub proof fn lemma_hit_test_point_in_node<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        hit_test(node, px, py, fuel).is_Some(),
    ensures
        point_in_node(node, px, py),
{
}

/// Whether a hit-test path is valid: each index is within the child array bounds,
/// and the rest of the path is valid on that child.
pub open spec fn path_valid<T: OrderedRing>(node: Node<T>, path: Seq<nat>) -> bool
    decreases path.len(),
{
    if path.len() == 0 {
        true
    } else {
        let idx = path[0];
        idx < node.children.len()
        && path_valid(node.children[idx as int], path.subrange(1, path.len() as int))
    }
}

/// hit_test_scan returns valid paths: each index is in bounds.
proof fn lemma_hit_test_scan_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    index: nat,
    depth: nat,
)
    requires
        hit_test_scan(node, px, py, index, depth).is_Some(),
    ensures
        path_valid(node, hit_test_scan(node, px, py, index, depth).unwrap()),
    decreases depth, index,
{
    if index == 0 || depth == 0 {
        // Returns None, contradicts precondition
    } else {
        let i = (index - 1) as nat;
        if i >= node.children.len() {
            // Returns None, contradicts precondition
        } else {
            let child = node.children[i as int];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            let result = hit_test_inner(child, local_x, local_y, (depth - 1) as nat);
            match result {
                Some(sub_path) => {
                    // hit_test_scan returns Some([i] ++ sub_path)
                    // Need: i < children.len (true) and path_valid(children[i], sub_path)
                    lemma_hit_test_inner_path_valid(child, local_x, local_y, (depth - 1) as nat);
                    // sub_path is valid on child = node.children[i]
                    // path = [i] ++ sub_path
                    let path = Seq::empty().push(i).add(sub_path);
                    // path[0] = i < children.len ✓
                    // path.subrange(1, path.len()) = sub_path
                    assert(path.subrange(1, path.len() as int) =~= sub_path);
                },
                None => {
                    // Recurse on hit_test_scan with index = i
                    lemma_hit_test_scan_path_valid(node, px, py, i, depth);
                },
            }
        }
    }
}

/// hit_test_inner returns valid paths.
proof fn lemma_hit_test_inner_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    depth: nat,
)
    requires
        hit_test_inner(node, px, py, depth).is_Some(),
    ensures
        path_valid(node, hit_test_inner(node, px, py, depth).unwrap()),
    decreases depth, node.children.len() + 1,
{
    if !point_in_node(node, px, py) {
        // Returns None, contradicts precondition
    } else {
        let child_hit = hit_test_scan(node, px, py, node.children.len(), depth);
        match child_hit {
            Some(path) => {
                lemma_hit_test_scan_path_valid(node, px, py, node.children.len(), depth);
            },
            None => {
                // Returns Some(Seq::empty()), path_valid for empty is true
            },
        }
    }
}

/// If hit_test returns Some(path), the path is valid: every index is within
/// the corresponding child array.
pub proof fn lemma_hit_test_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        hit_test(node, px, py, fuel).is_Some(),
    ensures
        path_valid(node, hit_test(node, px, py, fuel).unwrap()),
{
    lemma_hit_test_inner_path_valid(node, px, py, fuel);
}

// ── ScrollView clipping ───────────────────────────────────────────

/// Construct a ScrollView-shaped node: viewport at (0,0) with size (vw, vh),
/// containing a single child offset by (-scroll_x, -scroll_y).
pub open spec fn scrollview_node<T: OrderedRing>(
    viewport_w: T,
    viewport_h: T,
    scroll_x: T,
    scroll_y: T,
    child: Node<T>,
) -> Node<T> {
    Node {
        x: T::zero(),
        y: T::zero(),
        size: Size::new(viewport_w, viewport_h),
        children: Seq::empty().push(Node {
            x: scroll_x.neg(),
            y: scroll_y.neg(),
            size: child.size,
            children: child.children,
        }),
    }
}

/// If hit_test on a ScrollView returns Some, the point is inside the viewport.
pub proof fn lemma_scrollview_clips<T: OrderedRing>(
    viewport_w: T,
    viewport_h: T,
    scroll_x: T,
    scroll_y: T,
    child: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        hit_test(
            scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child),
            px, py, fuel,
        ).is_Some(),
    ensures
        T::zero().le(px) && px.le(viewport_w),
        T::zero().le(py) && py.le(viewport_h),
{
    let sv = scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child);
    lemma_hit_test_point_in_node(sv, px, py, fuel);
    // point_in_node checks 0 <= px <= size.width = viewport_w
}

/// If the point is outside the viewport, hit_test on a ScrollView returns None.
pub proof fn lemma_scrollview_rejects_outside<T: OrderedRing>(
    viewport_w: T,
    viewport_h: T,
    scroll_x: T,
    scroll_y: T,
    child: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        !point_in_node(
            scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child),
            px, py,
        ),
    ensures
        hit_test(
            scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child),
            px, py, fuel,
        ) == None::<Seq<nat>>,
{
    let sv = scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child);
    lemma_hit_test_none_outside(sv, px, py, fuel);
}

/// When hit_test on a single-child node returns a path through the child,
/// the child was hit-tested at local coordinates (px - child.x, py - child.y).
///
/// For a ScrollView with child at (-scroll_x, -scroll_y), the local coords
/// are (px + scroll_x, py + scroll_y).
pub proof fn lemma_hit_test_child_offset<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        fuel > 0,
        node.children.len() == 1,
        hit_test(node, px, py, fuel).is_Some(),
        hit_test(node, px, py, fuel).unwrap().len() > 0,
    ensures
        ({
            let path = hit_test(node, px, py, fuel).unwrap();
            let child = node.children[0];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            // The child index is 0, and the rest of the path comes from
            // hit_test_inner on the child at local coords
            &&& path[0] == 0nat
            &&& hit_test_inner(child, local_x, local_y, (fuel - 1) as nat).is_Some()
            &&& path.subrange(1, path.len() as int)
                === hit_test_inner(child, local_x, local_y, (fuel - 1) as nat).unwrap()
        }),
{
    lemma_hit_test_point_in_node(node, px, py, fuel);
    let child = node.children[0];
    let local_x = px.sub(child.x);
    let local_y = py.sub(child.y);
    let child_result = hit_test_inner(child, local_x, local_y, (fuel - 1) as nat);

    // Explicit unfolding: hit_test_scan(node, px, py, 0, fuel) == None
    assert(hit_test_scan(node, px, py, 0, fuel) == None::<Seq<nat>>);

    // hit_test_scan(node, px, py, 1, fuel) depends on child_result
    match child_result {
        Some(sub_path) => {
            // scan returns Some([0] ++ sub_path)
            let full_path = Seq::empty().push(0nat).add(sub_path);
            assert(hit_test_scan(node, px, py, 1, fuel) == Some(full_path));
            // hit_test_inner(node) returns Some(full_path)
            assert(hit_test(node, px, py, fuel) == Some(full_path));
            let path = hit_test(node, px, py, fuel).unwrap();
            assert(path =~= full_path);
            assert(path[0] == 0nat);
            assert(path.subrange(1, path.len() as int) =~= sub_path);
        },
        None => {
            // scan falls through: hit_test_scan(node, px, py, 0, fuel) = None
            assert(hit_test_scan(node, px, py, 1, fuel) == None::<Seq<nat>>);
            // hit_test_inner returns Some(Seq::empty())
            assert(hit_test(node, px, py, fuel) == Some(Seq::<nat>::empty()));
            // Contradicts path.len() > 0
            assert(false);
        },
    }
}

} // verus!
