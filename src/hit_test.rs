use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::node::Node;
use crate::size::Size;
use crate::diff::nodes_deeply_eqv;
use crate::layout::congruence_proofs::{lemma_le_congruence_iff, lemma_sub_congruence};

verus! {

///  Whether a point (px, py) lies within the node's bounds [0, size].
pub open spec fn point_in_node<T: OrderedRing>(node: Node<T>, px: T, py: T) -> bool {
    T::zero().le(px) && px.le(node.size.width)
    && T::zero().le(py) && py.le(node.size.height)
}

///  Scan children in reverse [0..index) looking for a hit.
///  `depth` bounds the recursion depth for descending into children.
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
            //  Recurse into child: uses (depth-1, child.children.len()) < (depth, index)
            let result = hit_test_inner(child, local_x, local_y, (depth - 1) as nat);
            match result {
                Some(sub_path) => Some(Seq::empty().push(i).add(sub_path)),
                //  Try next child: uses (depth, i) < (depth, index) since i < index
                None => hit_test_scan(node, px, py, i, depth),
            }
        }
    }
}

///  Inner hit-test on a single node (checks bounds, then scans children).
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
        //  depth >= 0; scan children with full depth budget
        let child_hit = hit_test_scan(node, px, py, node.children.len(), depth);
        match child_hit {
            Some(path) => Some(path),
            None => Some(Seq::empty()),
        }
    }
}

///  Top-level hit-test. fuel bounds the tree depth explored.
pub open spec fn hit_test<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
) -> Option<Seq<nat>> {
    hit_test_inner(node, px, py, fuel)
}

///  If no children exist, hit_test returns Some(empty) for points in bounds.
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

///  If the point is outside the node bounds, hit_test returns None.
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

///  If hit_test returns Some, the point must be within the node bounds.
pub proof fn lemma_hit_test_point_in_node<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        hit_test(node, px, py, fuel) is Some,
    ensures
        point_in_node(node, px, py),
{
}

///  Whether a hit-test path is valid: each index is within the child array bounds,
///  and the rest of the path is valid on that child.
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

///  hit_test_scan returns valid paths: each index is in bounds.
proof fn lemma_hit_test_scan_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    index: nat,
    depth: nat,
)
    requires
        hit_test_scan(node, px, py, index, depth) is Some,
    ensures
        path_valid(node, hit_test_scan(node, px, py, index, depth).unwrap()),
    decreases depth, index,
{
    if index == 0 || depth == 0 {
        //  Returns None, contradicts precondition
    } else {
        let i = (index - 1) as nat;
        if i >= node.children.len() {
            //  Returns None, contradicts precondition
        } else {
            let child = node.children[i as int];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            let result = hit_test_inner(child, local_x, local_y, (depth - 1) as nat);
            match result {
                Some(sub_path) => {
                    //  hit_test_scan returns Some([i] ++ sub_path)
                    //  Need: i < children.len (true) and path_valid(children[i], sub_path)
                    lemma_hit_test_inner_path_valid(child, local_x, local_y, (depth - 1) as nat);
                    //  sub_path is valid on child = node.children[i]
                    //  path = [i] ++ sub_path
                    let path = Seq::empty().push(i).add(sub_path);
                    //  path[0] = i < children.len ✓
                    //  path.subrange(1, path.len()) = sub_path
                    assert(path.subrange(1, path.len() as int) =~= sub_path);
                },
                None => {
                    //  Recurse on hit_test_scan with index = i
                    lemma_hit_test_scan_path_valid(node, px, py, i, depth);
                },
            }
        }
    }
}

///  hit_test_inner returns valid paths.
proof fn lemma_hit_test_inner_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    depth: nat,
)
    requires
        hit_test_inner(node, px, py, depth) is Some,
    ensures
        path_valid(node, hit_test_inner(node, px, py, depth).unwrap()),
    decreases depth, node.children.len() + 1,
{
    if !point_in_node(node, px, py) {
        //  Returns None, contradicts precondition
    } else {
        let child_hit = hit_test_scan(node, px, py, node.children.len(), depth);
        match child_hit {
            Some(path) => {
                lemma_hit_test_scan_path_valid(node, px, py, node.children.len(), depth);
            },
            None => {
                //  Returns Some(Seq::empty()), path_valid for empty is true
            },
        }
    }
}

///  If hit_test returns Some(path), the path is valid: every index is within
///  the corresponding child array.
pub proof fn lemma_hit_test_path_valid<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        hit_test(node, px, py, fuel) is Some,
    ensures
        path_valid(node, hit_test(node, px, py, fuel).unwrap()),
{
    lemma_hit_test_inner_path_valid(node, px, py, fuel);
}

//  ── ScrollView clipping ───────────────────────────────────────────

///  Construct a ScrollView-shaped node: viewport at (0,0) with size (vw, vh),
///  containing a single child offset by (-scroll_x, -scroll_y).
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

///  If hit_test on a ScrollView returns Some, the point is inside the viewport.
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
        ) is Some,
    ensures
        T::zero().le(px) && px.le(viewport_w),
        T::zero().le(py) && py.le(viewport_h),
{
    let sv = scrollview_node(viewport_w, viewport_h, scroll_x, scroll_y, child);
    lemma_hit_test_point_in_node(sv, px, py, fuel);
    //  point_in_node checks 0 <= px <= size.width = viewport_w
}

///  If the point is outside the viewport, hit_test on a ScrollView returns None.
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

///  When hit_test on a single-child node returns a path through the child,
///  the child was hit-tested at local coordinates (px - child.x, py - child.y).
///
///  For a ScrollView with child at (-scroll_x, -scroll_y), the local coords
///  are (px + scroll_x, py + scroll_y).
pub proof fn lemma_hit_test_child_offset<T: OrderedRing>(
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
)
    requires
        fuel > 0,
        node.children.len() == 1,
        hit_test(node, px, py, fuel) is Some,
        hit_test(node, px, py, fuel).unwrap().len() > 0,
    ensures
        ({
            let path = hit_test(node, px, py, fuel).unwrap();
            let child = node.children[0];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            //  The child index is 0, and the rest of the path comes from
            //  hit_test_inner on the child at local coords
            &&& path[0] == 0nat
            &&& hit_test_inner(child, local_x, local_y, (fuel - 1) as nat) is Some
            &&& path.subrange(1, path.len() as int)
                === hit_test_inner(child, local_x, local_y, (fuel - 1) as nat).unwrap()
        }),
{
    lemma_hit_test_point_in_node(node, px, py, fuel);
    let child = node.children[0];
    let local_x = px.sub(child.x);
    let local_y = py.sub(child.y);
    let child_result = hit_test_inner(child, local_x, local_y, (fuel - 1) as nat);

    //  Explicit unfolding: hit_test_scan(node, px, py, 0, fuel) == None
    assert(hit_test_scan(node, px, py, 0, fuel) == None::<Seq<nat>>);

    //  hit_test_scan(node, px, py, 1, fuel) depends on child_result
    match child_result {
        Some(sub_path) => {
            //  scan returns Some([0] ++ sub_path)
            let full_path = Seq::empty().push(0nat).add(sub_path);
            assert(hit_test_scan(node, px, py, 1, fuel) == Some(full_path));
            //  hit_test_inner(node) returns Some(full_path)
            assert(hit_test(node, px, py, fuel) == Some(full_path));
            let path = hit_test(node, px, py, fuel).unwrap();
            assert(path =~= full_path);
            assert(path[0] == 0nat);
            assert(path.subrange(1, path.len() as int) =~= sub_path);
        },
        None => {
            //  scan falls through: hit_test_scan(node, px, py, 0, fuel) = None
            assert(hit_test_scan(node, px, py, 1, fuel) == None::<Seq<nat>>);
            //  hit_test_inner returns Some(Seq::empty())
            assert(hit_test(node, px, py, fuel) == Some(Seq::<nat>::empty()));
            //  Contradicts path.len() > 0
            assert(false);
        },
    }
}

//  ── Node local coordinates ───────────────────────────────────────

///  Walk the node tree along a path, accumulating coordinate offsets.
///  Returns the local coordinates within the node at the path endpoint.
pub open spec fn node_local_coords<T: OrderedRing>(
    node: Node<T>, path: Seq<nat>, px: T, py: T,
) -> (T, T)
    decreases path.len(),
{
    if path.len() == 0 {
        (px, py)
    } else {
        let idx = path[0];
        if idx >= node.children.len() {
            (px, py)  //  out of bounds: return current coords
        } else {
            let child = node.children[idx as int];
            node_local_coords(
                child,
                path.subrange(1, path.len() as int),
                px.sub(child.x),
                py.sub(child.y),
            )
        }
    }
}

///  For empty path, local coords are the input coords.
pub proof fn lemma_node_local_coords_empty<T: OrderedRing>(
    node: Node<T>, px: T, py: T,
)
    ensures node_local_coords(node, Seq::empty(), px, py) == (px, py),
{}

//  ── Hit-test congruence ─────────────────────────────────────────

///  point_in_node is congruent: eqv nodes give the same answer for eqv points.
pub proof fn lemma_point_in_node_congruence<T: OrderedField>(
    n1: Node<T>, n2: Node<T>,
    px1: T, px2: T, py1: T, py2: T,
)
    requires
        n1.size.width.eqv(n2.size.width),
        n1.size.height.eqv(n2.size.height),
        px1.eqv(px2), py1.eqv(py2),
    ensures
        point_in_node(n1, px1, py1) == point_in_node(n2, px2, py2),
{
    T::axiom_eqv_reflexive(T::zero());
    lemma_le_congruence_iff(T::zero(), T::zero(), px1, px2);
    lemma_le_congruence_iff(px1, px2, n1.size.width, n2.size.width);
    lemma_le_congruence_iff(T::zero(), T::zero(), py1, py2);
    lemma_le_congruence_iff(py1, py2, n1.size.height, n2.size.height);
}

///  hit_test_scan is congruent on deeply eqv nodes with eqv coordinates.
proof fn lemma_hit_test_scan_congruence<T: OrderedField>(
    n1: Node<T>, n2: Node<T>,
    px1: T, px2: T, py1: T, py2: T,
    index: nat, depth: nat,
)
    requires
        nodes_deeply_eqv(n1, n2, depth),
        px1.eqv(px2), py1.eqv(py2),
    ensures
        hit_test_scan(n1, px1, py1, index, depth)
            == hit_test_scan(n2, px2, py2, index, depth),
    decreases depth, index,
{
    if index == 0 || depth == 0 {
        //  Both return None
    } else {
        let i = (index - 1) as nat;
        if i >= n1.children.len() {
            //  Both return None (children same length)
        } else {
            let c1 = n1.children[i as int];
            let c2 = n2.children[i as int];
            //  Children are deeply eqv at depth-1
            assert(nodes_deeply_eqv(c1, c2, (depth - 1) as nat));
            //  Local coords eqv: px.sub(child.x) eqv
            lemma_sub_congruence(px1, px2, c1.x, c2.x);
            lemma_sub_congruence(py1, py2, c1.y, c2.y);
            let lx1 = px1.sub(c1.x);
            let lx2 = px2.sub(c2.x);
            let ly1 = py1.sub(c1.y);
            let ly2 = py2.sub(c2.y);
            //  Recurse into child
            lemma_hit_test_inner_congruence(c1, c2, lx1, lx2, ly1, ly2, (depth - 1) as nat);
            let r1 = hit_test_inner(c1, lx1, ly1, (depth - 1) as nat);
            let r2 = hit_test_inner(c2, lx2, ly2, (depth - 1) as nat);
            match r1 {
                Some(_) => {
                    //  Both return Some with same sub_path
                },
                None => {
                    //  Both recurse to next sibling
                    lemma_hit_test_scan_congruence(n1, n2, px1, px2, py1, py2, i, depth);
                },
            }
        }
    }
}

///  hit_test_inner is congruent on deeply eqv nodes with eqv coordinates.
proof fn lemma_hit_test_inner_congruence<T: OrderedField>(
    n1: Node<T>, n2: Node<T>,
    px1: T, px2: T, py1: T, py2: T,
    depth: nat,
)
    requires
        nodes_deeply_eqv(n1, n2, depth),
        px1.eqv(px2), py1.eqv(py2),
    ensures
        hit_test_inner(n1, px1, py1, depth)
            == hit_test_inner(n2, px2, py2, depth),
    decreases depth, n1.children.len() + 1,
{
    lemma_point_in_node_congruence(n1, n2, px1, px2, py1, py2);
    if !point_in_node(n1, px1, py1) {
        //  Both return None
    } else {
        lemma_hit_test_scan_congruence(n1, n2, px1, px2, py1, py2, n1.children.len(), depth);
    }
}

///  Master hit-test congruence: deeply eqv nodes produce the same hit-test
///  result for eqv coordinates.
pub proof fn lemma_hit_test_congruence<T: OrderedField>(
    n1: Node<T>, n2: Node<T>,
    px1: T, px2: T, py1: T, py2: T,
    fuel: nat,
)
    requires
        nodes_deeply_eqv(n1, n2, fuel),
        px1.eqv(px2), py1.eqv(py2),
    ensures
        hit_test(n1, px1, py1, fuel) == hit_test(n2, px2, py2, fuel),
{
    lemma_hit_test_inner_congruence(n1, n2, px1, px2, py1, py2, fuel);
}

//  ── Hit-test geometric containment ──────────────────────────────

///  A path is geometrically valid: at each step, the point (in local coords)
///  is within the node's bounds.
pub open spec fn path_geometrically_valid<T: OrderedRing>(
    node: Node<T>, path: Seq<nat>, px: T, py: T,
) -> bool
    decreases path.len(),
{
    point_in_node(node, px, py)
    && if path.len() == 0 {
        true
    } else {
        let idx = path[0];
        idx < node.children.len() && {
            let child = node.children[idx as int];
            let local_x = px.sub(child.x);
            let local_y = py.sub(child.y);
            path_geometrically_valid(
                child, path.subrange(1, path.len() as int), local_x, local_y)
        }
    }
}

///  hit_test_inner returns geometrically valid paths.
proof fn lemma_hit_test_inner_geometric<T: OrderedRing>(
    node: Node<T>, px: T, py: T, depth: nat,
)
    requires hit_test_inner(node, px, py, depth) is Some,
    ensures
        path_geometrically_valid(
            node, hit_test_inner(node, px, py, depth).unwrap(), px, py),
    decreases depth, node.children.len() + 1,
{
    //  hit_test_inner checks point_in_node first — that's the geometric containment
    lemma_hit_test_point_in_node(node, px, py, depth);
    //  point_in_node(node, px, py) ✓
    let result = hit_test_inner(node, px, py, depth);
    let path = result.unwrap();
    let child_hit = hit_test_scan(node, px, py, node.children.len(), depth);
    match child_hit {
        Some(child_path) => {
            //  path = child_path, which came from scan
            lemma_hit_test_scan_geometric(node, px, py, node.children.len(), depth);
        },
        None => {
            //  path = Seq::empty(), geometrically valid (just point_in_node)
        },
    }
}

///  hit_test_scan returns geometrically valid paths (given point_in_node).
proof fn lemma_hit_test_scan_geometric<T: OrderedRing>(
    node: Node<T>, px: T, py: T, index: nat, depth: nat,
)
    requires
        hit_test_scan(node, px, py, index, depth) is Some,
        point_in_node(node, px, py),
    ensures
        path_geometrically_valid(
            node, hit_test_scan(node, px, py, index, depth).unwrap(), px, py),
    decreases depth, index,
{
    if index == 0 || depth == 0 {
    } else {
        let i = (index - 1) as nat;
        if i >= node.children.len() {
        } else {
            let child = node.children[i as int];
            let lx = px.sub(child.x);
            let ly = py.sub(child.y);
            let child_result = hit_test_inner(child, lx, ly, (depth - 1) as nat);
            match child_result {
                Some(sub_path) => {
                    lemma_hit_test_inner_geometric(child, lx, ly, (depth - 1) as nat);
                    let full_path = Seq::empty().push(i).add(sub_path);
                    assert(full_path.subrange(1, full_path.len() as int) =~= sub_path);
                },
                None => {
                    lemma_hit_test_scan_geometric(node, px, py, i, depth);
                },
            }
        }
    }
}

///  Master: if hit_test returns Some(path), the point is within the node
///  at every step along the path (geometric containment, not just index validity).
pub proof fn lemma_hit_test_geometrically_valid<T: OrderedRing>(
    node: Node<T>, px: T, py: T, fuel: nat,
)
    requires hit_test(node, px, py, fuel) is Some,
    ensures
        path_geometrically_valid(
            node, hit_test(node, px, py, fuel).unwrap(), px, py),
{
    lemma_hit_test_inner_geometric(node, px, py, fuel);
}

} //  verus!
