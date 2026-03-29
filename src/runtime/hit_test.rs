use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::node::RuntimeNode;
use crate::node::Node;
use crate::hit_test::{hit_test, hit_test_inner, hit_test_scan, point_in_node};

verus! {

///  Runtime hit-test: find deepest node at (px, py).
///  Returns Some(path) as Vec<usize> or None.
pub fn hit_test_exec(
    node: &RuntimeNode,
    px: &RuntimeRational,
    py: &RuntimeRational,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        node.wf_deep(depth as nat),
        px.wf_spec(),
        py.wf_spec(),
    ensures
        match (out, hit_test::<RationalModel>(node@, px@, py@, depth as nat)) {
            (Some(exec_path), Some(spec_path)) => {
                exec_path@.len() == spec_path.len()
                && forall|i: int| 0 <= i < exec_path@.len() ==>
                    exec_path@[i] as nat == spec_path[i]
            },
            (None, None) => true,
            _ => false,
        },
{
    hit_test_inner_exec(node, px, py, depth)
}

///  Inner hit-test exec: check bounds, then scan children.
fn hit_test_inner_exec(
    node: &RuntimeNode,
    px: &RuntimeRational,
    py: &RuntimeRational,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        node.wf_deep(depth as nat),
        px.wf_spec(),
        py.wf_spec(),
    ensures
        match (out, hit_test_inner::<RationalModel>(node@, px@, py@, depth as nat)) {
            (Some(exec_path), Some(spec_path)) => {
                exec_path@.len() == spec_path.len()
                && forall|i: int| 0 <= i < exec_path@.len() ==>
                    exec_path@[i] as nat == spec_path[i]
            },
            (None, None) => true,
            _ => false,
        },
    decreases depth, node.children.len() + 1,
{
    //  Check point in bounds
    let zero1 = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    if !(zero1.le(px) && px.le(&node.size.width)) {
        return None;
    }
    if !(zero2.le(py) && py.le(&node.size.height)) {
        return None;
    }

    let n = node.children.len();
    if depth == 0 || n == 0 {
        //  No children to check, or no depth budget — this node is the hit
        return Some(Vec::new());
    }

    let child_hit = hit_test_scan_exec(node, px, py, n, depth);
    match child_hit {
        Some(path) => Some(path),
        None => Some(Vec::new()),
    }
}

///  Scan children in reverse [0..index).
fn hit_test_scan_exec(
    node: &RuntimeNode,
    px: &RuntimeRational,
    py: &RuntimeRational,
    index: usize,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        node.wf_deep(depth as nat),
        px.wf_spec(),
        py.wf_spec(),
        depth > 0,
        index <= node.children@.len(),
    ensures
        match (out, hit_test_scan::<RationalModel>(node@, px@, py@, index as nat, depth as nat)) {
            (Some(exec_path), Some(spec_path)) => {
                exec_path@.len() == spec_path.len()
                && forall|i: int| 0 <= i < exec_path@.len() ==>
                    exec_path@[i] as nat == spec_path[i]
            },
            (None, None) => true,
            _ => false,
        },
    decreases depth, index,
{
    if index == 0 {
        return None;
    }
    let i = index - 1;

    //  Child wf from parent's wf_deep
    assert(node.children@[i as int].wf_deep((depth - 1) as nat));

    //  Get child's position
    let child_x = copy_rational(&node.children[i].x);
    let child_y = copy_rational(&node.children[i].y);

    //  Transform to local coordinates
    let local_x = px.sub(&child_x);
    let local_y = py.sub(&child_y);

    let result = hit_test_inner_exec(&node.children[i], &local_x, &local_y, depth - 1);
    match result {
        Some(sub_path) => {
            //  Build path: [i] ++ sub_path
            let mut path: Vec<usize> = Vec::new();
            path.push(i);
            let mut j: usize = 0;
            while j < sub_path.len()
                invariant
                    0 <= j <= sub_path@.len(),
                    path@.len() == 1 + j,
                    path@[0] == i,
                    forall|k: int| 1 <= k < path@.len() ==>
                        path@[k] == sub_path@[k - 1],
                decreases sub_path@.len() - j,
            {
                path.push(sub_path[j]);
                j = j + 1;
            }
            Some(path)
        },
        None => {
            hit_test_scan_exec(node, px, py, i, depth)
        },
    }
}

} //  verus!
