use vstd::prelude::*;
use crate::runtime::node::RuntimeNode;
use crate::node::Node;
use crate::hit_test::{hit_test, hit_test_inner, hit_test_scan, point_in_node};
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub fn hit_test_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    node: &RuntimeNode<R, V>,
    px: &R,
    py: &R,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        node.wf_deep(depth as nat),
        px.wf_spec(),
        py.wf_spec(),
    ensures
        match (out, hit_test::<V>(node.model@, px@, py@, depth as nat)) {
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

fn hit_test_inner_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    node: &RuntimeNode<R, V>,
    px: &R,
    py: &R,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        node.wf_deep(depth as nat),
        px.wf_spec(),
        py.wf_spec(),
    ensures
        match (out, hit_test_inner::<V>(node.model@, px@, py@, depth as nat)) {
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
    let zero = px.zero_like();
    if !(zero.le(px) && px.le(&node.size.width)) {
        return None;
    }
    let zero2 = py.zero_like();
    if !(zero2.le(py) && py.le(&node.size.height)) {
        return None;
    }

    let n = node.children.len();
    if depth == 0 || n == 0 {
        return Some(Vec::new());
    }

    let child_hit = hit_test_scan_exec(node, px, py, n, depth);
    match child_hit {
        Some(path) => Some(path),
        None => Some(Vec::new()),
    }
}

fn hit_test_scan_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    node: &RuntimeNode<R, V>,
    px: &R,
    py: &R,
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
        match (out, hit_test_scan::<V>(node.model@, px@, py@, index as nat, depth as nat)) {
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

    assert(node.children@[i as int].wf_deep((depth - 1) as nat));

    let child_x = node.children[i].x.copy();
    let child_y = node.children[i].y.copy();

    let local_x = px.sub(&child_x);
    let local_y = py.sub(&child_y);

    let result = hit_test_inner_exec(&node.children[i], &local_x, &local_y, depth - 1);
    match result {
        Some(sub_path) => {
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
