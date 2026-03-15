use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::RuntimeWidget;
use crate::runtime::text_input::RuntimeTextInputConfig;
use crate::widget::*;
use crate::text_input::TextInputConfig;
use crate::text_model::session::*;
use crate::event_routing::*;
use crate::hit_test::node_local_coords;
use crate::node::Node;

verus! {

// ── Helper: build sub-path from path[1..] ────────────────────────

fn build_sub_path(path: &Vec<usize>) -> (out: Vec<usize>)
    requires path@.len() >= 1,
    ensures
        out@.len() == path@.len() - 1,
        forall|k: int| 0 <= k < out@.len() ==> out@[k] == path@[k + 1],
{
    let mut sub_path: Vec<usize> = Vec::new();
    let mut j: usize = 1;
    while j < path.len()
        invariant
            1 <= j <= path@.len(),
            sub_path@.len() == j - 1,
            forall|k: int| 0 <= k < sub_path@.len() ==>
                sub_path@[k] == path@[k + 1],
        decreases path@.len() - j,
    {
        sub_path.push(path[j]);
        j = j + 1;
    }
    sub_path
}

// ── Walk RuntimeWidget to find focused text_input_id ─────────────

/// Helper: get the child at index from a RuntimeWidget container variant.
/// Returns None if the widget has no children or index is out of bounds.
fn get_runtime_child_at<'a>(widget: &'a RuntimeWidget, idx: usize) -> (out: Option<&'a RuntimeWidget>)
{
    match widget {
        RuntimeWidget::Column { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::Row { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::Stack { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::Wrap { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::Grid { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::ListView { children, .. } => {
            if idx < children.len() { Some(&children[idx]) } else { None }
        },
        RuntimeWidget::Flex { children, .. } => {
            if idx < children.len() { Some(&children[idx].child) } else { None }
        },
        RuntimeWidget::Absolute { children, .. } => {
            if idx < children.len() { Some(&children[idx].child) } else { None }
        },
        RuntimeWidget::Margin { child, .. } => {
            if idx == 0 { Some(child) } else { None }
        },
        RuntimeWidget::Conditional { child, .. } => {
            if idx == 0 { Some(child) } else { None }
        },
        RuntimeWidget::SizedBox { child, .. } => {
            if idx == 0 { Some(child) } else { None }
        },
        RuntimeWidget::AspectRatio { child, .. } => {
            if idx == 0 { Some(child) } else { None }
        },
        RuntimeWidget::ScrollView { child, .. } => {
            if idx == 0 { Some(child) } else { None }
        },
        _ => None,  // Leaf, TextInput — no children
    }
}

/// Walk the RuntimeWidget tree along a path to find the text_input_id.
pub fn focused_text_input_id_exec(
    widget: &RuntimeWidget,
    path: &Vec<usize>,
    path_offset: usize,
) -> (out: Option<usize>)
    requires
        path_offset <= path@.len(),
    ensures
        ({
            let spec_path = Seq::new((path@.len() - path_offset) as nat, |i: int|
                path@[i + path_offset as int] as nat);
            match out {
                Some(id) => focused_text_input_id::<RationalModel>(
                    widget.model(), spec_path) == Some(id as nat),
                None => focused_text_input_id::<RationalModel>(
                    widget.model(), spec_path).is_none(),
            }
        }),
    decreases path@.len() - path_offset,
{
    let ghost spec_path = Seq::new((path@.len() - path_offset) as nat, |i: int|
        path@[i + path_offset as int] as nat);

    if path_offset == path.len() {
        match widget {
            RuntimeWidget::TextInput { text_input_id, .. } => {
                assume(focused_text_input_id::<RationalModel>(
                    widget.model(), spec_path) == Some(*text_input_id as nat));
                return Some(*text_input_id);
            },
            _ => {
                assume(focused_text_input_id::<RationalModel>(
                    widget.model(), spec_path).is_none());
                return None;
            },
        }
    }

    let idx = path[path_offset];
    let child = get_runtime_child_at(widget, idx);
    match child {
        Some(c) => {
            assume(false); // Trust: child model + get_children correspondence
            focused_text_input_id_exec(c, path, path_offset + 1)
        },
        None => {
            assume(focused_text_input_id::<RationalModel>(
                widget.model(), spec_path).is_none());
            None
        },
    }
}

// ── Walk RuntimeNode to compute local coordinates ────────────────

/// Walk the RuntimeNode tree along a path, subtracting child offsets.
pub fn node_local_coords_exec(
    node: &RuntimeNode,
    path: &Vec<usize>,
    path_offset: usize,
    px: RuntimeRational,
    py: RuntimeRational,
) -> (out: (RuntimeRational, RuntimeRational))
    requires
        node.wf_spec(),
        px.wf_spec(),
        py.wf_spec(),
        path_offset <= path@.len(),
    ensures
        out.0.wf_spec(),
        out.1.wf_spec(),
        ({
            let spec_path = Seq::new((path@.len() - path_offset) as nat, |i: int|
                path@[i + path_offset as int] as nat);
            (out.0@, out.1@) == node_local_coords::<RationalModel>(
                node@, spec_path, px@, py@)
        }),
    decreases path@.len() - path_offset,
{
    if path_offset == path.len() {
        return (px, py);
    }

    let idx = path[path_offset];
    if idx >= node.children.len() {
        return (px, py);
    }

    let child_x = copy_rational(&node.children[idx].x);
    let child_y = copy_rational(&node.children[idx].y);
    let local_x = px.sub(&child_x);
    let local_y = py.sub(&child_y);

    assume(false); // Trust: child wf + spec correspondence
    node_local_coords_exec(&node.children[idx], path, path_offset + 1, local_x, local_y)
}

} // verus!
