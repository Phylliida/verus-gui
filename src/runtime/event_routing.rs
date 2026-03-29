use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::{RuntimeWidget, RuntimeLeafWidget, RuntimeWrapperWidget, RuntimeContainerWidget};
use crate::widget::*;
use crate::text_input::TextInputConfig;
use crate::text_model::session::*;
use crate::event_routing::*;
use crate::hit_test::node_local_coords;
use crate::node::Node;

verus! {

//  ── Helper: build sub-path from path[1..] ────────────────────────

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

//  ── Walk RuntimeWidget to find focused text_input_id ─────────────

///  Helper: get the child at index from a RuntimeWidget container variant.
///  Returns None if the widget has no children or index is out of bounds.
///  Proved: the returned child's model matches get_children(widget.model())[idx],
///  and the child inherits wf_spec(fuel - 1) from the parent's wf_spec(fuel).
fn get_runtime_child_at<'a>(
    widget: &'a RuntimeWidget,
    idx: usize,
    ghost_fuel: Ghost<nat>,
) -> (out: Option<&'a RuntimeWidget>)
    requires
        ghost_fuel@ > 0,
        widget.wf_spec(ghost_fuel@),
    ensures
        match out {
            Some(child) => {
                let spec_children = get_children::<RationalModel>(widget.model());
                &&& (idx as nat) < spec_children.len()
                &&& child.model() == spec_children[idx as int]
                &&& child.wf_spec((ghost_fuel@ - 1) as nat)
            },
            None => (idx as nat) >= get_children::<RationalModel>(widget.model()).len(),
        },
{
    match widget {
        RuntimeWidget::Leaf(_) => None,
        RuntimeWidget::Wrapper(w) => {
            match w {
                RuntimeWrapperWidget::Margin { child, .. } => {
                    if idx == 0 { Some(child) } else { None }
                },
                RuntimeWrapperWidget::Conditional { child, .. } => {
                    if idx == 0 { Some(child) } else { None }
                },
                RuntimeWrapperWidget::SizedBox { child, .. } => {
                    if idx == 0 { Some(child) } else { None }
                },
                RuntimeWrapperWidget::AspectRatio { child, .. } => {
                    if idx == 0 { Some(child) } else { None }
                },
                RuntimeWrapperWidget::ScrollView { child, .. } => {
                    if idx == 0 { Some(child) } else { None }
                },
            }
        },
        RuntimeWidget::Container(c) => {
            match c {
                RuntimeContainerWidget::Column { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
                RuntimeContainerWidget::Row { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
                RuntimeContainerWidget::Stack { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
                RuntimeContainerWidget::Wrap { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
                RuntimeContainerWidget::Flex { children, .. } => {
                    if idx < children.len() {
                        proof {
                            //  Help Z3: FlexItem.model().child == FlexItem.child.model()
                            assert(children@[idx as int].model().child
                                == children@[idx as int].child.model());
                        }
                        Some(&children[idx].child)
                    } else { None }
                },
                RuntimeContainerWidget::Grid { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
                RuntimeContainerWidget::Absolute { children, .. } => {
                    if idx < children.len() {
                        proof {
                            //  Help Z3: AbsoluteChild.model().child == AbsoluteChild.child.model()
                            assert(children@[idx as int].model().child
                                == children@[idx as int].child.model());
                        }
                        Some(&children[idx].child)
                    } else { None }
                },
                RuntimeContainerWidget::ListView { children, .. } => {
                    if idx < children.len() { Some(&children[idx]) } else { None }
                },
            }
        },
    }
}

///  Walk the RuntimeWidget tree along a path to find the text_input_id.
pub fn focused_text_input_id_exec(
    widget: &RuntimeWidget,
    path: &Vec<usize>,
    path_offset: usize,
) -> (out: Option<usize>)
    requires
        path_offset <= path@.len(),
        widget.wf_spec((path@.len() - path_offset + 1) as nat),
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
    let ghost fuel = (path@.len() - path_offset + 1) as nat;

    if path_offset == path.len() {
        proof {
            //  spec_path is empty ⇒ widget_at_path returns Some(widget.model())
            assert(spec_path =~= Seq::<nat>::empty());
            lemma_widget_at_path_empty::<RationalModel>(widget.model());
        }
        match widget {
            RuntimeWidget::Leaf(RuntimeLeafWidget::TextInput { text_input_id, .. }) => {
                //  widget.model() = Widget::Leaf(LeafWidget::TextInput { text_input_id: id, .. })
                //  focused_text_input_id matches ⇒ Some(id)
                return Some(*text_input_id);
            },
            RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf { .. }) => {
                return None;
            },
            RuntimeWidget::Wrapper(_) => {
                return None;
            },
            RuntimeWidget::Container(_) => {
                return None;
            },
        }
    }

    let idx = path[path_offset];
    let ghost gf = fuel;
    let child = get_runtime_child_at(widget, idx, Ghost(gf));
    match child {
        Some(c) => {
            proof {
                let spec_children = get_children::<RationalModel>(widget.model());
                //  From get_runtime_child_at ensures:
                //    c.model() == spec_children[idx]
                //    c.wf_spec(fuel - 1)

                assert(spec_path.len() > 0);
                assert(spec_path[0] == idx as nat);

                //  Connect spec_path[1..] to the recursive invocation's spec_path
                let sub_spec_path = Seq::new(
                    (path@.len() - (path_offset + 1)) as nat,
                    |i: int| path@[i + (path_offset + 1) as int] as nat,
                );
                assert(spec_path.subrange(1, spec_path.len() as int) =~= sub_spec_path);

                //  Unfold widget_at_path one step
                assert(widget_at_path::<RationalModel>(widget.model(), spec_path)
                    == widget_at_path::<RationalModel>(
                        spec_children[idx as int],
                        spec_path.subrange(1, spec_path.len() as int)));

                //  Chain: c.model() == spec_children[idx], sub_spec_path =~= spec_path[1..]
                assert(widget_at_path::<RationalModel>(widget.model(), spec_path)
                    == widget_at_path::<RationalModel>(c.model(), sub_spec_path));

                //  Therefore focused_text_input_id is the same for both
                assert(focused_text_input_id::<RationalModel>(widget.model(), spec_path)
                    == focused_text_input_id::<RationalModel>(c.model(), sub_spec_path));
            }
            focused_text_input_id_exec(c, path, path_offset + 1)
        },
        None => {
            proof {
                //  idx >= get_children(widget.model()).len()
                //  widget_at_path returns None when index is out of bounds
                assert(spec_path.len() > 0);
                assert(spec_path[0] == idx as nat);
            }
            None
        },
    }
}

//  ── Walk RuntimeNode to compute local coordinates ────────────────

///  Walk the RuntimeNode tree along a path, subtracting child offsets.
pub fn node_local_coords_exec(
    node: &RuntimeNode,
    path: &Vec<usize>,
    path_offset: usize,
    px: RuntimeRational,
    py: RuntimeRational,
) -> (out: (RuntimeRational, RuntimeRational))
    requires
        node.wf_deep((path@.len() - path_offset) as nat),
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

    proof {
        let depth = (path@.len() - path_offset) as nat;
        //  depth >= 1 since path_offset < path.len()
        assert(depth >= 1nat);
        //  wf_deep(depth >= 1) gives children's wf_deep and model correspondence
        assert(node.children@[idx as int].wf_deep((depth - 1) as nat));
        assert(node.children@[idx as int]@ == node@.children[idx as int]);
    }

    let child_x = copy_rational(&node.children[idx].x);
    let child_y = copy_rational(&node.children[idx].y);
    let local_x = px.sub(&child_x);
    let local_y = py.sub(&child_y);

    proof {
        let ghost spec_path = Seq::new((path@.len() - path_offset) as nat, |i: int|
            path@[i + path_offset as int] as nat);
        let ghost sub_spec_path = Seq::new(
            (path@.len() - (path_offset + 1)) as nat,
            |i: int| path@[i + (path_offset + 1) as int] as nat,
        );
        assert(spec_path[0] == idx as nat);
        assert(spec_path.subrange(1, spec_path.len() as int) =~= sub_spec_path);

        //  Connect local coords to spec
        assert(node.children@[idx as int].x@ == node.children@[idx as int]@.x);
        assert(child_x@ == node@.children[idx as int].x);
        assert(child_y@ == node@.children[idx as int].y);
    }

    node_local_coords_exec(&node.children[idx], path, path_offset + 1, local_x, local_y)
}

} //  verus!
