use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::size::Size;
use crate::node::Node;
use crate::widget::{Widget, get_children};

verus! {

//  ── Draw command type ─────────────────────────────────────────────────

///  A draw command: an axis-aligned rectangle with absolute screen coordinates
///  and a depth value (z-order from DFS traversal order).
#[verifier::reject_recursive_types(T)]
pub struct DrawCommand<T: OrderedRing> {
    pub x: T,
    pub y: T,
    pub width: T,
    pub height: T,
    pub depth: nat,
}

//  ── Flatten node tree to draw commands ────────────────────────────────

///  Count the total number of nodes in a Node tree.
pub open spec fn node_count<T: OrderedRing>(node: Node<T>, fuel: nat) -> nat
    decreases fuel, 0nat,
{
    if fuel == 0 {
        1
    } else {
        1 + children_node_count(node.children, (fuel - 1) as nat, 0)
    }
}

///  Count nodes across children starting from index `from`.
pub open spec fn children_node_count<T: OrderedRing>(
    children: Seq<Node<T>>,
    fuel: nat,
    from: nat,
) -> nat
    decreases fuel, children.len() - from,
{
    if from >= children.len() {
        0nat
    } else {
        node_count(children[from as int], fuel) +
            children_node_count(children, fuel, from + 1)
    }
}

///  Count widgets in a widget tree (fuel-bounded, like widget_depth).
///  When fuel exceeds widget_depth, this gives the exact widget count.
pub open spec fn widget_node_count<T: OrderedRing>(widget: Widget<T>, fuel: nat) -> nat
    decreases fuel, 0nat,
{
    if fuel == 0 {
        1
    } else {
        let children = get_children(widget);
        1 + widget_children_node_count(children, (fuel - 1) as nat, children.len())
    }
}

///  Sum of widget_node_count for children[0..count].
pub open spec fn widget_children_node_count<T: OrderedRing>(
    children: Seq<Widget<T>>, fuel: nat, count: nat,
) -> nat
    decreases fuel, count,
{
    if count == 0 || count > children.len() {
        0
    } else {
        widget_children_node_count(children, fuel, (count - 1) as nat)
            + widget_node_count(children[(count - 1) as int], fuel)
    }
}

///  Flatten a Node tree into a sequence of DrawCommands with absolute coordinates.
///
///  DFS traversal: emit current node first, then recursively emit children.
pub open spec fn flatten_node_to_draws<T: OrderedRing>(
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
) -> Seq<DrawCommand<T>>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Seq::empty().push(DrawCommand {
            x: offset_x.add(node.x),
            y: offset_y.add(node.y),
            width: node.size.width,
            height: node.size.height,
            depth,
        })
    } else {
        let self_draw = DrawCommand {
            x: offset_x.add(node.x),
            y: offset_y.add(node.y),
            width: node.size.width,
            height: node.size.height,
            depth,
        };
        let abs_x = offset_x.add(node.x);
        let abs_y = offset_y.add(node.y);
        Seq::empty().push(self_draw).add(
            flatten_children_to_draws(
                node.children, abs_x, abs_y, depth + 1, (fuel - 1) as nat, 0)
        )
    }
}

///  Flatten children starting from index `from`.
pub open spec fn flatten_children_to_draws<T: OrderedRing>(
    children: Seq<Node<T>>,
    parent_abs_x: T,
    parent_abs_y: T,
    start_depth: nat,
    fuel: nat,
    from: nat,
) -> Seq<DrawCommand<T>>
    decreases fuel, children.len() - from,
{
    if from >= children.len() {
        Seq::empty()
    } else {
        let first_draws = flatten_node_to_draws(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let next_depth = start_depth + first_draws.len();
        first_draws.add(
            flatten_children_to_draws(
                children, parent_abs_x, parent_abs_y,
                next_depth, fuel, from + 1)
        )
    }
}

///  Total number of draw commands produced by flattening.
pub open spec fn flatten_count<T: OrderedRing>(
    node: Node<T>,
    fuel: nat,
) -> nat {
    flatten_node_to_draws::<T>(node, T::zero(), T::zero(), 0, fuel).len()
}

} //  verus!
