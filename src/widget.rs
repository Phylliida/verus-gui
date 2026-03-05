use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::Alignment;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;

verus! {

/// A composable layout widget that can nest heterogeneous layout strategies.
#[verifier::reject_recursive_types(T)]
pub enum Widget<T: OrderedRing> {
    Leaf { size: Size<T> },
    Column {
        padding: Padding<T>,
        spacing: T,
        alignment: Alignment,
        children: Seq<Widget<T>>,
    },
    Row {
        padding: Padding<T>,
        spacing: T,
        alignment: Alignment,
        children: Seq<Widget<T>>,
    },
    Stack {
        padding: Padding<T>,
        h_align: Alignment,
        v_align: Alignment,
        children: Seq<Widget<T>>,
    },
    Wrap {
        padding: Padding<T>,
        h_spacing: T,
        v_spacing: T,
        children: Seq<Widget<T>>,
    },
}

// ── Variant body helpers ───────────────────────────────────────────
// Extracted from layout_widget to enable shallow unfolding in proofs.

/// Column layout body: given pre-computed child nodes, run column_layout and merge.
pub open spec fn layout_column_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = column_layout(limits, padding, spacing, alignment, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Row layout body.
pub open spec fn layout_row_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = row_layout(limits, padding, spacing, alignment, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Stack layout body.
pub open spec fn layout_stack_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = stack_layout(limits, padding, h_align, v_align, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Wrap layout body.
pub open spec fn layout_wrap_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = wrap_layout(limits, padding, h_spacing, v_spacing, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Compute child nodes from children widgets at a given fuel.
pub open spec fn widget_child_nodes<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| layout_widget(inner_limits, children[i], fuel))
}

// ── Main layout function ───────────────────────────────────────────

/// Recursively lay out a widget tree, producing a positioned Node tree.
///
/// Uses fuel-based recursion (fuel must exceed tree depth).
pub open spec fn layout_widget<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
) -> Node<T>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Node {
            x: T::zero(),
            y: T::zero(),
            size: Size::new(T::zero(), T::zero()),
            children: Seq::empty(),
        }
    } else {
        match widget {
            Widget::Leaf { size } => {
                Node {
                    x: T::zero(),
                    y: T::zero(),
                    size: limits.resolve(size),
                    children: Seq::empty(),
                }
            },
            Widget::Column { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_column_body(limits, padding, spacing, alignment, cn)
            },
            Widget::Row { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_row_body(limits, padding, spacing, alignment, cn)
            },
            Widget::Stack { padding, h_align, v_align, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_stack_body(limits, padding, h_align, v_align, cn)
            },
            Widget::Wrap { padding, h_spacing, v_spacing, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_wrap_body(limits, padding, h_spacing, v_spacing, cn)
            },
        }
    }
}

/// Merge positions from a layout result with recursively-computed child Nodes.
pub open spec fn merge_layout<T: OrderedRing>(
    layout: Node<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    Node {
        x: layout.x,
        y: layout.y,
        size: layout.size,
        children: Seq::new(child_nodes.len(), |i: int| Node {
            x: layout.children[i].x,
            y: layout.children[i].y,
            size: child_nodes[i].size,
            children: child_nodes[i].children,
        }),
    }
}

// ── Widget depth and canonical entry point ─────────────────────────

/// Maximum of a sequence of natural numbers.
pub open spec fn seq_max_nat(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let rest = seq_max_nat(s.drop_last());
        let last = s.last();
        if last >= rest { last } else { rest }
    }
}

/// Extract the children sequence from any Widget variant.
pub open spec fn get_children<T: OrderedRing>(widget: Widget<T>) -> Seq<Widget<T>> {
    match widget {
        Widget::Leaf { .. } => Seq::empty(),
        Widget::Column { children, .. } => children,
        Widget::Row { children, .. } => children,
        Widget::Stack { children, .. } => children,
        Widget::Wrap { children, .. } => children,
    }
}

/// Compute the depth of a widget tree (fuel-bounded).
pub open spec fn widget_depth<T: OrderedRing>(widget: Widget<T>, fuel: nat) -> nat
    decreases fuel,
{
    if fuel == 0 {
        0
    } else {
        let children = get_children(widget);
        if children.len() == 0 {
            0
        } else {
            1 + seq_max_nat(Seq::new(children.len(), |i: int|
                widget_depth(children[i], (fuel - 1) as nat)
            ))
        }
    }
}

/// Canonical entry point: lay out a widget with sufficient fuel.
pub open spec fn layout_widget_full<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel_bound: nat,
) -> Node<T> {
    layout_widget(limits, widget, widget_depth(widget, fuel_bound) + 1)
}

// ── Fuel convergence ───────────────────────────────────────────────

/// Whether the widget tree has converged at the given fuel level.
///
/// A leaf always converges (at fuel >= 1). A container converges when
/// all its children have converged at fuel-1.
pub open spec fn widget_converged<T: OrderedRing>(widget: Widget<T>, fuel: nat) -> bool
    decreases fuel,
{
    if fuel == 0 {
        false
    } else {
        let children = get_children(widget);
        if children.len() == 0 {
            true
        } else {
            forall|i: int| 0 <= i < children.len() ==>
                widget_converged(children[i], (fuel - 1) as nat)
        }
    }
}

/// Extra fuel doesn't change child_nodes when children have converged.
proof fn lemma_child_nodes_fuel_monotone<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel),
    ensures
        widget_child_nodes(inner_limits, children, fuel)
            == widget_child_nodes(inner_limits, children, fuel + 1),
    decreases fuel, 1nat,
{
    assert forall|i: int| 0 <= i < children.len() implies
        layout_widget(inner_limits, children[i], fuel)
        == layout_widget(inner_limits, children[i], fuel + 1)
    by {
        lemma_layout_widget_fuel_monotone(inner_limits, children[i], fuel);
    }
    assert(widget_child_nodes(inner_limits, children, fuel)
        =~= widget_child_nodes(inner_limits, children, fuel + 1));
}

/// Extra fuel doesn't change the result when the widget has converged.
pub proof fn lemma_layout_widget_fuel_monotone<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires
        widget_converged(widget, fuel),
    ensures
        layout_widget(limits, widget, fuel) == layout_widget(limits, widget, fuel + 1),
    decreases fuel, 0nat,
{
    // widget_converged(widget, fuel) implies fuel >= 1
    assert(fuel >= 1nat);
    match widget {
        Widget::Leaf { .. } => {},
        Widget::Column { padding, spacing, alignment, children } => {
            assert(get_children(widget) =~= children);
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            if children.len() > 0 {
                lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
            }
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert(cn =~= widget_child_nodes(inner, children, fuel));
            assert(layout_widget(limits, widget, fuel)
                == layout_column_body(limits, padding, spacing, alignment, cn));
            assert(layout_widget(limits, widget, fuel + 1)
                == layout_column_body(limits, padding, spacing, alignment,
                    widget_child_nodes(inner, children, fuel)));
        },
        Widget::Row { padding, spacing, alignment, children } => {
            assert(get_children(widget) =~= children);
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            if children.len() > 0 {
                lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
            }
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert(cn =~= widget_child_nodes(inner, children, fuel));
            assert(layout_widget(limits, widget, fuel)
                == layout_row_body(limits, padding, spacing, alignment, cn));
            assert(layout_widget(limits, widget, fuel + 1)
                == layout_row_body(limits, padding, spacing, alignment,
                    widget_child_nodes(inner, children, fuel)));
        },
        Widget::Stack { padding, h_align, v_align, children } => {
            assert(get_children(widget) =~= children);
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            if children.len() > 0 {
                lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
            }
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert(cn =~= widget_child_nodes(inner, children, fuel));
            assert(layout_widget(limits, widget, fuel)
                == layout_stack_body(limits, padding, h_align, v_align, cn));
            assert(layout_widget(limits, widget, fuel + 1)
                == layout_stack_body(limits, padding, h_align, v_align,
                    widget_child_nodes(inner, children, fuel)));
        },
        Widget::Wrap { padding, h_spacing, v_spacing, children } => {
            assert(get_children(widget) =~= children);
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            if children.len() > 0 {
                lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
            }
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert(cn =~= widget_child_nodes(inner, children, fuel));
            assert(layout_widget(limits, widget, fuel)
                == layout_wrap_body(limits, padding, h_spacing, v_spacing, cn));
            assert(layout_widget(limits, widget, fuel + 1)
                == layout_wrap_body(limits, padding, h_spacing, v_spacing,
                    widget_child_nodes(inner, children, fuel)));
        },
    }
}

} // verus!
