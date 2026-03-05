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
use crate::layout::flex::*;
use crate::layout::grid::*;
use crate::layout::wrap::*;

verus! {

/// Flex layout direction.
pub enum FlexDirection {
    Column,
    Row,
}

/// A flex child with a weight.
#[verifier::reject_recursive_types(T)]
pub struct FlexItem<T: OrderedRing> {
    pub weight: T,
    pub child: Widget<T>,
}

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
    Flex {
        padding: Padding<T>,
        spacing: T,
        alignment: Alignment,
        direction: FlexDirection,
        children: Seq<FlexItem<T>>,
    },
    Grid {
        padding: Padding<T>,
        h_spacing: T,
        v_spacing: T,
        h_align: Alignment,
        v_align: Alignment,
        col_widths: Seq<Size<T>>,
        row_heights: Seq<Size<T>>,
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

/// Flex column layout body: given pre-computed child nodes, run flex_column_layout and merge.
pub open spec fn layout_flex_column_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = flex_column_layout(limits, padding, spacing, alignment, weights, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Flex row layout body.
pub open spec fn layout_flex_row_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = flex_row_layout(limits, padding, spacing, alignment, weights, child_sizes);
    merge_layout(layout, child_nodes)
}

/// Grid layout body: given pre-computed child nodes (flat, row-major), run grid_layout and merge.
pub open spec fn layout_grid_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let num_cols = col_widths.len();
    let num_rows = row_heights.len();
    let child_sizes_2d = Seq::new(num_rows, |r: int|
        Seq::new(num_cols, |c: int|
            child_nodes[(r * num_cols as int + c)].size
        )
    );
    let layout = grid_layout(limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, child_sizes_2d);
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

/// Compute child nodes for a flex column: each child gets per-weight limits.
pub open spec fn flex_column_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_height: T,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_height);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(inner.max.width, main_alloc),
        };
        layout_widget(child_lim, children[i].child, fuel)
    })
}

/// Compute child nodes for a flex row: each child gets per-weight limits.
pub open spec fn flex_row_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_width: T,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_width);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(main_alloc, inner.max.height),
        };
        layout_widget(child_lim, children[i].child, fuel)
    })
}

/// Compute child nodes for a grid: each child gets cell-sized limits.
pub open spec fn grid_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    children: Seq<Widget<T>>,
    num_cols: nat,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| {
        let r = i / num_cols as int;
        let c = i % num_cols as int;
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(col_widths[c].width, row_heights[r].height),
        };
        layout_widget(child_lim, children[i], fuel)
    })
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
            Widget::Flex { padding, spacing, alignment, direction, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let weights = Seq::new(children.len(), |i: int| children[i].weight);
                let total_weight = sum_weights(weights, weights.len() as nat);
                let total_spacing = if children.len() > 0 {
                    repeated_add(spacing, (children.len() - 1) as nat)
                } else { T::zero() };
                match direction {
                    FlexDirection::Column => {
                        let available_height = inner.max.height.sub(total_spacing);
                        let cn = flex_column_widget_child_nodes(
                            inner, children, weights, total_weight,
                            available_height, (fuel - 1) as nat,
                        );
                        layout_flex_column_body(
                            limits, padding, spacing, alignment, weights, cn,
                        )
                    },
                    FlexDirection::Row => {
                        let available_width = inner.max.width.sub(total_spacing);
                        let cn = flex_row_widget_child_nodes(
                            inner, children, weights, total_weight,
                            available_width, (fuel - 1) as nat,
                        );
                        layout_flex_row_body(
                            limits, padding, spacing, alignment, weights, cn,
                        )
                    },
                }
            },
            Widget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                           col_widths, row_heights, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = grid_widget_child_nodes(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), (fuel - 1) as nat,
                );
                layout_grid_body(
                    limits, padding, h_spacing, v_spacing, h_align, v_align,
                    col_widths, row_heights, cn,
                )
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
        Widget::Flex { children, .. } =>
            Seq::new(children.len(), |i: int| children[i].child),
        Widget::Grid { children, .. } => children,
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

/// Flex column child nodes are fuel-monotone.
proof fn lemma_flex_column_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_height: T,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel)
            == flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel + 1),
    decreases fuel, 1nat,
{
    assert forall|i: int| 0 <= i < children.len() implies {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_height);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(inner.max.width, main_alloc),
        };
        layout_widget(child_lim, children[i].child, fuel)
            == layout_widget(child_lim, children[i].child, fuel + 1)
    } by {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_height);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(inner.max.width, main_alloc),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i].child, fuel);
    }
    assert(flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel)
        =~= flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel + 1));
}

/// Flex row child nodes are fuel-monotone.
proof fn lemma_flex_row_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_width: T,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel)
            == flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel + 1),
    decreases fuel, 1nat,
{
    assert forall|i: int| 0 <= i < children.len() implies {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_width);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(main_alloc, inner.max.height),
        };
        layout_widget(child_lim, children[i].child, fuel)
            == layout_widget(child_lim, children[i].child, fuel + 1)
    } by {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_width);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(main_alloc, inner.max.height),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i].child, fuel);
    }
    assert(flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel)
        =~= flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel + 1));
}

/// Grid child nodes are fuel-monotone.
proof fn lemma_grid_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    children: Seq<Widget<T>>,
    num_cols: nat,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel),
    ensures
        grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel)
            == grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel + 1),
    decreases fuel, 1nat,
{
    assert forall|i: int| 0 <= i < children.len() implies {
        let r = i / num_cols as int;
        let c = i % num_cols as int;
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(col_widths[c].width, row_heights[r].height),
        };
        layout_widget(child_lim, children[i], fuel)
            == layout_widget(child_lim, children[i], fuel + 1)
    } by {
        let r = i / num_cols as int;
        let c = i % num_cols as int;
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(col_widths[c].width, row_heights[r].height),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i], fuel);
    }
    assert(grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel)
        =~= grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel + 1));
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
        Widget::Flex { padding, spacing, alignment, direction, children } => {
            assert(get_children(widget) =~=
                Seq::new(children.len(), |i: int| children[i].child));
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let weights = Seq::new(children.len(), |i: int| children[i].weight);
            let total_weight = sum_weights(weights, weights.len() as nat);
            let total_spacing = if children.len() > 0 {
                repeated_add(spacing, (children.len() - 1) as nat)
            } else { T::zero() };

            // Flex children converge via FlexItem.child
            if children.len() > 0 {
                match direction {
                    FlexDirection::Column => {
                        let ah = inner.max.height.sub(total_spacing);
                        lemma_flex_column_child_nodes_fuel_monotone(
                            inner, children, weights, total_weight, ah, (fuel - 1) as nat);
                        let cn = flex_column_widget_child_nodes(
                            inner, children, weights, total_weight, ah, (fuel - 1) as nat);
                        assert(cn =~= flex_column_widget_child_nodes(
                            inner, children, weights, total_weight, ah, fuel));
                    },
                    FlexDirection::Row => {
                        let aw = inner.max.width.sub(total_spacing);
                        lemma_flex_row_child_nodes_fuel_monotone(
                            inner, children, weights, total_weight, aw, (fuel - 1) as nat);
                        let cn = flex_row_widget_child_nodes(
                            inner, children, weights, total_weight, aw, (fuel - 1) as nat);
                        assert(cn =~= flex_row_widget_child_nodes(
                            inner, children, weights, total_weight, aw, fuel));
                    },
                }
            }
        },
        Widget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                       col_widths, row_heights, children } => {
            assert(get_children(widget) =~= children);
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            if children.len() > 0 {
                lemma_grid_child_nodes_fuel_monotone(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), (fuel - 1) as nat);
            }
            let cn = grid_widget_child_nodes(
                inner, col_widths, row_heights, children,
                col_widths.len(), (fuel - 1) as nat);
            assert(cn =~= grid_widget_child_nodes(
                inner, col_widths, row_heights, children,
                col_widths.len(), fuel));
        },
    }
}

} // verus!
