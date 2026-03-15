use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::Alignment;
use crate::layout::*;
use crate::layout::proofs::*;
use crate::layout::stack::*;
use crate::layout::flex::*;
use crate::layout::grid::*;
use crate::layout::wrap::*;
use crate::layout::absolute::*;
use crate::layout::listview::*;
use crate::widget::*;

verus! {

// ── Per-variant helpers ──────────────────────────────────────────────
// Each proves: the output size of the variant's layout function equals
// limits.resolve(something), then applies lemma_resolve_bounds.

/// Column: output.size == column_layout(...).size == limits.resolve(something).
proof fn lemma_column_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_column_body(limits, padding, spacing, alignment, child_nodes).size),
        layout_column_body(limits, padding, spacing, alignment, child_nodes).size.le(limits.max),
{
    reveal(column_layout);
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = column_layout(limits, padding, spacing, alignment, child_sizes);
    // merge_layout preserves .size
    assert(layout_column_body(limits, padding, spacing, alignment, child_nodes).size
        == layout.size);
    // column_layout returns limits.resolve(...)
    let total_height = padding.vertical().add(column_content_height(child_sizes, spacing));
    let s = Size::new(limits.max.width, total_height);
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

/// Row: output.size == row_layout(...).size == limits.resolve(something).
proof fn lemma_row_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_row_body(limits, padding, spacing, alignment, child_nodes).size),
        layout_row_body(limits, padding, spacing, alignment, child_nodes).size.le(limits.max),
{
    reveal(row_layout);
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = row_layout(limits, padding, spacing, alignment, child_sizes);
    assert(layout_row_body(limits, padding, spacing, alignment, child_nodes).size
        == layout.size);
    let total_width = padding.horizontal().add(row_content_width(child_sizes, spacing));
    let s = Size::new(total_width, limits.max.height);
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

/// Stack: output.size == stack_layout(...).size == limits.resolve(something).
proof fn lemma_stack_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_stack_body(limits, padding, h_align, v_align, child_nodes).size),
        layout_stack_body(limits, padding, h_align, v_align, child_nodes).size.le(limits.max),
{
    reveal(stack_layout);
    reveal(stack_content_size);
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = stack_layout(limits, padding, h_align, v_align, child_sizes);
    assert(layout_stack_body(limits, padding, h_align, v_align, child_nodes).size
        == layout.size);
    let content = stack_content_size(child_sizes);
    let s = Size::new(
        padding.horizontal().add(content.width),
        padding.vertical().add(content.height),
    );
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

/// Wrap: output.size == wrap_layout(...).size == limits.resolve(something).
proof fn lemma_wrap_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_wrap_body(limits, padding, h_spacing, v_spacing, child_nodes).size),
        layout_wrap_body(limits, padding, h_spacing, v_spacing, child_nodes).size.le(limits.max),
{
    reveal(wrap_layout);
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = wrap_layout(limits, padding, h_spacing, v_spacing, child_sizes);
    assert(layout_wrap_body(limits, padding, h_spacing, v_spacing, child_nodes).size
        == layout.size);
    let available_width = limits.max.width.sub(padding.horizontal());
    let content = wrap_content_size(child_sizes, h_spacing, v_spacing, available_width);
    let s = Size::new(
        padding.horizontal().add(content.width),
        padding.vertical().add(content.height),
    );
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

/// Flex column: output.size == flex_column_layout(...).size == limits.resolve(limits.max).
proof fn lemma_flex_column_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_flex_column_body(limits, padding, spacing, alignment, weights, child_nodes).size),
        layout_flex_column_body(limits, padding, spacing, alignment, weights, child_nodes).size.le(limits.max),
{
    reveal(flex_column_layout);
    let child_cross_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size.width);
    let layout = flex_column_layout(limits, padding, spacing, alignment, weights, child_cross_sizes);
    assert(layout_flex_column_body(limits, padding, spacing, alignment, weights, child_nodes).size
        == layout.size);
    assert(layout.size == limits.resolve(limits.max));
    lemma_resolve_bounds(limits, limits.max);
}

/// Flex row: output.size == flex_row_layout(...).size == limits.resolve(limits.max).
proof fn lemma_flex_row_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_flex_row_body(limits, padding, spacing, alignment, weights, child_nodes).size),
        layout_flex_row_body(limits, padding, spacing, alignment, weights, child_nodes).size.le(limits.max),
{
    reveal(flex_row_layout);
    let child_cross_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size.height);
    let layout = flex_row_layout(limits, padding, spacing, alignment, weights, child_cross_sizes);
    assert(layout_flex_row_body(limits, padding, spacing, alignment, weights, child_nodes).size
        == layout.size);
    assert(layout.size == limits.resolve(limits.max));
    lemma_resolve_bounds(limits, limits.max);
}

/// Grid: output.size == grid_layout(...).size == limits.resolve(something).
proof fn lemma_grid_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    child_nodes: Seq<Node<T>>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_grid_body(limits, padding, h_spacing, v_spacing,
            h_align, v_align, col_widths, row_heights, child_nodes).size),
        layout_grid_body(limits, padding, h_spacing, v_spacing,
            h_align, v_align, col_widths, row_heights, child_nodes).size.le(limits.max),
{
    reveal(grid_layout);
    let num_cols = col_widths.len();
    let num_rows = row_heights.len();
    let child_sizes_2d = Seq::new(num_rows, |r: int|
        Seq::new(num_cols, |c: int|
            child_nodes[(r * num_cols as int + c)].size
        )
    );
    let layout = grid_layout(limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, child_sizes_2d);
    assert(layout_grid_body(limits, padding, h_spacing, v_spacing,
        h_align, v_align, col_widths, row_heights, child_nodes).size
        == layout.size);
    let s = Size::new(
        padding.horizontal().add(grid_content_width(col_widths, h_spacing)),
        padding.vertical().add(grid_content_height(row_heights, v_spacing)),
    );
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

/// Absolute: output.size == absolute_layout(...).size == limits.resolve(something).
proof fn lemma_absolute_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    child_nodes: Seq<Node<T>>,
    child_offsets: Seq<(T, T)>,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_absolute_body(limits, padding, child_nodes, child_offsets).size),
        layout_absolute_body(limits, padding, child_nodes, child_offsets).size.le(limits.max),
{
    reveal(absolute_layout);
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let child_data = Seq::new(child_nodes.len(), |i: int|
        (child_offsets[i].0, child_offsets[i].1, child_nodes[i].size));
    let layout = absolute_layout(limits, padding, child_data);
    assert(layout_absolute_body(limits, padding, child_nodes, child_offsets).size
        == layout.size);
    let content = absolute_content_size(child_data);
    let s = Size::new(
        padding.horizontal().add(content.width),
        padding.vertical().add(content.height),
    );
    assert(layout.size == limits.resolve(s));
    lemma_resolve_bounds(limits, s);
}

// ── Main theorem ─────────────────────────────────────────────────────

/// For any widget with fuel > 0 and well-formed limits, the output size
/// is within [limits.min, limits.max] component-wise.
pub proof fn lemma_layout_widget_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 0,
    ensures
        limits.min.le(layout_widget(limits, widget, fuel).size),
        layout_widget(limits, widget, fuel).size.le(limits.max),
{
    match widget {
        Widget::Leaf { size } => {
            lemma_resolve_bounds(limits, size);
        },
        Widget::Column { padding, spacing, alignment, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            lemma_column_respects_limits(limits, padding, spacing, alignment, cn);
        },
        Widget::Row { padding, spacing, alignment, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            lemma_row_respects_limits(limits, padding, spacing, alignment, cn);
        },
        Widget::Stack { padding, h_align, v_align, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            lemma_stack_respects_limits(limits, padding, h_align, v_align, cn);
        },
        Widget::Wrap { padding, h_spacing, v_spacing, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            lemma_wrap_respects_limits(limits, padding, h_spacing, v_spacing, cn);
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
                    lemma_flex_column_respects_limits(
                        limits, padding, spacing, alignment, weights, cn,
                    );
                },
                FlexDirection::Row => {
                    let available_width = inner.max.width.sub(total_spacing);
                    let cn = flex_row_widget_child_nodes(
                        inner, children, weights, total_weight,
                        available_width, (fuel - 1) as nat,
                    );
                    lemma_flex_row_respects_limits(
                        limits, padding, spacing, alignment, weights, cn,
                    );
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
            lemma_grid_respects_limits(limits, padding, h_spacing, v_spacing,
                h_align, v_align, col_widths, row_heights, cn);
        },
        Widget::Absolute { padding, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
            let offsets = Seq::new(children.len(), |i: int|
                (children[i].x, children[i].y));
            lemma_absolute_respects_limits(limits, padding, cn, offsets);
        },
        Widget::Margin { margin, child } => {
            let inner = limits.shrink(margin.horizontal(), margin.vertical());
            let child_node = layout_widget(inner, *child, (fuel - 1) as nat);
            let total_w = margin.horizontal().add(child_node.size.width);
            let total_h = margin.vertical().add(child_node.size.height);
            let s = Size::new(total_w, total_h);
            lemma_resolve_bounds(limits, s);
        },
        Widget::Conditional { visible, child } => {
            if visible {
                let child_node = layout_widget(limits, *child, (fuel - 1) as nat);
                lemma_resolve_bounds(limits, child_node.size);
            } else {
                lemma_resolve_bounds(limits, Size::zero_size());
            }
        },
        Widget::SizedBox { inner_limits, child } => {
            let effective = limits.intersect(inner_limits);
            let child_node = layout_widget(effective, *child, (fuel - 1) as nat);
            lemma_resolve_bounds(limits, child_node.size);
        },
        Widget::AspectRatio { ratio, child } => {
            let w1 = limits.max.width;
            let h1 = w1.div(ratio);
            if h1.le(limits.max.height) {
                let eff = Limits {
                    min: limits.min,
                    max: Size::new(w1, h1),
                };
                let child_node = layout_widget(eff, *child, (fuel - 1) as nat);
                lemma_resolve_bounds(limits, child_node.size);
            } else {
                let h2 = limits.max.height;
                let w2 = h2.mul(ratio);
                let eff = Limits {
                    min: limits.min,
                    max: Size::new(w2, h2),
                };
                let child_node = layout_widget(eff, *child, (fuel - 1) as nat);
                lemma_resolve_bounds(limits, child_node.size);
            }
        },
        Widget::ScrollView { viewport, scroll_x, scroll_y, child } => {
            lemma_resolve_bounds(limits, viewport);
        },
        Widget::ListView { spacing, scroll_y, viewport, children } => {
            reveal(layout_listview_body);
            lemma_resolve_bounds(limits, viewport);
        },
        Widget::TextInput { preferred_size, .. } => {
            lemma_resolve_bounds(limits, preferred_size);
        },
    }
}

} // verus!
