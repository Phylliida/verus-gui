use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::widget::*;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::flex::*;
use crate::layout::grid::*;
use crate::layout::wrap::*;
use crate::layout::absolute::*;

verus! {

// ── Measure spec functions ─────────────────────────────────────────

/// Measure absolute children: recursively compute each child's preferred size.
pub open spec fn measure_absolute_children<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<AbsoluteChild<T>>,
    fuel: nat,
) -> Seq<Size<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| measure_widget(inner_limits, children[i].child, fuel))
}

/// Measure child sizes: recursively compute each child's preferred size.
pub open spec fn measure_children<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
) -> Seq<Size<T>>
    decreases fuel, 1nat,
{
    Seq::new(children.len(), |i: int| measure_widget(inner_limits, children[i], fuel))
}

/// Compute the preferred size of a widget within constraints, without
/// computing positions.
///
/// Equivalent to `layout_widget(limits, widget, fuel).size` — proved by
/// `lemma_measure_is_layout_size`.
pub open spec fn measure_widget<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
) -> Size<T>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Size::new(T::zero(), T::zero())
    } else {
        match widget {
            Widget::Leaf { size } => {
                limits.resolve(size)
            },
            Widget::Column { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let child_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let content_height = column_content_height(child_sizes, spacing);
                let total_height = padding.vertical().add(content_height);
                limits.resolve(Size::new(limits.max.width, total_height))
            },
            Widget::Row { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let child_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let content_width = row_content_width(child_sizes, spacing);
                let total_width = padding.horizontal().add(content_width);
                limits.resolve(Size::new(total_width, limits.max.height))
            },
            Widget::Stack { padding, h_align, v_align, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let child_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let content = stack_content_size(child_sizes);
                let total_width = padding.horizontal().add(content.width);
                let total_height = padding.vertical().add(content.height);
                limits.resolve(Size::new(total_width, total_height))
            },
            Widget::Wrap { padding, h_spacing, v_spacing, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let child_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let available_width = limits.max.width.sub(padding.horizontal());
                let content = wrap_content_size(
                    child_sizes, h_spacing, v_spacing, available_width,
                );
                let total_width = padding.horizontal().add(content.width);
                let total_height = padding.vertical().add(content.height);
                limits.resolve(Size::new(total_width, total_height))
            },
            Widget::Flex { .. } => {
                // Flex fills its limits: parent_size = limits.resolve(limits.max)
                limits.resolve(limits.max)
            },
            Widget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                           col_widths, row_heights, children } => {
                let content_w = grid_content_width(col_widths, h_spacing);
                let content_h = grid_content_height(row_heights, v_spacing);
                let tw = padding.horizontal().add(content_w);
                let th = padding.vertical().add(content_h);
                limits.resolve(Size::new(tw, th))
            },
            Widget::Absolute { padding, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let child_sizes = measure_absolute_children(inner, children, (fuel - 1) as nat);
                let child_data = Seq::new(children.len(), |i: int|
                    (children[i].x, children[i].y, child_sizes[i]));
                let content = absolute_content_size(child_data);
                let tw = padding.horizontal().add(content.width);
                let th = padding.vertical().add(content.height);
                limits.resolve(Size::new(tw, th))
            },
            Widget::Margin { margin, child } => {
                let inner = limits.shrink(margin.horizontal(), margin.vertical());
                let child_size = measure_widget(inner, *child, (fuel - 1) as nat);
                let tw = margin.horizontal().add(child_size.width);
                let th = margin.vertical().add(child_size.height);
                limits.resolve(Size::new(tw, th))
            },
            Widget::Conditional { visible, child } => {
                if visible {
                    let child_size = measure_widget(limits, *child, (fuel - 1) as nat);
                    limits.resolve(child_size)
                } else {
                    limits.resolve(Size::zero_size())
                }
            },
            Widget::SizedBox { inner_limits, child } => {
                let effective = limits.intersect(inner_limits);
                let child_size = measure_widget(effective, *child, (fuel - 1) as nat);
                limits.resolve(child_size)
            },
            Widget::AspectRatio { ratio, child } => {
                let w1 = limits.max.width;
                let h1 = w1.div(ratio);
                let child_size = if h1.le(limits.max.height) {
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w1, h1),
                    };
                    measure_widget(eff, *child, (fuel - 1) as nat)
                } else {
                    let h2 = limits.max.height;
                    let w2 = h2.mul(ratio);
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w2, h2),
                    };
                    measure_widget(eff, *child, (fuel - 1) as nat)
                };
                limits.resolve(child_size)
            },
        }
    }
}

// ── Per-variant size helpers (used by runtime ensures) ─────────────

/// Column container size from pre-measured child sizes.
pub open spec fn measure_column_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    let content_height = column_content_height(child_sizes, spacing);
    let total_height = padding.vertical().add(content_height);
    limits.resolve(Size::new(limits.max.width, total_height))
}

/// Row container size from pre-measured child sizes.
pub open spec fn measure_row_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    let content_width = row_content_width(child_sizes, spacing);
    let total_width = padding.horizontal().add(content_width);
    limits.resolve(Size::new(total_width, limits.max.height))
}

/// Stack container size from pre-measured child sizes.
pub open spec fn measure_stack_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    let content = stack_content_size(child_sizes);
    let total_width = padding.horizontal().add(content.width);
    let total_height = padding.vertical().add(content.height);
    limits.resolve(Size::new(total_width, total_height))
}

/// Flex container size: always fills limits.
pub open spec fn measure_flex_result<T: OrderedField>(
    limits: Limits<T>,
) -> Size<T> {
    limits.resolve(limits.max)
}

/// Grid container size from column widths and row heights.
pub open spec fn measure_grid_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
) -> Size<T> {
    let content_w = grid_content_width(col_widths, h_spacing);
    let content_h = grid_content_height(row_heights, v_spacing);
    let tw = padding.horizontal().add(content_w);
    let th = padding.vertical().add(content_h);
    limits.resolve(Size::new(tw, th))
}

/// Wrap container size from pre-measured child sizes.
pub open spec fn measure_wrap_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    let available_width = limits.max.width.sub(padding.horizontal());
    let content = wrap_content_size(child_sizes, h_spacing, v_spacing, available_width);
    let total_width = padding.horizontal().add(content.width);
    let total_height = padding.vertical().add(content.height);
    limits.resolve(Size::new(total_width, total_height))
}

/// Absolute container size from pre-measured child sizes and offsets.
pub open spec fn measure_absolute_result<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    children: Seq<AbsoluteChild<T>>,
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    let child_data = Seq::new(children.len(), |i: int|
        (children[i].x, children[i].y, child_sizes[i]));
    let content = absolute_content_size(child_data);
    let tw = padding.horizontal().add(content.width);
    let th = padding.vertical().add(content.height);
    limits.resolve(Size::new(tw, th))
}

/// Margin container size from pre-measured child size.
pub open spec fn measure_margin_result<T: OrderedField>(
    limits: Limits<T>,
    margin: Padding<T>,
    child_size: Size<T>,
) -> Size<T> {
    let tw = margin.horizontal().add(child_size.width);
    let th = margin.vertical().add(child_size.height);
    limits.resolve(Size::new(tw, th))
}

// ── Equivalence proof: measure == layout.size ──────────────────────

/// Helper: measure_children matches the sizes of widget_child_nodes.
proof fn lemma_measure_children_match<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    ensures
        measure_children(inner_limits, children, fuel)
            =~= Seq::new(
                widget_child_nodes(inner_limits, children, fuel).len(),
                |i: int| widget_child_nodes(inner_limits, children, fuel)[i].size,
            ),
    decreases fuel, 1nat,
{
    let mc = measure_children(inner_limits, children, fuel);
    let cn = widget_child_nodes(inner_limits, children, fuel);

    // Both are Seq::new with same length
    assert(mc.len() == cn.len());

    // Pointwise: mc[i] == cn[i].size
    assert forall|i: int| 0 <= i < children.len() implies
        mc[i] == cn[i].size
    by {
        lemma_measure_is_layout_size(inner_limits, children[i], fuel);
    }
}

/// Helper: measure_absolute_children matches the sizes of absolute_widget_child_nodes.
proof fn lemma_measure_absolute_children_match<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<AbsoluteChild<T>>,
    fuel: nat,
)
    ensures
        measure_absolute_children(inner_limits, children, fuel)
            =~= Seq::new(
                absolute_widget_child_nodes(inner_limits, children, fuel).len(),
                |i: int| absolute_widget_child_nodes(inner_limits, children, fuel)[i].size,
            ),
    decreases fuel, 1nat,
{
    let mc = measure_absolute_children(inner_limits, children, fuel);
    let cn = absolute_widget_child_nodes(inner_limits, children, fuel);
    assert(mc.len() == cn.len());
    assert forall|i: int| 0 <= i < children.len() implies
        mc[i] == cn[i].size
    by {
        lemma_measure_is_layout_size(inner_limits, children[i].child, fuel);
    }
}

/// Main equivalence: measure_widget computes layout_widget(...).size.
pub proof fn lemma_measure_is_layout_size<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    ensures
        measure_widget(limits, widget, fuel)
            == layout_widget(limits, widget, fuel).size,
    decreases fuel, 0nat,
{
    if fuel == 0 {
        // Both return Size::new(T::zero(), T::zero())
    } else {
        match widget {
            Widget::Leaf { size } => {
                // Both return limits.resolve(size)
            },
            Widget::Column { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                lemma_measure_children_match(inner, children, (fuel - 1) as nat);

                // child_sizes used by measure
                let m_sizes = measure_children(inner, children, (fuel - 1) as nat);
                // child nodes from layout
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                // child_sizes used by layout (extracted from nodes)
                let l_sizes = Seq::new(cn.len(), |i: int| cn[i].size);

                // From lemma: m_sizes =~= l_sizes
                assert(m_sizes =~= l_sizes);

                // layout_column_body computes column_layout then merge_layout
                // merge_layout preserves .size
                let layout = column_layout(limits, padding, spacing, alignment, l_sizes);
                assert(merge_layout(layout, cn).size == layout.size);

                // layout_widget returns merge_layout(column_layout(...), cn)
                assert(layout_widget(limits, widget, fuel).size == layout.size);

                // measure_widget returns limits.resolve(Size::new(limits.max.width, total_height))
                // which is exactly layout.size (= parent_size in column_layout)
            },
            Widget::Row { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                lemma_measure_children_match(inner, children, (fuel - 1) as nat);

                let m_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                let l_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
                assert(m_sizes =~= l_sizes);

                let layout = row_layout(limits, padding, spacing, alignment, l_sizes);
                assert(merge_layout(layout, cn).size == layout.size);
                assert(layout_widget(limits, widget, fuel).size == layout.size);
            },
            Widget::Stack { padding, h_align, v_align, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                lemma_measure_children_match(inner, children, (fuel - 1) as nat);

                let m_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                let l_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
                assert(m_sizes =~= l_sizes);

                let layout = stack_layout(limits, padding, h_align, v_align, l_sizes);
                assert(merge_layout(layout, cn).size == layout.size);
                assert(layout_widget(limits, widget, fuel).size == layout.size);
            },
            Widget::Wrap { padding, h_spacing, v_spacing, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                lemma_measure_children_match(inner, children, (fuel - 1) as nat);

                let m_sizes = measure_children(inner, children, (fuel - 1) as nat);
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                let l_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
                assert(m_sizes =~= l_sizes);

                let layout = wrap_layout(limits, padding, h_spacing, v_spacing, l_sizes);
                assert(merge_layout(layout, cn).size == layout.size);
                assert(layout_widget(limits, widget, fuel).size == layout.size);
            },
            Widget::Flex { padding, spacing, alignment, direction, children } => {
                // Flex fills limits.max regardless of direction
                // flex_column_layout / flex_row_layout both set parent_size = limits.resolve(limits.max)
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let weights = Seq::new(children.len(), |i: int| children[i].weight);
                let total_weight = sum_weights(weights, weights.len() as nat);
                let total_spacing = if children.len() > 0 {
                    repeated_add(spacing, (children.len() - 1) as nat)
                } else { T::zero() };

                match direction {
                    FlexDirection::Column => {
                        let ah = inner.max.height.sub(total_spacing);
                        let cn = flex_column_widget_child_nodes(
                            inner, children, weights, total_weight, ah, (fuel - 1) as nat);
                        let cs = Seq::new(cn.len(), |i: int| cn[i].size.width);
                        let layout = flex_column_layout(
                            limits, padding, spacing, alignment, weights, cs);
                        assert(merge_layout(layout, cn).size == layout.size);
                    },
                    FlexDirection::Row => {
                        let aw = inner.max.width.sub(total_spacing);
                        let cn = flex_row_widget_child_nodes(
                            inner, children, weights, total_weight, aw, (fuel - 1) as nat);
                        let cs = Seq::new(cn.len(), |i: int| cn[i].size.height);
                        let layout = flex_row_layout(
                            limits, padding, spacing, alignment, weights, cs);
                        assert(merge_layout(layout, cn).size == layout.size);
                    },
                }
            },
            Widget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                           col_widths, row_heights, children } => {
                // Grid parent size depends only on col_widths and row_heights
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = grid_widget_child_nodes(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), (fuel - 1) as nat);
                let num_cols = col_widths.len();
                let num_rows = row_heights.len();
                let cs_2d = Seq::new(num_rows, |r: int|
                    Seq::new(num_cols, |c: int|
                        cn[(r * num_cols as int + c)].size
                    )
                );
                let layout = grid_layout(
                    limits, padding, h_spacing, v_spacing, h_align, v_align,
                    col_widths, row_heights, cs_2d);
                assert(merge_layout(layout, cn).size == layout.size);
            },
            Widget::Absolute { padding, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                lemma_measure_absolute_children_match(inner, children, (fuel - 1) as nat);

                let m_sizes = measure_absolute_children(inner, children, (fuel - 1) as nat);
                let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
                let l_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
                assert(m_sizes =~= l_sizes);

                // measure computes child_data from m_sizes
                let m_data = Seq::new(children.len(), |i: int|
                    (children[i].x, children[i].y, m_sizes[i]));

                // layout_absolute_body computes child_data from cn
                let offsets = Seq::new(children.len(), |i: int|
                    (children[i].x, children[i].y));
                let body_data = Seq::new(cn.len(), |i: int|
                    (offsets[i].0, offsets[i].1, cn[i].size));
                assert(m_data =~= body_data);

                let layout = absolute_layout(limits, padding, body_data);
                assert(merge_layout(layout, cn).size == layout.size);
            },
            Widget::Margin { margin, child } => {
                let inner = limits.shrink(margin.horizontal(), margin.vertical());
                lemma_measure_is_layout_size(inner, *child, (fuel - 1) as nat);
                // measure returns limits.resolve(Size::new(tw, th))
                // layout returns Node { size: limits.resolve(Size::new(tw, th)), ... }
                // where tw/th are the same in both cases
            },
            Widget::Conditional { visible, child } => {
                if visible {
                    lemma_measure_is_layout_size(limits, *child, (fuel - 1) as nat);
                } else {
                    // Both return limits.resolve(Size::zero_size())
                }
            },
            Widget::SizedBox { inner_limits, child } => {
                let effective = limits.intersect(inner_limits);
                lemma_measure_is_layout_size(effective, *child, (fuel - 1) as nat);
            },
            Widget::AspectRatio { ratio, child } => {
                let w1 = limits.max.width;
                let h1 = w1.div(ratio);
                if h1.le(limits.max.height) {
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w1, h1),
                    };
                    lemma_measure_is_layout_size(eff, *child, (fuel - 1) as nat);
                } else {
                    let h2 = limits.max.height;
                    let w2 = h2.mul(ratio);
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w2, h2),
                    };
                    lemma_measure_is_layout_size(eff, *child, (fuel - 1) as nat);
                }
            },
        }
    }
}

// ── Fuel convergence for measure ───────────────────────────────────

/// Measure is fuel-monotone: extra fuel doesn't change the result when converged.
///
/// Follows from the equivalence with layout_widget.size and layout's fuel monotonicity.
pub proof fn lemma_measure_fuel_monotone<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires
        widget_converged(widget, fuel),
    ensures
        measure_widget(limits, widget, fuel)
            == measure_widget(limits, widget, fuel + 1),
{
    lemma_measure_is_layout_size(limits, widget, fuel);
    lemma_measure_is_layout_size(limits, widget, fuel + 1);
    lemma_layout_widget_fuel_monotone(limits, widget, fuel);
    // measure(fuel) == layout(fuel).size == layout(fuel+1).size == measure(fuel+1)
}

} // verus!
