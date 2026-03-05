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
use crate::layout::wrap::*;

verus! {

// ── Measure spec functions ─────────────────────────────────────────

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
