use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};
use crate::layout::repeated_add;

verus! {

// ── Helper spec functions ───────────────────────────────────────────

/// Sum of the first `count` weights.
pub open spec fn sum_weights<T: OrderedRing>(
    weights: Seq<T>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        sum_weights(weights, (count - 1) as nat).add(weights[(count - 1) as int])
    }
}

/// Size allocated to a single flex child on the main axis:
/// weight / total_weight * available.
pub open spec fn flex_child_main_size<T: OrderedField>(
    weight: T,
    total_weight: T,
    available: T,
) -> T {
    weight.div(total_weight).mul(available)
}

/// Sum of main-axis sizes for children 0..count in a flex layout:
/// Σ (weights[i] / total_weight * available) for i in 0..count.
pub open spec fn flex_main_sum<T: OrderedField>(
    weights: Seq<T>,
    total_weight: T,
    available: T,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        flex_main_sum(weights, total_weight, available, (count - 1) as nat)
            .add(flex_child_main_size(weights[(count - 1) as int], total_weight, available))
    }
}

// ── Flex column layout ──────────────────────────────────────────────

/// Y-position of child at `index` in a flex column:
/// padding_top + Σ(flex sizes for 0..index) + index * spacing.
pub open spec fn flex_column_child_y<T: OrderedField>(
    padding_top: T,
    weights: Seq<T>,
    total_weight: T,
    available_height: T,
    spacing: T,
    index: nat,
) -> T {
    padding_top
        .add(flex_main_sum(weights, total_weight, available_height, index))
        .add(repeated_add(spacing, index))
}

/// Build child Nodes for a flex column layout.
pub open spec fn flex_column_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    h_align: Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    index: nat,
) -> Seq<Node<T>>
    decreases weights.len() - index,
{
    if index >= weights.len() {
        Seq::empty()
    } else {
        let child_h = flex_child_main_size(weights[index as int], total_weight, available_height);
        let child_w = child_cross_sizes[index as int];
        let child_x = padding.left.add(
            align_offset(h_align, available_width, child_w)
        );
        let child_y = flex_column_child_y(
            padding.top, weights, total_weight, available_height, spacing, index,
        );
        let child_node = Node::leaf(child_x, child_y, Size::new(child_w, child_h));
        Seq::empty().push(child_node).add(
            flex_column_children(padding, spacing, h_align, weights, child_cross_sizes,
                total_weight, available_width, available_height, index + 1)
        )
    }
}

/// Lay out children in a flex column (proportional vertical distribution).
///
/// Each child gets a fraction of the available height proportional to its weight.
/// The cross-axis (horizontal) uses alignment.
#[verifier::opaque]
pub open spec fn flex_column_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    h_align: Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
) -> Node<T> {
    let total_weight = sum_weights(weights, weights.len() as nat);
    let available_width = limits.max.width.sub(padding.horizontal());
    let total_spacing = if weights.len() == 0 {
        T::zero()
    } else {
        repeated_add(spacing, (weights.len() - 1) as nat)
    };
    let available_height = limits.max.height.sub(padding.vertical()).sub(total_spacing);
    let parent_size = limits.resolve(limits.max);
    let children = flex_column_children(
        padding, spacing, h_align, weights, child_cross_sizes,
        total_weight, available_width, available_height, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

// ── Flex row layout ─────────────────────────────────────────────────

/// X-position of child at `index` in a flex row.
pub open spec fn flex_row_child_x<T: OrderedField>(
    padding_left: T,
    weights: Seq<T>,
    total_weight: T,
    available_width: T,
    spacing: T,
    index: nat,
) -> T {
    padding_left
        .add(flex_main_sum(weights, total_weight, available_width, index))
        .add(repeated_add(spacing, index))
}

/// Build child Nodes for a flex row layout.
pub open spec fn flex_row_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    v_align: Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    index: nat,
) -> Seq<Node<T>>
    decreases weights.len() - index,
{
    if index >= weights.len() {
        Seq::empty()
    } else {
        let child_w = flex_child_main_size(weights[index as int], total_weight, available_width);
        let child_h = child_cross_sizes[index as int];
        let child_x = flex_row_child_x(
            padding.left, weights, total_weight, available_width, spacing, index,
        );
        let child_y = padding.top.add(
            align_offset(v_align, available_height, child_h)
        );
        let child_node = Node::leaf(child_x, child_y, Size::new(child_w, child_h));
        Seq::empty().push(child_node).add(
            flex_row_children(padding, spacing, v_align, weights, child_cross_sizes,
                total_weight, available_width, available_height, index + 1)
        )
    }
}

/// Lay out children in a flex row (proportional horizontal distribution).
#[verifier::opaque]
pub open spec fn flex_row_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    v_align: Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
) -> Node<T> {
    let total_weight = sum_weights(weights, weights.len() as nat);
    let available_height = limits.max.height.sub(padding.vertical());
    let total_spacing = if weights.len() == 0 {
        T::zero()
    } else {
        repeated_add(spacing, (weights.len() - 1) as nat)
    };
    let available_width = limits.max.width.sub(padding.horizontal()).sub(total_spacing);
    let parent_size = limits.resolve(limits.max);
    let children = flex_row_children(
        padding, spacing, v_align, weights, child_cross_sizes,
        total_weight, available_width, available_height, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

} // verus!
