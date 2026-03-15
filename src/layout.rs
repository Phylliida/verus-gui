use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};

pub mod proofs;
pub mod stack;
pub mod stack_proofs;
pub mod flex;
pub mod flex_proofs;
pub mod grid;
pub mod grid_proofs;
pub mod wrap;
pub mod wrap_proofs;
pub mod absolute;
pub mod absolute_proofs;
pub mod incremental_proofs;
pub mod cache_proofs;
pub mod bounds_proofs;
pub mod listview;
pub mod listview_proofs;

verus! {

// ── Axis enum ───────────────────────────────────────────────────────

/// Layout axis: Vertical for column-like layouts, Horizontal for row-like layouts.
#[derive(PartialEq, Eq)]
pub enum Axis {
    Horizontal,
    Vertical,
}

// ── Helper spec functions ───────────────────────────────────────────

/// Sum of child heights for children at indices 0..count.
pub open spec fn sum_heights<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        sum_heights(sizes, (count - 1) as nat)
            .add(sizes[(count - 1) as int].height)
    }
}

/// Sum of child widths for children at indices 0..count.
pub open spec fn sum_widths<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        sum_widths(sizes, (count - 1) as nat)
            .add(sizes[(count - 1) as int].width)
    }
}

/// Repeated addition: val added n times (n * val without requiring multiplication by nat).
pub open spec fn repeated_add<T: OrderedRing>(val: T, n: nat) -> T
    decreases n,
{
    if n == 0 {
        T::zero()
    } else {
        repeated_add(val, (n - 1) as nat).add(val)
    }
}

// ── Column layout ───────────────────────────────────────────────────

/// Compute the y-position of child at `index` in a column layout.
///
/// child_y(0) = padding.top
/// child_y(i) = child_y(i-1) + child_sizes[i-1].height + spacing
pub open spec fn child_y_position<T: OrderedRing>(
    padding_top: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    index: nat,
) -> T
    decreases index,
{
    if index == 0 {
        padding_top
    } else {
        child_y_position(padding_top, child_sizes, spacing, (index - 1) as nat)
            .add(child_sizes[(index - 1) as int].height)
            .add(spacing)
    }
}

/// Build the sequence of child Nodes for a column layout.
pub open spec fn column_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    index: nat,
) -> Seq<Node<T>>
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
        Seq::empty()
    } else {
        let child_x = padding.left.add(
            align_offset(alignment, available_width, child_sizes[index as int].width)
        );
        let child_y = child_y_position(padding.top, child_sizes, spacing, index);
        let child_node = Node::leaf(child_x, child_y, child_sizes[index as int]);
        Seq::empty().push(child_node).add(
            column_children(padding, spacing, alignment, child_sizes, available_width, index + 1)
        )
    }
}

/// Total height consumed by children in a column layout:
/// sum of child heights + (n-1) * spacing  (for n > 0).
pub open spec fn column_content_height<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
) -> T {
    if child_sizes.len() == 0 {
        T::zero()
    } else {
        sum_heights(child_sizes, child_sizes.len() as nat)
            .add(repeated_add(spacing, (child_sizes.len() - 1) as nat))
    }
}

/// Lay out children in a vertical column.
///
/// Algorithm:
/// 1. Subtract padding from available space
/// 2. Place each child vertically, separated by spacing
/// 3. Align children on cross-axis (horizontal) per Alignment
/// 4. Return parent Node with positioned children
#[verifier::opaque]
pub open spec fn column_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
) -> Node<T> {
    let available_width = limits.max.width.sub(padding.horizontal());
    let content_height = column_content_height(child_sizes, spacing);
    let total_height = padding.vertical().add(content_height);
    let parent_size = limits.resolve(Size::new(limits.max.width, total_height));
    let children = column_children(
        padding, spacing, alignment, child_sizes, available_width, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

// ── Unified linear layout ────────────────────────────────────────────

/// Sum of main-axis dimensions for children at indices 0..count.
pub open spec fn sum_main<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    axis: Axis,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        sum_main(sizes, axis, (count - 1) as nat)
            .add(sizes[(count - 1) as int].main_dim(axis))
    }
}

/// Compute the main-axis position of child at `index` in a linear layout.
pub open spec fn child_main_position<T: OrderedRing>(
    padding_start: T,
    child_sizes: Seq<Size<T>>,
    axis: Axis,
    spacing: T,
    index: nat,
) -> T
    decreases index,
{
    if index == 0 {
        padding_start
    } else {
        child_main_position(padding_start, child_sizes, axis, spacing, (index - 1) as nat)
            .add(child_sizes[(index - 1) as int].main_dim(axis))
            .add(spacing)
    }
}

/// Build the sequence of child Nodes for a linear layout.
pub open spec fn linear_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    axis: Axis,
    available_cross: T,
    index: nat,
) -> Seq<Node<T>>
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
        Seq::empty()
    } else {
        let cross_offset = padding.cross_start(axis).add(
            align_offset(alignment, available_cross, child_sizes[index as int].cross_dim(axis))
        );
        let main_offset = child_main_position(
            padding.main_start(axis), child_sizes, axis, spacing, index,
        );
        let (x, y) = match axis {
            Axis::Vertical => (cross_offset, main_offset),
            Axis::Horizontal => (main_offset, cross_offset),
        };
        let child_node = Node::leaf(x, y, child_sizes[index as int]);
        Seq::empty().push(child_node).add(
            linear_children(padding, spacing, alignment, child_sizes, axis, available_cross, index + 1)
        )
    }
}

/// Total main-axis content size: sum of main dimensions + (n-1) * spacing.
pub open spec fn linear_content_main<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    axis: Axis,
    spacing: T,
) -> T {
    if child_sizes.len() == 0 {
        T::zero()
    } else {
        sum_main(child_sizes, axis, child_sizes.len() as nat)
            .add(repeated_add(spacing, (child_sizes.len() - 1) as nat))
    }
}

/// Lay out children along a single axis (unified column/row).
#[verifier::opaque]
pub open spec fn linear_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    axis: Axis,
) -> Node<T> {
    let available_cross = limits.max.cross_dim(axis).sub(padding.cross_padding(axis));
    let content_main = linear_content_main(child_sizes, axis, spacing);
    let total_main = padding.main_padding(axis).add(content_main);
    let parent_size = limits.resolve(Size::from_axes(axis, total_main, limits.max.cross_dim(axis)));
    let children = linear_children(
        padding, spacing, alignment, child_sizes, axis, available_cross, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

/// Bridge: column_layout == linear_layout with Axis::Vertical.
pub proof fn lemma_column_layout_is_linear<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
)
    ensures
        column_layout(limits, padding, spacing, alignment, child_sizes)
            == linear_layout(limits, padding, spacing, alignment, child_sizes, Axis::Vertical),
{
    reveal(column_layout);
    reveal(linear_layout);
    // Both sides reduce to the same expression when axis = Vertical:
    // sum_main with Vertical reads .height == sum_heights
    // child_main_position with Vertical uses padding.top == child_y_position
    // linear_children with Vertical puts (cross, main) = (x, y) matching column_children
    // Content: linear_content_main with Vertical == column_content_height
    // Parent size: from_axes(Vertical, main, cross) = Size { width: cross, height: main }
    //   = Size::new(limits.max.width, total_height) matching column_layout

    // First prove sum_main == sum_heights for all counts
    assert forall|count: nat| count <= child_sizes.len() implies
        sum_main::<T>(child_sizes, Axis::Vertical, count)
        == sum_heights::<T>(child_sizes, count)
    by {
        lemma_sum_main_eq_sum_heights(child_sizes, count);
    }

    // Prove child_main_position == child_y_position for all indices
    assert forall|index: nat| index <= child_sizes.len() implies
        child_main_position::<T>(padding.top, child_sizes, Axis::Vertical, spacing, index)
        == child_y_position::<T>(padding.top, child_sizes, spacing, index)
    by {
        lemma_child_main_position_eq_child_y_position(padding, child_sizes, spacing, index);
    }

    // Prove linear_children == column_children
    assert forall|index: nat| index <= child_sizes.len() implies
        linear_children::<T>(padding, spacing, alignment, child_sizes, Axis::Vertical,
            limits.max.width.sub(padding.horizontal()), index)
        == column_children::<T>(padding, spacing, alignment, child_sizes,
            limits.max.width.sub(padding.horizontal()), index)
    by {
        lemma_linear_children_eq_column_children(
            padding, spacing, alignment, child_sizes,
            limits.max.width.sub(padding.horizontal()), index,
        );
    }
}

/// Helper: sum_main(Vertical) == sum_heights
proof fn lemma_sum_main_eq_sum_heights<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
)
    requires count <= sizes.len(),
    ensures sum_main::<T>(sizes, Axis::Vertical, count) == sum_heights::<T>(sizes, count),
    decreases count,
{
    if count > 0 {
        lemma_sum_main_eq_sum_heights::<T>(sizes, (count - 1) as nat);
    }
}

/// Helper: child_main_position(Vertical) == child_y_position
proof fn lemma_child_main_position_eq_child_y_position<T: OrderedRing>(
    padding: Padding<T>,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    index: nat,
)
    requires index <= child_sizes.len(),
    ensures
        child_main_position::<T>(padding.top, child_sizes, Axis::Vertical, spacing, index)
        == child_y_position::<T>(padding.top, child_sizes, spacing, index),
    decreases index,
{
    if index > 0 {
        lemma_child_main_position_eq_child_y_position::<T>(padding, child_sizes, spacing, (index - 1) as nat);
    }
}

/// Helper: linear_children(Vertical) == column_children
proof fn lemma_linear_children_eq_column_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    index: nat,
)
    requires index <= child_sizes.len(),
    ensures
        linear_children::<T>(padding, spacing, alignment, child_sizes, Axis::Vertical,
            available_width, index)
        == column_children::<T>(padding, spacing, alignment, child_sizes,
            available_width, index),
    decreases child_sizes.len() - index,
{
    if index < child_sizes.len() {
        lemma_child_main_position_eq_child_y_position::<T>(padding, child_sizes, spacing, index);
        lemma_linear_children_eq_column_children::<T>(
            padding, spacing, alignment, child_sizes, available_width, index + 1,
        );
    }
}

/// Bridge: row_layout == linear_layout with Axis::Horizontal.
pub proof fn lemma_row_layout_is_linear<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
)
    ensures
        row_layout(limits, padding, spacing, alignment, child_sizes)
            == linear_layout(limits, padding, spacing, alignment, child_sizes, Axis::Horizontal),
{
    reveal(column_layout);
    reveal(row_layout);
    reveal(linear_layout);

    // Prove sum_main(Horizontal) == sum_widths
    assert forall|count: nat| count <= child_sizes.len() implies
        sum_main::<T>(child_sizes, Axis::Horizontal, count)
        == sum_widths::<T>(child_sizes, count)
    by {
        lemma_sum_main_eq_sum_widths(child_sizes, count);
    }

    // Prove child_main_position == child_x_position
    assert forall|index: nat| index <= child_sizes.len() implies
        child_main_position::<T>(padding.left, child_sizes, Axis::Horizontal, spacing, index)
        == child_x_position::<T>(padding.left, child_sizes, spacing, index)
    by {
        lemma_child_main_position_eq_child_x_position(padding, child_sizes, spacing, index);
    }

    // Prove linear_children == row_children
    assert forall|index: nat| index <= child_sizes.len() implies
        linear_children::<T>(padding, spacing, alignment, child_sizes, Axis::Horizontal,
            limits.max.height.sub(padding.vertical()), index)
        == row_children::<T>(padding, spacing, alignment, child_sizes,
            limits.max.height.sub(padding.vertical()), index)
    by {
        lemma_linear_children_eq_row_children(
            padding, spacing, alignment, child_sizes,
            limits.max.height.sub(padding.vertical()), index,
        );
    }
}

/// Helper: sum_main(Horizontal) == sum_widths
proof fn lemma_sum_main_eq_sum_widths<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
)
    requires count <= sizes.len(),
    ensures sum_main::<T>(sizes, Axis::Horizontal, count) == sum_widths::<T>(sizes, count),
    decreases count,
{
    if count > 0 {
        lemma_sum_main_eq_sum_widths::<T>(sizes, (count - 1) as nat);
    }
}

/// Helper: child_main_position(Horizontal) == child_x_position
proof fn lemma_child_main_position_eq_child_x_position<T: OrderedRing>(
    padding: Padding<T>,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    index: nat,
)
    requires index <= child_sizes.len(),
    ensures
        child_main_position::<T>(padding.left, child_sizes, Axis::Horizontal, spacing, index)
        == child_x_position::<T>(padding.left, child_sizes, spacing, index),
    decreases index,
{
    if index > 0 {
        lemma_child_main_position_eq_child_x_position::<T>(padding, child_sizes, spacing, (index - 1) as nat);
    }
}

/// Helper: linear_children(Horizontal) == row_children
proof fn lemma_linear_children_eq_row_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_height: T,
    index: nat,
)
    requires index <= child_sizes.len(),
    ensures
        linear_children::<T>(padding, spacing, alignment, child_sizes, Axis::Horizontal,
            available_height, index)
        == row_children::<T>(padding, spacing, alignment, child_sizes,
            available_height, index),
    decreases child_sizes.len() - index,
{
    if index < child_sizes.len() {
        lemma_child_main_position_eq_child_x_position::<T>(padding, child_sizes, spacing, index);
        lemma_linear_children_eq_row_children::<T>(
            padding, spacing, alignment, child_sizes, available_height, index + 1,
        );
    }
}

// ── Row layout ──────────────────────────────────────────────────────

/// Compute the x-position of child at `index` in a row layout.
///
/// child_x(0) = padding.left
/// child_x(i) = child_x(i-1) + child_sizes[i-1].width + spacing
pub open spec fn child_x_position<T: OrderedRing>(
    padding_left: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    index: nat,
) -> T
    decreases index,
{
    if index == 0 {
        padding_left
    } else {
        child_x_position(padding_left, child_sizes, spacing, (index - 1) as nat)
            .add(child_sizes[(index - 1) as int].width)
            .add(spacing)
    }
}

/// Build the sequence of child Nodes for a row layout.
pub open spec fn row_children<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_height: T,
    index: nat,
) -> Seq<Node<T>>
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
        Seq::empty()
    } else {
        let child_x = child_x_position(padding.left, child_sizes, spacing, index);
        let child_y = padding.top.add(
            align_offset(alignment, available_height, child_sizes[index as int].height)
        );
        let child_node = Node::leaf(child_x, child_y, child_sizes[index as int]);
        Seq::empty().push(child_node).add(
            row_children(padding, spacing, alignment, child_sizes, available_height, index + 1)
        )
    }
}

/// Total width consumed by children in a row layout:
/// sum of child widths + (n-1) * spacing  (for n > 0).
pub open spec fn row_content_width<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
) -> T {
    if child_sizes.len() == 0 {
        T::zero()
    } else {
        sum_widths(child_sizes, child_sizes.len() as nat)
            .add(repeated_add(spacing, (child_sizes.len() - 1) as nat))
    }
}

/// Lay out children in a horizontal row.
///
/// Algorithm:
/// 1. Subtract padding from available space
/// 2. Place each child horizontally, separated by spacing
/// 3. Align children on cross-axis (vertical) per Alignment
/// 4. Return parent Node with positioned children
#[verifier::opaque]
pub open spec fn row_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
) -> Node<T> {
    let available_height = limits.max.height.sub(padding.vertical());
    let content_width = row_content_width(child_sizes, spacing);
    let total_width = padding.horizontal().add(content_width);
    let parent_size = limits.resolve(Size::new(total_width, limits.max.height));
    let children = row_children(
        padding, spacing, alignment, child_sizes, available_height, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

} // verus!
