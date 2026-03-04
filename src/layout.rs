use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};

pub mod proofs;

verus! {

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
pub open spec fn column_children<T: OrderedRing>(
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
pub open spec fn column_layout<T: OrderedRing>(
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
pub open spec fn row_children<T: OrderedRing>(
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
pub open spec fn row_layout<T: OrderedRing>(
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
