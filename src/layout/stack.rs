use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::max;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};

verus! {

// ── Helper spec functions ───────────────────────────────────────────

/// Maximum width among the first `count` children.
#[verifier::opaque]
pub open spec fn max_width<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        max::<T>(max_width(sizes, (count - 1) as nat), sizes[(count - 1) as int].width)
    }
}

/// Maximum height among the first `count` children.
#[verifier::opaque]
pub open spec fn max_height<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        max::<T>(max_height(sizes, (count - 1) as nat), sizes[(count - 1) as int].height)
    }
}

/// The content size of a stack: max width x max height.
#[verifier::opaque]
pub open spec fn stack_content_size<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
) -> Size<T> {
    Size::new(
        max_width(child_sizes, child_sizes.len() as nat),
        max_height(child_sizes, child_sizes.len() as nat),
    )
}

// ── Stack layout ────────────────────────────────────────────────────

/// Build the sequence of child Nodes for a stack layout.
/// Each child is independently positioned via alignment on both axes.
#[verifier::opaque]
pub open spec fn stack_children<T: OrderedField>(
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    available_height: T,
    index: nat,
) -> Seq<Node<T>>
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
        Seq::empty()
    } else {
        let child_x = padding.left.add(
            align_offset(h_align, available_width, child_sizes[index as int].width)
        );
        let child_y = padding.top.add(
            align_offset(v_align, available_height, child_sizes[index as int].height)
        );
        let child_node = Node::leaf(child_x, child_y, child_sizes[index as int]);
        Seq::empty().push(child_node).add(
            stack_children(padding, h_align, v_align, child_sizes,
                available_width, available_height, index + 1)
        )
    }
}

/// Lay out children in a stack (all overlapping at the same position).
///
/// Algorithm:
/// 1. Subtract padding from available space
/// 2. Content size is max_width x max_height of children
/// 3. Each child is independently aligned on both axes
/// 4. Return parent Node with positioned children
#[verifier::opaque]
pub open spec fn stack_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Size<T>>,
) -> Node<T> {
    let content = stack_content_size(child_sizes);
    let total_width = padding.horizontal().add(content.width);
    let total_height = padding.vertical().add(content.height);
    let parent_size = limits.resolve(Size::new(total_width, total_height));
    let available_width = limits.max.width.sub(padding.horizontal());
    let available_height = limits.max.height.sub(padding.vertical());
    let children = stack_children(
        padding, h_align, v_align, child_sizes,
        available_width, available_height, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

} // verus!
