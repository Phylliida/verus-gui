use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::max;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;

verus! {

// ── Helper spec functions ───────────────────────────────────────────

/// Maximum of (x + width) across the first `count` children.
pub open spec fn absolute_max_right<T: OrderedRing>(
    child_data: Seq<(T, T, Size<T>)>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        let (x, _y, sz) = child_data[(count - 1) as int];
        max::<T>(
            absolute_max_right(child_data, (count - 1) as nat),
            x.add(sz.width),
        )
    }
}

/// Maximum of (y + height) across the first `count` children.
pub open spec fn absolute_max_bottom<T: OrderedRing>(
    child_data: Seq<(T, T, Size<T>)>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        let (_x, y, sz) = child_data[(count - 1) as int];
        max::<T>(
            absolute_max_bottom(child_data, (count - 1) as nat),
            y.add(sz.height),
        )
    }
}

/// The content size of an absolute layout: bounding box of all positioned children.
pub open spec fn absolute_content_size<T: OrderedRing>(
    child_data: Seq<(T, T, Size<T>)>,
) -> Size<T> {
    Size::new(
        absolute_max_right(child_data, child_data.len() as nat),
        absolute_max_bottom(child_data, child_data.len() as nat),
    )
}

// ── Absolute layout ─────────────────────────────────────────────────

/// Build the sequence of child Nodes for an absolute layout.
/// Each child is placed at (padding.left + x, padding.top + y).
pub open spec fn absolute_children<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    index: nat,
) -> Seq<Node<T>>
    decreases child_data.len() - index,
{
    if index >= child_data.len() {
        Seq::empty()
    } else {
        let (x, y, sz) = child_data[index as int];
        let child_x = padding.left.add(x);
        let child_y = padding.top.add(y);
        let child_node = Node::leaf(child_x, child_y, sz);
        Seq::empty().push(child_node).add(
            absolute_children(padding, child_data, index + 1)
        )
    }
}

/// Lay out children at absolute positions within padding.
///
/// Algorithm:
/// 1. Subtract padding from available space
/// 2. Content size is the bounding box of all (x + width, y + height)
/// 3. Each child is placed at (padding.left + x, padding.top + y)
/// 4. Return parent Node with positioned children
#[verifier::opaque]
pub open spec fn absolute_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
) -> Node<T> {
    let content = absolute_content_size(child_data);
    let total_width = padding.horizontal().add(content.width);
    let total_height = padding.vertical().add(content.height);
    let parent_size = limits.resolve(Size::new(total_width, total_height));
    let children = absolute_children(padding, child_data, 0);
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

} // verus!
