use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::min_max::max;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;

verus! {

// ── Wrap cursor state ──────────────────────────────────────────────

/// Cursor state tracking position during wrap layout.
///
/// Tracks the current insertion point, line height, and maximum line width
/// as children are placed left-to-right with line wrapping.
pub ghost struct WrapCursor<T> {
    /// X position for the next child (includes trailing h_spacing after previous child).
    pub x: T,
    /// Y position of the current line top.
    pub y: T,
    /// Maximum child height on the current line.
    pub line_height: T,
    /// Maximum line width seen (across all lines including current).
    pub content_width: T,
}

// ── Line-break predicate ───────────────────────────────────────────

/// Whether a child triggers a line break.
///
/// Returns true when the current line already has content (cursor_x > 0)
/// and adding the child would exceed the available width.
pub open spec fn wrap_needs_break<T: OrderedRing>(
    cursor_x: T,
    child_width: T,
    available_width: T,
) -> bool {
    // cursor_x > 0 (line has content) AND cursor_x + child_width > available_width
    !cursor_x.le(T::zero()) && !cursor_x.add(child_width).le(available_width)
}

// ── Cursor recursion ───────────────────────────────────────────────

/// Compute cursor state after placing children [0..count).
///
/// `wrap_cursor(sizes, h_sp, v_sp, avail_w, 0)` is the initial state (all zeros).
/// `wrap_cursor(sizes, h_sp, v_sp, avail_w, n)` is the state after placing n children.
pub open spec fn wrap_cursor<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    count: nat,
) -> WrapCursor<T>
    decreases count,
{
    if count == 0 {
        WrapCursor {
            x: T::zero(),
            y: T::zero(),
            line_height: T::zero(),
            content_width: T::zero(),
        }
    } else {
        let prev = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat);
        let child = child_sizes[(count - 1) as int];
        if wrap_needs_break(prev.x, child.width, available_width) {
            // New line
            WrapCursor {
                x: child.width.add(h_spacing),
                y: prev.y.add(prev.line_height).add(v_spacing),
                line_height: child.height,
                content_width: max(prev.content_width, child.width),
            }
        } else {
            // Same line
            WrapCursor {
                x: prev.x.add(child.width).add(h_spacing),
                y: prev.y,
                line_height: max(prev.line_height, child.height),
                content_width: max(prev.content_width, prev.x.add(child.width)),
            }
        }
    }
}

// ── Child positioning ──────────────────────────────────────────────

/// Build the sequence of child Nodes for a wrap layout.
///
/// Children are placed left-to-right, wrapping to the next line when
/// a child would exceed the available width.
pub open spec fn wrap_children<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    index: nat,
) -> Seq<Node<T>>
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
        Seq::empty()
    } else {
        let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, index);
        let child = child_sizes[index as int];
        let needs_break = wrap_needs_break(cursor.x, child.width, available_width);
        let cx = if needs_break { T::zero() } else { cursor.x };
        let cy = if needs_break {
            cursor.y.add(cursor.line_height).add(v_spacing)
        } else {
            cursor.y
        };
        let child_node = Node::leaf(
            padding.left.add(cx),
            padding.top.add(cy),
            child,
        );
        Seq::empty().push(child_node).add(
            wrap_children(padding, h_spacing, v_spacing, child_sizes, available_width, index + 1)
        )
    }
}

// ── Content size ───────────────────────────────────────────────────

/// Content size of a wrap layout: max line width x total height.
pub open spec fn wrap_content_size<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
) -> Size<T> {
    if child_sizes.len() == 0 {
        Size::new(T::zero(), T::zero())
    } else {
        let cursor = wrap_cursor(
            child_sizes, h_spacing, v_spacing, available_width,
            child_sizes.len() as nat,
        );
        Size::new(cursor.content_width, cursor.y.add(cursor.line_height))
    }
}

// ── Main layout function ───────────────────────────────────────────

/// Lay out children in a wrapping flow (left-to-right, top-to-bottom).
///
/// Algorithm:
/// 1. Subtract padding to get available width
/// 2. Place children left-to-right, wrapping when exceeding available width
/// 3. Content size is max-line-width x total-height
/// 4. Return parent Node with positioned children
#[verifier::opaque]
pub open spec fn wrap_layout<T: OrderedRing>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
) -> Node<T> {
    let available_width = limits.max.width.sub(padding.horizontal());
    let content = wrap_content_size(child_sizes, h_spacing, v_spacing, available_width);
    let total_width = padding.horizontal().add(content.width);
    let total_height = padding.vertical().add(content.height);
    let parent_size = limits.resolve(Size::new(total_width, total_height));
    let children = wrap_children(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

// ── Uniform height predicate ──────────────────────────────────────

/// Whether all children have the same height (up to equivalence).
///
/// Empty sequences are vacuously uniform.
pub open spec fn wrap_uniform_height<T: OrderedRing>(child_sizes: Seq<Size<T>>) -> bool {
    child_sizes.len() > 0 ==> forall|i: int, j: int|
        0 <= i < child_sizes.len() && 0 <= j < child_sizes.len() ==>
            child_sizes[i].height.eqv(child_sizes[j].height)
}

// ── Line break counting ──────────────────────────────────────────

/// Count the number of line breaks in [0..count).
///
/// A line break occurs when `wrap_needs_break` is true for the cursor
/// at that position.
pub open spec fn wrap_break_count<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    count: nat,
) -> nat
    decreases count,
{
    if count == 0 {
        0
    } else {
        let prev_breaks = wrap_break_count(child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat);
        let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat);
        let child = child_sizes[(count - 1) as int];
        if wrap_needs_break(cursor.x, child.width, available_width) {
            prev_breaks + 1
        } else {
            prev_breaks
        }
    }
}

} // verus!
