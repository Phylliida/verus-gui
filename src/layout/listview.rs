use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::layout::repeated_add;
use crate::widget::Widget;

verus! {

// ── Cumulative position helpers ──────────────────────────────────────

/// Y-position of the i-th item in a variable-height ListView.
///
/// listview_child_y(sizes, sp, 0) = 0
/// listview_child_y(sizes, sp, i+1) = child_y(i) + sizes[i].height + spacing
pub open spec fn listview_child_y<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
) -> T
    decreases i,
{
    if i == 0 {
        T::zero()
    } else {
        listview_child_y(child_sizes, spacing, (i - 1) as nat)
            .add(child_sizes[(i - 1) as int].height)
            .add(spacing)
    }
}

/// Bottom edge of the i-th item: y + sizes[i].height.
pub open spec fn listview_child_bottom<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
) -> T {
    listview_child_y(child_sizes, spacing, i).add(child_sizes[i as int].height)
}

// ── Visible range computation ────────────────────────────────────────

/// First visible index: smallest i in [0, total) where bottom > scroll_y.
/// Returns child_sizes.len() if no child is visible.
pub open spec fn listview_first_visible<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
) -> nat {
    listview_first_visible_from(child_sizes, spacing, scroll_y, 0)
}

/// Linear scan for first visible starting from `from`.
pub open spec fn listview_first_visible_from<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    from: nat,
) -> nat
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        child_sizes.len()
    } else if scroll_y.lt(listview_child_bottom(child_sizes, spacing, from)) {
        from
    } else {
        listview_first_visible_from(child_sizes, spacing, scroll_y, from + 1)
    }
}

/// End-of-visible index: smallest i in [0, total] where top >= scroll_bottom.
/// Returns child_sizes.len() if all remaining children are visible.
pub open spec fn listview_end_visible<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
) -> nat {
    listview_end_visible_from(child_sizes, spacing, scroll_y, viewport_h, 0)
}

/// Linear scan for end-of-visible starting from `from`.
pub open spec fn listview_end_visible_from<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
    from: nat,
) -> nat
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        child_sizes.len()
    } else {
        let scroll_bottom = scroll_y.add(viewport_h);
        if scroll_bottom.le(listview_child_y(child_sizes, spacing, from)) {
            from
        } else {
            listview_end_visible_from(child_sizes, spacing, scroll_y, viewport_h, from + 1)
        }
    }
}

// ── Layout assembly ──────────────────────────────────────────────────

/// Number of visible children.
pub open spec fn listview_visible_count<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
) -> nat {
    let first = listview_first_visible(child_sizes, spacing, scroll_y);
    let end = listview_end_visible(child_sizes, spacing, scroll_y, viewport_h);
    if end >= first { (end - first) as nat } else { 0 }
}

/// Assemble a ListView Node from pre-computed visible child nodes.
///
/// Each child is positioned at (0, child_y(first + i) - scroll_y).
/// Output size = limits.resolve(viewport).
#[verifier::opaque]
pub open spec fn layout_listview_body<T: OrderedField>(
    limits: Limits<T>,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport: Size<T>,
    child_nodes: Seq<Node<T>>,
    first: nat,
) -> Node<T> {
    let parent_size = limits.resolve(viewport);
    Node {
        x: T::zero(),
        y: T::zero(),
        size: parent_size,
        children: Seq::new(child_nodes.len(), |i: int| Node {
            x: T::zero(),
            y: listview_child_y(child_sizes, spacing, (first + i) as nat).sub(scroll_y),
            size: child_nodes[i].size,
            children: child_nodes[i].children,
        }),
    }
}

// ── Widget child node helpers for visible range ──────────────────────

/// Lay out visible children from children[first..end].
pub open spec fn listview_widget_child_nodes<T: OrderedField>(
    child_limits: Limits<T>,
    children: Seq<Widget<T>>,
    first: nat,
    end: nat,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel,
{
    let count = if end >= first { (end - first) as nat } else { 0 };
    Seq::new(count, |i: int|
        crate::widget::layout_widget(child_limits, children[(first + i) as int], fuel)
    )
}

} // verus!
