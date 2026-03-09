use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::layout::listview::*;
use crate::layout::proofs::lemma_resolve_bounds;

verus! {

/// ListView output respects limits: output size is within [min, max].
pub proof fn lemma_listview_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport: Size<T>,
    child_nodes: Seq<Node<T>>,
    first: nat,
)
    requires limits.wf(),
    ensures
        limits.min.le(layout_listview_body(limits, child_sizes, spacing, scroll_y, viewport, child_nodes, first).size),
        layout_listview_body(limits, child_sizes, spacing, scroll_y, viewport, child_nodes, first).size.le(limits.max),
{
    // layout_listview_body returns limits.resolve(viewport)
    lemma_resolve_bounds(limits, viewport);
}

/// First visible scan is bounded: result <= total.
pub proof fn lemma_first_visible_bounded<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
)
    ensures
        listview_first_visible(child_sizes, spacing, scroll_y) <= child_sizes.len(),
    decreases child_sizes.len(),
{
    lemma_first_visible_from_bounded(child_sizes, spacing, scroll_y, 0);
}

proof fn lemma_first_visible_from_bounded<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    from: nat,
)
    ensures
        listview_first_visible_from(child_sizes, spacing, scroll_y, from) <= child_sizes.len(),
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        // returns child_sizes.len()
    } else if scroll_y.lt(listview_child_bottom(child_sizes, spacing, from)) {
        // returns from <= child_sizes.len()
    } else {
        lemma_first_visible_from_bounded(child_sizes, spacing, scroll_y, from + 1);
    }
}

/// End visible scan is bounded: result <= total.
pub proof fn lemma_end_visible_bounded<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
)
    ensures
        listview_end_visible(child_sizes, spacing, scroll_y, viewport_h) <= child_sizes.len(),
    decreases child_sizes.len(),
{
    lemma_end_visible_from_bounded(child_sizes, spacing, scroll_y, viewport_h, 0);
}

proof fn lemma_end_visible_from_bounded<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
    from: nat,
)
    ensures
        listview_end_visible_from(child_sizes, spacing, scroll_y, viewport_h, from) <= child_sizes.len(),
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        // returns child_sizes.len()
    } else {
        let scroll_bottom = scroll_y.add(viewport_h);
        if scroll_bottom.le(listview_child_y(child_sizes, spacing, from)) {
            // returns from <= child_sizes.len()
        } else {
            lemma_end_visible_from_bounded(child_sizes, spacing, scroll_y, viewport_h, from + 1);
        }
    }
}

} // verus!
