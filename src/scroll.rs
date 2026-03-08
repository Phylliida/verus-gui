use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::partial_order::PartialOrder;
use verus_algebra::lemmas::ordered_ring_lemmas;
use crate::size::Size;
use crate::layout::child_y_position;
use crate::layout::proofs::lemma_le_add_nonneg;

verus! {

// ── Visibility predicates ──────────────────────────────────────────

/// Whether child at `index` is visible in the scroll viewport.
/// Visible iff the child's vertical interval overlaps [scroll_y, scroll_y + viewport_h).
/// That is: bottom > scroll_y AND top < scroll_bottom.
pub open spec fn child_visible<T: OrderedRing>(
    padding_top: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    index: nat,
    scroll_y: T,
    viewport_h: T,
) -> bool {
    let y_pos = child_y_position(padding_top, child_sizes, spacing, index);
    let bottom = y_pos.add(child_sizes[index as int].height);
    let scroll_bottom = scroll_y.add(viewport_h);
    // visible iff bottom > scroll_y AND top < scroll_bottom
    scroll_y.lt(bottom) && y_pos.lt(scroll_bottom)
}

/// A range [first, end) is a valid visible range for the given scroll state.
pub open spec fn visible_range_valid<T: OrderedRing>(
    padding_top: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
    first: nat,
    end: nat,
) -> bool {
    &&& first <= end
    &&& end <= child_sizes.len()
    // All children in [first, end) are visible
    &&& forall|i: nat| first <= i && i < end ==>
        child_visible(padding_top, child_sizes, spacing, i, scroll_y, viewport_h)
    // All children outside [first, end) are not visible
    &&& forall|i: nat| i < child_sizes.len() && (i < first || i >= end) ==>
        !child_visible(padding_top, child_sizes, spacing, i, scroll_y, viewport_h)
}

// ── Monotonicity ───────────────────────────────────────────────────

/// child_y_position is monotone when spacing >= 0 and heights >= 0.
pub proof fn lemma_child_y_monotone<T: OrderedRing>(
    pt: T,
    sizes: Seq<Size<T>>,
    sp: T,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        T::zero().le(sp),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        child_y_position(pt, sizes, sp, i).le(child_y_position(pt, sizes, sp, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(child_y_position(pt, sizes, sp, i));
    } else {
        // IH: child_y(i) <= child_y(j-1)
        lemma_child_y_monotone(pt, sizes, sp, i, (j - 1) as nat);

        let y_prev = child_y_position(pt, sizes, sp, (j - 1) as nat);
        let h = sizes[(j - 1) as int].height;

        // child_y(j) = y_prev + h + sp (by definition of child_y_position)
        // Need: y_prev <= y_prev + h + sp

        // Step 1: y_prev <= y_prev + h  (h >= 0)
        lemma_le_add_nonneg(y_prev, h);

        // Step 2: y_prev + h <= (y_prev + h) + sp  (sp >= 0)
        lemma_le_add_nonneg(y_prev.add(h), sp);

        // Chain: child_y(i) <= y_prev <= y_prev + h <= (y_prev + h) + sp = child_y(j)
        T::axiom_le_transitive(
            child_y_position(pt, sizes, sp, i), y_prev, y_prev.add(h),
        );
        T::axiom_le_transitive(
            child_y_position(pt, sizes, sp, i), y_prev.add(h), y_prev.add(h).add(sp),
        );
    }
}

// ── Contiguity ─────────────────────────────────────────────────────

/// Visible children form a contiguous range (no gaps).
/// If children i and j are both visible, then any k between them is also visible.
pub proof fn lemma_visible_range_contiguous<T: OrderedRing>(
    pt: T,
    sizes: Seq<Size<T>>,
    sp: T,
    scroll_y: T,
    vh: T,
    i: nat,
    k: nat,
    j: nat,
)
    requires
        i < k,
        k < j,
        j < sizes.len(),
        child_visible(pt, sizes, sp, i, scroll_y, vh),
        child_visible(pt, sizes, sp, j, scroll_y, vh),
        T::zero().le(sp),
        forall|m: int| 0 <= m < sizes.len() ==> T::zero().le(sizes[m].height),
    ensures
        child_visible(pt, sizes, sp, k, scroll_y, vh),
{
    let y_i = child_y_position(pt, sizes, sp, i);
    let y_k = child_y_position(pt, sizes, sp, k);
    let y_j = child_y_position(pt, sizes, sp, j);
    let scroll_bottom = scroll_y.add(vh);

    // ── Part 1: y_k < scroll_bottom ──
    // From visibility of j: y_j < scroll_bottom
    // From monotonicity: y_k <= y_j (since k < j, so k <= j)
    lemma_child_y_monotone(pt, sizes, sp, k, j);
    // Chain: y_k <= y_j < scroll_bottom
    ordered_ring_lemmas::lemma_le_lt_transitive(y_k, y_j, scroll_bottom);

    // ── Part 2: scroll_y < y_k + sizes[k].height ──
    // Strategy: scroll_y < bottom_i <= y_{i+1} <= y_k <= y_k + sizes[k].height

    // From visibility of i: scroll_y < y_i + sizes[i].height
    let bottom_i = y_i.add(sizes[i as int].height);

    // bottom_i <= bottom_i + sp = y_{i+1} (sp >= 0)
    lemma_le_add_nonneg(bottom_i, sp);
    let y_i1 = child_y_position(pt, sizes, sp, (i + 1) as nat);
    // scroll_y < bottom_i <= y_{i+1}
    ordered_ring_lemmas::lemma_lt_le_transitive(scroll_y, bottom_i, y_i1);

    // y_{i+1} <= y_k (since i+1 <= k, by monotonicity)
    lemma_child_y_monotone(pt, sizes, sp, (i + 1) as nat, k);
    // scroll_y < y_{i+1} <= y_k
    ordered_ring_lemmas::lemma_lt_le_transitive(scroll_y, y_i1, y_k);

    // y_k <= y_k + sizes[k].height (sizes[k].height >= 0)
    let bottom_k = y_k.add(sizes[k as int].height);
    lemma_le_add_nonneg(y_k, sizes[k as int].height);
    // scroll_y < y_k <= bottom_k
    ordered_ring_lemmas::lemma_lt_le_transitive(scroll_y, y_k, bottom_k);
}

} // verus!
