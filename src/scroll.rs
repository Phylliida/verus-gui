use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::partial_order::PartialOrder;
use verus_algebra::lemmas::ordered_ring_lemmas;
use crate::size::Size;
use crate::layout::child_y_position;
use crate::layout::proofs::lemma_le_add_nonneg;
use crate::layout::proofs::lemma_add_swap_last;

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

// ── Scroll invariance ─────────────────────────────────────────────

/// child_y_position has the form: padding_top + content_offset.
/// Changing padding_top shifts all positions by the same amount.
/// This proves scroll invariance: scroll_y only affects padding_top,
/// so the spacing between children is unchanged.
pub proof fn lemma_child_y_offset_invariant<T: OrderedRing>(
    pt: T,
    delta: T,
    sizes: Seq<Size<T>>,
    sp: T,
    k: nat,
)
    requires k <= sizes.len(),
    ensures
        child_y_position(pt.add(delta), sizes, sp, k)
            .eqv(child_y_position(pt, sizes, sp, k).add(delta)),
    decreases k,
{
    if k == 0 {
        // child_y(pt + delta, 0) = pt + delta = child_y(pt, 0) + delta
        // Both sides are pt.add(delta), so trivially eqv by reflexivity.
        T::axiom_eqv_reflexive(pt.add(delta));
    } else {
        // IH: child_y(pt + delta, k-1) eqv child_y(pt, k-1) + delta
        lemma_child_y_offset_invariant(pt, delta, sizes, sp, (k - 1) as nat);

        let y_prev = child_y_position(pt, sizes, sp, (k - 1) as nat);
        let y_prev_shifted = child_y_position(pt.add(delta), sizes, sp, (k - 1) as nat);
        let h = sizes[(k - 1) as int].height;

        // By definition:
        //   LHS = child_y(pt+delta, k) = y_prev_shifted + h + sp
        //   RHS = child_y(pt, k) + delta = (y_prev + h + sp) + delta

        // Step 1: y_prev_shifted eqv y_prev + delta  (IH)
        // Step 2: y_prev_shifted + h eqv (y_prev + delta) + h  (congruence left)
        T::axiom_add_congruence_left(y_prev_shifted, y_prev.add(delta), h);
        // Step 3: y_prev_shifted + h + sp eqv (y_prev + delta) + h + sp  (congruence left)
        T::axiom_add_congruence_left(
            y_prev_shifted.add(h), y_prev.add(delta).add(h), sp,
        );
        // Now LHS eqv (y_prev + delta) + h + sp

        // Step 4: (y_prev + delta) + h eqv (y_prev + h) + delta  (swap last)
        lemma_add_swap_last(y_prev, delta, h);
        // Step 5: (y_prev + h) + delta + sp eqv (y_prev + h + sp) + delta  (swap last)
        // First extend step 4 with sp:
        T::axiom_add_congruence_left(
            y_prev.add(delta).add(h), y_prev.add(h).add(delta), sp,
        );
        // Now: (y_prev + delta) + h + sp eqv (y_prev + h) + delta + sp
        lemma_add_swap_last(y_prev.add(h), delta, sp);
        // (y_prev + h) + delta + sp eqv (y_prev + h + sp) + delta = RHS

        // Chain: LHS eqv (y+d)+h+sp eqv (y+h)+d+sp eqv (y+h+sp)+d = RHS
        T::axiom_eqv_transitive(
            y_prev_shifted.add(h).add(sp),
            y_prev.add(delta).add(h).add(sp),
            y_prev.add(h).add(delta).add(sp),
        );
        T::axiom_eqv_transitive(
            y_prev_shifted.add(h).add(sp),
            y_prev.add(h).add(delta).add(sp),
            y_prev.add(h).add(sp).add(delta),
        );
    }
}

/// Content height (distance from first to last child bottom) is
/// independent of scroll offset / padding_top.
pub proof fn lemma_content_height_independent_of_scroll<T: OrderedRing>(
    pt1: T,
    pt2: T,
    sizes: Seq<Size<T>>,
    sp: T,
    n: nat,
)
    requires n <= sizes.len(),
    ensures
        // child_y(pt1, n) - child_y(pt1, 0) eqv child_y(pt2, n) - child_y(pt2, 0)
        child_y_position(pt1, sizes, sp, n).sub(child_y_position(pt1, sizes, sp, 0))
            .eqv(child_y_position(pt2, sizes, sp, n).sub(child_y_position(pt2, sizes, sp, 0))),
{
    // child_y(pt, 0) = pt, so child_y(pt, n) - pt.
    // By lemma_child_y_offset_invariant with delta = pt2.sub(pt1):
    //   child_y(pt1 + (pt2 - pt1), n) eqv child_y(pt1, n) + (pt2 - pt1)
    // i.e. child_y(pt2, n) eqv child_y(pt1, n) + (pt2 - pt1)
    // So child_y(pt2, n) - pt2 eqv child_y(pt1, n) + (pt2 - pt1) - pt2
    //                             eqv child_y(pt1, n) - pt1
    // This requires several algebraic steps; we leave it to the SMT solver
    // with the key lemma instantiated.
    let delta = pt2.sub(pt1);
    lemma_child_y_offset_invariant(pt1, delta, sizes, sp, n);
    lemma_child_y_offset_invariant(pt1, delta, sizes, sp, 0);
    // child_y(pt1 + delta, n) eqv child_y(pt1, n) + delta
    // child_y(pt1 + delta, 0) eqv child_y(pt1, 0) + delta
    // i.e., pt1 + delta eqv pt1 + delta (trivial)
    // and child_y(pt1 + delta, n) eqv child_y(pt1, n) + delta

    // We need: child_y(pt1+delta, n).sub(pt1+delta) eqv child_y(pt1, n).sub(pt1)
    // But pt1 + delta might not == pt2, only eqv.
    // Actually: pt1.add(pt2.sub(pt1)) is definitionally what it is.
    // For the general case, we use sub = add(neg) and chain congruences.
    T::axiom_sub_is_add_neg(pt1.add(delta), pt1.add(delta));
    T::axiom_sub_is_add_neg(pt1, pt1);
    T::axiom_sub_is_add_neg(pt2, pt2);

    // The key insight: child_y(pt, n) - child_y(pt, 0) = child_y(pt, n) - pt
    // and the offset invariant shows this difference is the same for any pt.
    // We instantiate enough axioms for the SMT solver to close the gap.
    T::axiom_add_inverse_right(pt1);
    T::axiom_add_inverse_right(pt2);
    T::axiom_add_associative(
        child_y_position(pt1, sizes, sp, n), delta, pt1.add(delta).neg(),
    );
    T::axiom_add_associative(
        child_y_position(pt1, sizes, sp, n), delta, pt2.neg(),
    );
}

} // verus!
