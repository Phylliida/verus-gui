use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;

verus! {

// ── Drag constraints ────────────────────────────────────────────────

/// Rectangular bounds constraining a draggable element's position.
pub struct DragConstraints<T: OrderedRing> {
    pub min_x: T,
    pub max_x: T,
    pub min_y: T,
    pub max_y: T,
}

impl<T: OrderedRing> DragConstraints<T> {
    /// Well-formed: min <= max in both dimensions.
    pub open spec fn wf(self) -> bool {
        self.min_x.le(self.max_x) && self.min_y.le(self.max_y)
    }

    /// Whether position (x, y) is within the constraints.
    pub open spec fn contains(self, x: T, y: T) -> bool {
        self.min_x.le(x) && x.le(self.max_x) &&
        self.min_y.le(y) && y.le(self.max_y)
    }
}

/// Apply a drag delta to a position, clamping to constraints.
///
/// Returns (clamp(x + dx, min_x, max_x), clamp(y + dy, min_y, max_y)).
pub open spec fn apply_drag<T: OrderedRing>(
    constraints: DragConstraints<T>,
    x: T,
    y: T,
    dx: T,
    dy: T,
) -> (T, T) {
    (
        Limits::clamp(x.add(dx), constraints.min_x, constraints.max_x),
        Limits::clamp(y.add(dy), constraints.min_y, constraints.max_y),
    )
}

// ── Drag proofs ─────────────────────────────────────────────────────

/// The result of apply_drag is always within constraints.
pub proof fn lemma_drag_within_bounds<T: OrderedRing>(
    constraints: DragConstraints<T>,
    x: T,
    y: T,
    dx: T,
    dy: T,
)
    requires
        constraints.wf(),
    ensures ({
        let (rx, ry) = apply_drag(constraints, x, y, dx, dy);
        constraints.contains(rx, ry)
    }),
{
    let new_x = x.add(dx);
    let new_y = y.add(dy);
    // clamp = max(lo, min(val, hi))
    // max(lo, min(val, hi)) >= lo  (max_ge_left)
    // max(lo, min(val, hi)) <= hi  (min_le_right => min(val, hi) <= hi, max(lo, x) <= hi when lo<=hi and x<=hi)
    verus_algebra::min_max::lemma_max_ge_left::<T>(constraints.min_x, min::<T>(new_x, constraints.max_x));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_x, constraints.max_x);
    // max(lo, min(val, hi)) <= hi: since min(val, hi) <= hi, and lo <= hi,
    // both args to max are <= hi
    verus_algebra::min_max::lemma_max_le_iff::<T>(constraints.min_x, min::<T>(new_x, constraints.max_x), constraints.max_x);

    verus_algebra::min_max::lemma_max_ge_left::<T>(constraints.min_y, min::<T>(new_y, constraints.max_y));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_y, constraints.max_y);
    verus_algebra::min_max::lemma_max_le_iff::<T>(constraints.min_y, min::<T>(new_y, constraints.max_y), constraints.max_y);
}

/// At a boundary, further drag in the same direction has no effect.
///
/// If the position is already at constraints and the new position
/// (x + dx) still exceeds the constraint in the same direction,
/// the clamped result equals the boundary.
pub proof fn lemma_drag_idempotent_at_boundary<T: OrderedRing>(
    constraints: DragConstraints<T>,
    x: T,
    y: T,
    dx: T,
    dy: T,
)
    requires
        constraints.wf(),
        constraints.contains(x, y),
    ensures ({
        let (rx, ry) = apply_drag(constraints, x, y, dx, dy);
        // rx is within bounds
        constraints.contains(rx, ry)
        // If already at max and pushing further right, result == max
        && (x.eqv(constraints.max_x) && T::zero().le(dx) ==>
            rx.eqv(constraints.max_x))
        // If already at min and pushing further left, result == min
        && (x.eqv(constraints.min_x) && dx.le(T::zero()) ==>
            rx.eqv(constraints.min_x))
        // Same for y
        && (y.eqv(constraints.max_y) && T::zero().le(dy) ==>
            ry.eqv(constraints.max_y))
        && (y.eqv(constraints.min_y) && dy.le(T::zero()) ==>
            ry.eqv(constraints.min_y))
    }),
{
    lemma_drag_within_bounds(constraints, x, y, dx, dy);
    // For boundary idempotency, use the fact that:
    // if x ≡ max_x and dx >= 0, then x + dx >= max_x, so min(x+dx, max_x) = max_x,
    // so clamp = max(min_x, max_x) = max_x.
    lemma_clamp_at_upper::<T>(x, dx, constraints.min_x, constraints.max_x);
    lemma_clamp_at_lower::<T>(x, dx, constraints.min_x, constraints.max_x);
    lemma_clamp_at_upper::<T>(y, dy, constraints.min_y, constraints.max_y);
    lemma_clamp_at_lower::<T>(y, dy, constraints.min_y, constraints.max_y);
}

/// Helper: if x ≡ hi and delta >= 0 and lo <= hi, then clamp(x + delta, lo, hi) ≡ hi.
proof fn lemma_clamp_at_upper<T: OrderedRing>(x: T, delta: T, lo: T, hi: T)
    requires
        lo.le(hi),
        lo.le(x),
        x.le(hi),
    ensures
        x.eqv(hi) && T::zero().le(delta) ==>
            Limits::clamp(x.add(delta), lo, hi).eqv(hi),
{
    if x.eqv(hi) && T::zero().le(delta) {
        // x + delta >= hi since x ≡ hi and delta >= 0
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_le_right::<T>(T::zero(), delta, x);
        // 0 + x <= delta + x, i.e., x <= x + delta
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(x);
        // 0 + x ≡ x
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
            T::zero().add(x), x, x.add(delta), x.add(delta));
        // So x <= x + delta
        // And x ≡ hi, so hi <= x + delta
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
            x, hi, x.add(delta), x.add(delta));
        // hi <= x + delta, so min(x + delta, hi) = hi
        // max(lo, hi) = hi since lo <= hi
    }
}

/// Helper: if x ≡ lo and delta <= 0 and lo <= hi, then clamp(x + delta, lo, hi) ≡ lo.
proof fn lemma_clamp_at_lower<T: OrderedRing>(x: T, delta: T, lo: T, hi: T)
    requires
        lo.le(hi),
        lo.le(x),
        x.le(hi),
    ensures
        x.eqv(lo) && delta.le(T::zero()) ==>
            Limits::clamp(x.add(delta), lo, hi).eqv(lo),
{
    if x.eqv(lo) && delta.le(T::zero()) {
        // x + delta <= x since delta <= 0
        // delta <= 0 => x + delta <= x + 0 = x
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_le_right::<T>(delta, T::zero(), x);
        // delta + x <= 0 + x
        T::axiom_add_commutative(delta, x);
        T::axiom_add_commutative(T::zero(), x);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(x);
        // x + delta ≡ delta + x <= 0 + x ≡ x
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
            delta.add(x), x.add(delta), T::zero().add(x), x);
        // x + delta <= x
        // x ≡ lo, so x + delta <= lo
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
            x.add(delta), x.add(delta), x, lo);
        // x + delta <= lo, so max(lo, min(x+delta, hi)) = max(lo, ...) = lo
        // since min(x+delta, hi) <= x+delta <= lo, and max(lo, y) when y <= lo is lo
    }
}

// ── Resize constraints ──────────────────────────────────────────────

/// Min/max size constraints for a resizable element.
pub struct ResizeConstraints<T: OrderedRing> {
    pub min_size: Size<T>,
    pub max_size: Size<T>,
}

impl<T: OrderedRing> ResizeConstraints<T> {
    /// Well-formed: min <= max componentwise.
    pub open spec fn wf(self) -> bool {
        self.min_size.le(self.max_size)
    }

    /// Whether a size is within constraints.
    pub open spec fn contains(self, size: Size<T>) -> bool {
        self.min_size.le(size) && size.le(self.max_size)
    }
}

/// Apply a resize delta, clamping to constraints.
///
/// Returns Size with each dimension clamped to [min, max].
pub open spec fn apply_resize<T: OrderedRing>(
    constraints: ResizeConstraints<T>,
    size: Size<T>,
    dw: T,
    dh: T,
) -> Size<T> {
    Size {
        width: Limits::clamp(
            size.width.add(dw),
            constraints.min_size.width,
            constraints.max_size.width,
        ),
        height: Limits::clamp(
            size.height.add(dh),
            constraints.min_size.height,
            constraints.max_size.height,
        ),
    }
}

// ── Resize proofs ───────────────────────────────────────────────────

/// The result of apply_resize is always within constraints.
pub proof fn lemma_resize_within_bounds<T: OrderedRing>(
    constraints: ResizeConstraints<T>,
    size: Size<T>,
    dw: T,
    dh: T,
)
    requires
        constraints.wf(),
    ensures
        constraints.contains(apply_resize(constraints, size, dw, dh)),
{
    let new_w = size.width.add(dw);
    let new_h = size.height.add(dh);
    // Width: clamp(new_w, min_w, max_w) is in [min_w, max_w]
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        constraints.min_size.width, min::<T>(new_w, constraints.max_size.width));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_w, constraints.max_size.width);
    verus_algebra::min_max::lemma_max_le_iff::<T>(
        constraints.min_size.width,
        min::<T>(new_w, constraints.max_size.width),
        constraints.max_size.width,
    );
    // Height: same
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        constraints.min_size.height, min::<T>(new_h, constraints.max_size.height));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_h, constraints.max_size.height);
    verus_algebra::min_max::lemma_max_le_iff::<T>(
        constraints.min_size.height,
        min::<T>(new_h, constraints.max_size.height),
        constraints.max_size.height,
    );
}

/// Resize is monotone: a positive delta never decreases the result (until max).
pub proof fn lemma_resize_monotone<T: OrderedRing>(
    constraints: ResizeConstraints<T>,
    size: Size<T>,
    dw1: T,
    dh1: T,
    dw2: T,
    dh2: T,
)
    requires
        constraints.wf(),
        dw1.le(dw2),
        dh1.le(dh2),
    ensures
        apply_resize(constraints, size, dw1, dh1).le(
            apply_resize(constraints, size, dw2, dh2)),
{
    // width + dw1 <= width + dw2 (by add_le_right)
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_le_right::<T>(
        dw1, dw2, size.width);
    T::axiom_add_commutative(dw1, size.width);
    T::axiom_add_commutative(dw2, size.width);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
        dw1.add(size.width), size.width.add(dw1),
        dw2.add(size.width), size.width.add(dw2));
    // clamp is monotone in value
    crate::layout::proofs::lemma_clamp_monotone_value::<T>(
        size.width.add(dw1), size.width.add(dw2),
        constraints.min_size.width, constraints.max_size.width);

    // Same for height
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_le_right::<T>(
        dh1, dh2, size.height);
    T::axiom_add_commutative(dh1, size.height);
    T::axiom_add_commutative(dh2, size.height);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_both::<T>(
        dh1.add(size.height), size.height.add(dh1),
        dh2.add(size.height), size.height.add(dh2));
    crate::layout::proofs::lemma_clamp_monotone_value::<T>(
        size.height.add(dh1), size.height.add(dh2),
        constraints.min_size.height, constraints.max_size.height);
}

} // verus!
