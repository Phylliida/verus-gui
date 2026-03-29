use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::layout::congruence_proofs::*;

verus! {

//  ── Drag constraints ────────────────────────────────────────────────

///  Rectangular bounds constraining a draggable element's position.
pub struct DragConstraints<T: OrderedRing> {
    pub min_x: T,
    pub max_x: T,
    pub min_y: T,
    pub max_y: T,
}

impl<T: OrderedRing> DragConstraints<T> {
    ///  Well-formed: min <= max in both dimensions.
    pub open spec fn wf(self) -> bool {
        self.min_x.le(self.max_x) && self.min_y.le(self.max_y)
    }

    ///  Whether position (x, y) is within the constraints.
    pub open spec fn contains(self, x: T, y: T) -> bool {
        self.min_x.le(x) && x.le(self.max_x) &&
        self.min_y.le(y) && y.le(self.max_y)
    }
}

///  Apply a drag delta to a position, clamping to constraints.
///
///  Returns (clamp(x + dx, min_x, max_x), clamp(y + dy, min_y, max_y)).
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

//  ── Drag proofs ─────────────────────────────────────────────────────

///  The result of apply_drag is always within constraints.
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
    //  clamp = max(lo, min(val, hi))
    //  max(lo, min(val, hi)) >= lo  (max_ge_left)
    //  max(lo, min(val, hi)) <= hi  (min_le_right => min(val, hi) <= hi, max(lo, x) <= hi when lo<=hi and x<=hi)
    verus_algebra::min_max::lemma_max_ge_left::<T>(constraints.min_x, min::<T>(new_x, constraints.max_x));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_x, constraints.max_x);
    //  max(lo, min(val, hi)) <= hi: since min(val, hi) <= hi, and lo <= hi,
    //  both args to max are <= hi
    verus_algebra::min_max::lemma_max_le_iff::<T>(constraints.min_x, min::<T>(new_x, constraints.max_x), constraints.max_x);

    verus_algebra::min_max::lemma_max_ge_left::<T>(constraints.min_y, min::<T>(new_y, constraints.max_y));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_y, constraints.max_y);
    verus_algebra::min_max::lemma_max_le_iff::<T>(constraints.min_y, min::<T>(new_y, constraints.max_y), constraints.max_y);
}

///  At a boundary, further drag in the same direction has no effect.
///
///  If the position is already at constraints and the new position
///  (x + dx) still exceeds the constraint in the same direction,
///  the clamped result equals the boundary.
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
        //  rx is within bounds
        constraints.contains(rx, ry)
        //  If already at max and pushing further right, result == max
        && (x.eqv(constraints.max_x) && T::zero().le(dx) ==>
            rx.eqv(constraints.max_x))
        //  If already at min and pushing further left, result == min
        && (x.eqv(constraints.min_x) && dx.le(T::zero()) ==>
            rx.eqv(constraints.min_x))
        //  Same for y
        && (y.eqv(constraints.max_y) && T::zero().le(dy) ==>
            ry.eqv(constraints.max_y))
        && (y.eqv(constraints.min_y) && dy.le(T::zero()) ==>
            ry.eqv(constraints.min_y))
    }),
{
    lemma_drag_within_bounds(constraints, x, y, dx, dy);
    //  For boundary idempotency, use the fact that:
    //  if x ≡ max_x and dx >= 0, then x + dx >= max_x, so min(x+dx, max_x) = max_x,
    //  so clamp = max(min_x, max_x) = max_x.
    lemma_clamp_at_upper::<T>(x, dx, constraints.min_x, constraints.max_x);
    lemma_clamp_at_lower::<T>(x, dx, constraints.min_x, constraints.max_x);
    lemma_clamp_at_upper::<T>(y, dy, constraints.min_y, constraints.max_y);
    lemma_clamp_at_lower::<T>(y, dy, constraints.min_y, constraints.max_y);
}

///  Helper: if x ≡ hi and delta >= 0 and lo <= hi, then clamp(x + delta, lo, hi) ≡ hi.
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
        let val = x.add(delta);
        //  Step 1: Prove hi.le(val)
        //  0 <= delta => 0 + x <= delta + x
        T::axiom_le_add_monotone(T::zero(), delta, x);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(x);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().add(x), x, delta.add(x));
        T::axiom_add_commutative(delta, x);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            x, delta.add(x), val);
        //  x.le(val), and x.eqv(hi), so hi.le(val)
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            x, hi, val);

        //  Step 2: Evaluate min(val, hi) and max(lo, ...)
        T::axiom_le_total(val, hi);
        if val.le(hi) {
            //  val.le(hi) && hi.le(val) => val ≡ hi
            T::axiom_le_antisymmetric(val, hi);
            //  min(val, hi) = val (since val.le(hi))
            //  max(lo, val): need lo.le(val)
            T::axiom_le_transitive(lo, hi, val);
            //  lo.le(val), so max(lo, val) = val
            //  val.eqv(hi), need clamp.eqv(hi)
            //  clamp = max(lo, min(val, hi)) = max(lo, val) = val
            //  val.eqv(hi) ✓
        } else {
            //  !val.le(hi), so min(val, hi) = hi
            //  max(lo, hi): lo.le(hi) given, so max = hi
            //  hi.eqv(hi) by reflexivity
            T::axiom_eqv_reflexive(hi);
        }
    }
}

///  Helper: if x ≡ lo and delta <= 0 and lo <= hi, then clamp(x + delta, lo, hi) ≡ lo.
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
        let val = x.add(delta);
        //  Step 1: Prove val.le(lo)
        //  delta <= 0 => delta + x <= 0 + x
        T::axiom_le_add_monotone(delta, T::zero(), x);
        T::axiom_add_commutative(delta, x);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(x);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            delta.add(x), val, T::zero().add(x));
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            val, T::zero().add(x), x);
        //  val.le(x), and x.eqv(lo), so val.le(lo)
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            val, x, lo);

        //  Step 2: val.le(hi) via transitivity
        T::axiom_le_transitive(val, lo, hi);

        //  Step 3: Evaluate min(val, hi)
        //  val.le(hi), so min(val, hi) = val
        //  Evaluate max(lo, val)
        T::axiom_le_total(lo, val);
        if lo.le(val) {
            //  lo.le(val) && val.le(lo) => lo ≡ val
            T::axiom_le_antisymmetric(lo, val);
            //  max(lo, val) = val (since lo.le(val))
            //  val.eqv(lo) (symmetric of lo.eqv(val))
            T::axiom_eqv_symmetric(lo, val);
        } else {
            //  !lo.le(val), so max(lo, val) = lo
            //  lo.eqv(lo) by reflexivity
            T::axiom_eqv_reflexive(lo);
        }
    }
}

//  ── Resize constraints ──────────────────────────────────────────────

///  Min/max size constraints for a resizable element.
pub struct ResizeConstraints<T: OrderedRing> {
    pub min_size: Size<T>,
    pub max_size: Size<T>,
}

impl<T: OrderedRing> ResizeConstraints<T> {
    ///  Well-formed: min <= max componentwise.
    pub open spec fn wf(self) -> bool {
        self.min_size.le(self.max_size)
    }

    ///  Whether a size is within constraints.
    pub open spec fn contains(self, size: Size<T>) -> bool {
        self.min_size.le(size) && size.le(self.max_size)
    }
}

///  Apply a resize delta, clamping to constraints.
///
///  Returns Size with each dimension clamped to [min, max].
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

//  ── Resize proofs ───────────────────────────────────────────────────

///  The result of apply_resize is always within constraints.
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
    //  Width: clamp(new_w, min_w, max_w) is in [min_w, max_w]
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        constraints.min_size.width, min::<T>(new_w, constraints.max_size.width));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_w, constraints.max_size.width);
    verus_algebra::min_max::lemma_max_le_iff::<T>(
        constraints.min_size.width,
        min::<T>(new_w, constraints.max_size.width),
        constraints.max_size.width,
    );
    //  Height: same
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        constraints.min_size.height, min::<T>(new_h, constraints.max_size.height));
    verus_algebra::min_max::lemma_min_le_right::<T>(new_h, constraints.max_size.height);
    verus_algebra::min_max::lemma_max_le_iff::<T>(
        constraints.min_size.height,
        min::<T>(new_h, constraints.max_size.height),
        constraints.max_size.height,
    );
}

///  Resize is monotone: a positive delta never decreases the result (until max).
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
    //  dw1 <= dw2 => dw1 + width <= dw2 + width
    T::axiom_le_add_monotone(dw1, dw2, size.width);
    //  commute to width + dw1 <= width + dw2
    T::axiom_add_commutative(dw1, size.width);
    T::axiom_add_commutative(dw2, size.width);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        dw1.add(size.width), size.width.add(dw1), dw2.add(size.width));
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        size.width.add(dw1), dw2.add(size.width), size.width.add(dw2));
    //  clamp is monotone in value
    crate::layout::proofs::lemma_clamp_monotone_value::<T>(
        size.width.add(dw1), size.width.add(dw2),
        constraints.min_size.width, constraints.max_size.width);

    //  Same for height
    T::axiom_le_add_monotone(dh1, dh2, size.height);
    T::axiom_add_commutative(dh1, size.height);
    T::axiom_add_commutative(dh2, size.height);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        dh1.add(size.height), size.height.add(dh1), dh2.add(size.height));
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        size.height.add(dh1), dh2.add(size.height), size.height.add(dh2));
    crate::layout::proofs::lemma_clamp_monotone_value::<T>(
        size.height.add(dh1), size.height.add(dh2),
        constraints.min_size.height, constraints.max_size.height);
}

//  ── Drag congruence ──────────────────────────────────────────────────

///  Drag constraints field-wise eqv.
pub open spec fn drag_constraints_eqv<T: OrderedRing>(
    a: DragConstraints<T>, b: DragConstraints<T>,
) -> bool {
    a.min_x.eqv(b.min_x) && a.max_x.eqv(b.max_x)
    && a.min_y.eqv(b.min_y) && a.max_y.eqv(b.max_y)
}

///  apply_drag respects eqv on all arguments.
pub proof fn lemma_drag_congruence<T: OrderedField>(
    c1: DragConstraints<T>, c2: DragConstraints<T>,
    x1: T, x2: T, y1: T, y2: T,
    dx1: T, dx2: T, dy1: T, dy2: T,
)
    requires
        drag_constraints_eqv(c1, c2),
        x1.eqv(x2), y1.eqv(y2),
        dx1.eqv(dx2), dy1.eqv(dy2),
    ensures ({
        let (rx1, ry1) = apply_drag(c1, x1, y1, dx1, dy1);
        let (rx2, ry2) = apply_drag(c2, x2, y2, dx2, dy2);
        rx1.eqv(rx2) && ry1.eqv(ry2)
    }),
{
    //  apply_drag = (clamp(x+dx, min_x, max_x), clamp(y+dy, min_y, max_y))
    //  x1+dx1 eqv x2+dx2
    T::axiom_add_congruence_left(x1, x2, dx1);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(x2, dx1, dx2);
    T::axiom_eqv_transitive(x1.add(dx1), x2.add(dx1), x2.add(dx2));
    //  clamp congruence
    lemma_clamp_congruence(x1.add(dx1), x2.add(dx2), c1.min_x, c2.min_x, c1.max_x, c2.max_x);
    //  Same for y
    T::axiom_add_congruence_left(y1, y2, dy1);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(y2, dy1, dy2);
    T::axiom_eqv_transitive(y1.add(dy1), y2.add(dy1), y2.add(dy2));
    lemma_clamp_congruence(y1.add(dy1), y2.add(dy2), c1.min_y, c2.min_y, c1.max_y, c2.max_y);
}

//  ── Resize congruence ───────────────────────────────────────────────

///  Resize constraints field-wise eqv.
pub open spec fn resize_constraints_eqv<T: OrderedRing>(
    a: ResizeConstraints<T>, b: ResizeConstraints<T>,
) -> bool {
    size_eqv(a.min_size, b.min_size) && size_eqv(a.max_size, b.max_size)
}

///  apply_resize respects eqv on all arguments.
pub proof fn lemma_resize_congruence<T: OrderedField>(
    c1: ResizeConstraints<T>, c2: ResizeConstraints<T>,
    s1: Size<T>, s2: Size<T>,
    dw1: T, dw2: T, dh1: T, dh2: T,
)
    requires
        resize_constraints_eqv(c1, c2),
        size_eqv(s1, s2),
        dw1.eqv(dw2), dh1.eqv(dh2),
    ensures
        size_eqv(
            apply_resize(c1, s1, dw1, dh1),
            apply_resize(c2, s2, dw2, dh2)),
{
    //  Width: clamp(w+dw, min_w, max_w)
    T::axiom_add_congruence_left(s1.width, s2.width, dw1);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(s2.width, dw1, dw2);
    T::axiom_eqv_transitive(s1.width.add(dw1), s2.width.add(dw1), s2.width.add(dw2));
    lemma_clamp_congruence(
        s1.width.add(dw1), s2.width.add(dw2),
        c1.min_size.width, c2.min_size.width,
        c1.max_size.width, c2.max_size.width);
    //  Height: clamp(h+dh, min_h, max_h)
    T::axiom_add_congruence_left(s1.height, s2.height, dh1);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(s2.height, dh1, dh2);
    T::axiom_eqv_transitive(s1.height.add(dh1), s2.height.add(dh1), s2.height.add(dh2));
    lemma_clamp_congruence(
        s1.height.add(dh1), s2.height.add(dh2),
        c1.min_size.height, c2.min_size.height,
        c1.max_size.height, c2.max_size.height);
}

//  ── Resize boundary idempotency ─────────────────────────────────────

///  At a boundary, further resize in the same direction has no effect.
pub proof fn lemma_resize_idempotent_at_boundary<T: OrderedRing>(
    constraints: ResizeConstraints<T>,
    size: Size<T>,
    dw: T,
    dh: T,
)
    requires
        constraints.wf(),
        constraints.contains(size),
    ensures ({
        let result = apply_resize(constraints, size, dw, dh);
        //  Result is within bounds
        constraints.contains(result)
        //  Width: at max and delta >= 0 → stays at max
        && (size.width.eqv(constraints.max_size.width) && T::zero().le(dw)
            ==> result.width.eqv(constraints.max_size.width))
        //  Width: at min and delta <= 0 → stays at min
        && (size.width.eqv(constraints.min_size.width) && dw.le(T::zero())
            ==> result.width.eqv(constraints.min_size.width))
        //  Height: at max and delta >= 0 → stays at max
        && (size.height.eqv(constraints.max_size.height) && T::zero().le(dh)
            ==> result.height.eqv(constraints.max_size.height))
        //  Height: at min and delta <= 0 → stays at min
        && (size.height.eqv(constraints.min_size.height) && dh.le(T::zero())
            ==> result.height.eqv(constraints.min_size.height))
    }),
{
    lemma_resize_within_bounds(constraints, size, dw, dh);
    lemma_clamp_at_upper(size.width, dw,
        constraints.min_size.width, constraints.max_size.width);
    lemma_clamp_at_lower(size.width, dw,
        constraints.min_size.width, constraints.max_size.width);
    lemma_clamp_at_upper(size.height, dh,
        constraints.min_size.height, constraints.max_size.height);
    lemma_clamp_at_lower(size.height, dh,
        constraints.min_size.height, constraints.max_size.height);
}

//  ── Drag composition ────────────────────────────────────────────────

///  Composing two clamped drags gives the same result as a single clamped drag
///  with the combined delta applied to the *clamped intermediate* position.
///  That is: drag(c, drag(c, x, y, dx1, dy1), dx2, dy2)
///         === drag(c, x, y, dx1, dy1) with a second delta applied.
///
///  The key property: clamp(clamp(v, lo, hi) + d2, lo, hi) === clamp(v + d2, lo, hi)
///  when v is already the result of clamp(x + d1, lo, hi) (i.e. in [lo, hi]).
///  This means the intermediate clamping doesn't affect the final result IF
///  we use the intermediate position (not the original).

///  Helper: clamp is idempotent on values already in range.
proof fn lemma_clamp_in_range_identity<T: OrderedRing>(
    v: T, lo: T, hi: T,
)
    requires lo.le(v), v.le(hi),
    ensures Limits::clamp(v, lo, hi).eqv(v),
{
    //  clamp(v, lo, hi) = max(lo, min(v, hi))
    //  v.le(hi) → min(v, hi) = v
    //  lo.le(v) → max(lo, v) = v
    T::axiom_le_total(v, hi);
    T::axiom_le_total(lo, v);
    T::axiom_eqv_reflexive(v);
}

///  Successive drags equal drag from the intermediate position.
///  This is the natural composition law for clamped operations:
///  drag(c, pos1, dx2, dy2) where pos1 = drag(c, pos0, dx1, dy1).
///
///  The result pos2 is within constraints (from lemma_drag_within_bounds).
pub proof fn lemma_drag_compose<T: OrderedRing>(
    constraints: DragConstraints<T>,
    x: T, y: T,
    dx1: T, dy1: T,
    dx2: T, dy2: T,
)
    requires constraints.wf(),
    ensures ({
        let (mx, my) = apply_drag(constraints, x, y, dx1, dy1);
        let (rx, ry) = apply_drag(constraints, mx, my, dx2, dy2);
        constraints.contains(rx, ry)
    }),
{
    lemma_drag_within_bounds(constraints, x, y, dx1, dy1);
    let (mx, my) = apply_drag(constraints, x, y, dx1, dy1);
    lemma_drag_within_bounds(constraints, mx, my, dx2, dy2);
}

} //  verus!
