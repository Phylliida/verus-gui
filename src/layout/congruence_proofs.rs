use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use verus_algebra::convex::two;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};
use crate::layout::*;
use crate::widget::*;

verus! {

// ══════════════════════════════════════════════════════════════════════
// Primitive congruence: min, max, clamp respect eqv
// ══════════════════════════════════════════════════════════════════════

/// min respects eqv: if a1 ≡ a2 and b1 ≡ b2, then min(a1,b1) ≡ min(a2,b2).
pub proof fn lemma_min_congruence<T: OrderedRing>(a1: T, a2: T, b1: T, b2: T)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        min::<T>(a1, b1).eqv(min::<T>(a2, b2)),
{
    T::axiom_le_total(a1, b1);
    T::axiom_le_total(a2, b2);
    if a1.le(b1) {
        // min(a1,b1) = a1
        if a2.le(b2) {
            // min(a2,b2) = a2, need a1 ≡ a2 ✓
        } else {
            // min(a2,b2) = b2, need a1 ≡ b2
            // a1 ≤ b1 and ¬(a2 ≤ b2), with a1≡a2, b1≡b2
            // a2 ≤ b2 would follow from a1 ≤ b1 by le_congruence — contradiction
            T::axiom_le_congruence(a1, a2, b1, b2);
            // a2 ≤ b2, contradiction with ¬(a2 ≤ b2)
            assert(false);
        }
    } else {
        // min(a1,b1) = b1
        if a2.le(b2) {
            // min(a2,b2) = a2, need b1 ≡ a2
            // ¬(a1 ≤ b1), so by totality b1 ≤ a1 (strict)
            T::axiom_le_total(b1, a1);
            // b1 ≤ a1 with b1≡b2, a1≡a2 → b2 ≤ a2
            T::axiom_le_congruence(b1, b2, a1, a2);
            // b2 ≤ a2 and a2 ≤ b2 → a2 ≡ b2 → a2 ≡ b1 (by transitivity with b2≡b1)
            T::axiom_le_antisymmetric(a2, b2);
            // a2 ≡ b2, and b1 ≡ b2, so b1 ≡ b2 ≡ a2
            T::axiom_eqv_symmetric(a2, b2); // b2 ≡ a2
            T::axiom_eqv_transitive(b1, b2, a2);
        } else {
            // min(a2,b2) = b2, need b1 ≡ b2 ✓
        }
    }
}

/// max respects eqv: if a1 ≡ a2 and b1 ≡ b2, then max(a1,b1) ≡ max(a2,b2).
pub proof fn lemma_max_congruence<T: OrderedRing>(a1: T, a2: T, b1: T, b2: T)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        max::<T>(a1, b1).eqv(max::<T>(a2, b2)),
{
    T::axiom_le_total(a1, b1);
    T::axiom_le_total(a2, b2);
    if a1.le(b1) {
        // max(a1,b1) = b1
        if a2.le(b2) {
            // max(a2,b2) = b2, need b1 ≡ b2 ✓
        } else {
            // max(a2,b2) = a2, need b1 ≡ a2
            T::axiom_le_congruence(a1, a2, b1, b2);
            assert(false); // a2 ≤ b2 contradicts ¬(a2 ≤ b2)
        }
    } else {
        // max(a1,b1) = a1
        if a2.le(b2) {
            // max(a2,b2) = b2, need a1 ≡ b2
            T::axiom_le_total(b1, a1);
            T::axiom_le_congruence(b1, b2, a1, a2);
            T::axiom_le_antisymmetric(a2, b2);
            T::axiom_eqv_symmetric(a1, a2);
            T::axiom_eqv_transitive(a1, a2, b2);
        } else {
            // max(a2,b2) = a2, need a1 ≡ a2 ✓
        }
    }
}

/// clamp respects eqv on all three arguments.
pub proof fn lemma_clamp_congruence<T: OrderedRing>(
    val1: T, val2: T, lo1: T, lo2: T, hi1: T, hi2: T,
)
    requires
        val1.eqv(val2),
        lo1.eqv(lo2),
        hi1.eqv(hi2),
    ensures
        Limits::clamp(val1, lo1, hi1).eqv(Limits::clamp(val2, lo2, hi2)),
{
    // clamp(val, lo, hi) = max(lo, min(val, hi))
    lemma_min_congruence(val1, val2, hi1, hi2);
    lemma_max_congruence(lo1, lo2, min::<T>(val1, hi1), min::<T>(val2, hi2));
}

// ══════════════════════════════════════════════════════════════════════
// Size / Limits / Padding eqv predicates and congruence
// ══════════════════════════════════════════════════════════════════════

/// Two sizes are field-wise eqv.
pub open spec fn size_eqv<T: OrderedRing>(a: Size<T>, b: Size<T>) -> bool {
    a.width.eqv(b.width) && a.height.eqv(b.height)
}

/// Two paddings are field-wise eqv.
pub open spec fn padding_eqv<T: OrderedRing>(a: Padding<T>, b: Padding<T>) -> bool {
    a.top.eqv(b.top) && a.right.eqv(b.right)
    && a.bottom.eqv(b.bottom) && a.left.eqv(b.left)
}

/// Two limits are field-wise eqv.
pub open spec fn limits_eqv<T: OrderedRing>(a: Limits<T>, b: Limits<T>) -> bool {
    size_eqv(a.min, b.min) && size_eqv(a.max, b.max)
}

/// Two nodes are field-wise eqv (top-level only, not children).
pub open spec fn node_eqv<T: OrderedRing>(a: Node<T>, b: Node<T>) -> bool {
    a.x.eqv(b.x) && a.y.eqv(b.y) && size_eqv(a.size, b.size)
    && a.children.len() == b.children.len()
}

/// Limits::resolve respects eqv.
pub proof fn lemma_resolve_congruence<T: OrderedRing>(
    lim1: Limits<T>, lim2: Limits<T>, size1: Size<T>, size2: Size<T>,
)
    requires
        limits_eqv(lim1, lim2),
        size_eqv(size1, size2),
    ensures
        size_eqv(lim1.resolve(size1), lim2.resolve(size2)),
{
    lemma_clamp_congruence(size1.width, size2.width,
        lim1.min.width, lim2.min.width, lim1.max.width, lim2.max.width);
    lemma_clamp_congruence(size1.height, size2.height,
        lim1.min.height, lim2.min.height, lim1.max.height, lim2.max.height);
}

// ══════════════════════════════════════════════════════════════════════
// Alignment congruence
// ══════════════════════════════════════════════════════════════════════

/// sub respects eqv: a1 ≡ a2 && b1 ≡ b2 → a1.sub(b1) ≡ a2.sub(b2).
pub proof fn lemma_sub_congruence<T: OrderedField>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2),
    ensures a1.sub(b1).eqv(a2.sub(b2)),
{
    T::axiom_sub_is_add_neg(a1, b1);
    T::axiom_sub_is_add_neg(a2, b2);
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_congruence::<T>(b1, b2);
    T::axiom_add_congruence_left(a1, a2, b1.neg());
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        a2, b1.neg(), b2.neg(),
    );
    T::axiom_eqv_transitive(
        a1.add(b1.neg()), a2.add(b1.neg()), a2.add(b2.neg()),
    );
    // a1.sub(b1) ≡ a1.add(b1.neg()) ≡ a2.add(b2.neg()) ≡ a2.sub(b2)
    T::axiom_eqv_symmetric(a1.sub(b1), a1.add(b1.neg()));
    T::axiom_eqv_transitive(a1.sub(b1), a1.add(b1.neg()), a2.add(b2.neg()));
    T::axiom_eqv_symmetric(a2.sub(b2), a2.add(b2.neg()));
    T::axiom_eqv_transitive(a1.sub(b1), a2.add(b2.neg()), a2.sub(b2));
}

/// align_offset(Start) respects eqv.
pub proof fn lemma_align_offset_start_congruence<T: OrderedField>(
    avail1: T, avail2: T, used1: T, used2: T,
)
    requires avail1.eqv(avail2), used1.eqv(used2),
    ensures
        align_offset(Alignment::Start, avail1, used1)
            .eqv(align_offset(Alignment::Start, avail2, used2)),
{
    T::axiom_eqv_reflexive(T::zero());
}

/// align_offset(Center) respects eqv.
pub proof fn lemma_align_offset_center_congruence<T: OrderedField>(
    avail1: T, avail2: T, used1: T, used2: T,
)
    requires avail1.eqv(avail2), used1.eqv(used2),
    ensures
        align_offset(Alignment::Center, avail1, used1)
            .eqv(align_offset(Alignment::Center, avail2, used2)),
{
    lemma_sub_congruence(avail1, avail2, used1, used2);
    T::axiom_eqv_reflexive(two::<T>());
    verus_algebra::convex::lemma_two_nonzero::<T>();
    verus_algebra::quadratic::lemma_div_congruence::<T>(
        avail1.sub(used1), avail2.sub(used2), two::<T>(), two::<T>(),
    );
}

/// align_offset(End) respects eqv.
pub proof fn lemma_align_offset_end_congruence<T: OrderedField>(
    avail1: T, avail2: T, used1: T, used2: T,
)
    requires avail1.eqv(avail2), used1.eqv(used2),
    ensures
        align_offset(Alignment::End, avail1, used1)
            .eqv(align_offset(Alignment::End, avail2, used2)),
{
    lemma_sub_congruence(avail1, avail2, used1, used2);
}

/// align_offset respects eqv on its rational arguments (all alignments).
pub proof fn lemma_align_offset_congruence<T: OrderedField>(
    alignment: Alignment,
    avail1: T, avail2: T,
    used1: T, used2: T,
)
    requires
        avail1.eqv(avail2),
        used1.eqv(used2),
    ensures
        align_offset(alignment, avail1, used1)
            .eqv(align_offset(alignment, avail2, used2)),
{
    match alignment {
        Alignment::Start => lemma_align_offset_start_congruence(avail1, avail2, used1, used2),
        Alignment::Center => lemma_align_offset_center_congruence(avail1, avail2, used1, used2),
        Alignment::End => lemma_align_offset_end_congruence(avail1, avail2, used1, used2),
    }
}

// ══════════════════════════════════════════════════════════════════════
// Padding helpers congruence
// ══════════════════════════════════════════════════════════════════════

/// Padding::horizontal respects eqv.
pub proof fn lemma_padding_horizontal_congruence<T: OrderedRing>(
    p1: Padding<T>, p2: Padding<T>,
)
    requires padding_eqv(p1, p2),
    ensures p1.horizontal().eqv(p2.horizontal()),
{
    T::axiom_add_congruence_left(p1.left, p2.left, p1.right);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        p2.left, p1.right, p2.right,
    );
    T::axiom_eqv_transitive(
        p1.left.add(p1.right), p2.left.add(p1.right), p2.left.add(p2.right),
    );
}

/// Padding::vertical respects eqv.
pub proof fn lemma_padding_vertical_congruence<T: OrderedRing>(
    p1: Padding<T>, p2: Padding<T>,
)
    requires padding_eqv(p1, p2),
    ensures p1.vertical().eqv(p2.vertical()),
{
    T::axiom_add_congruence_left(p1.top, p2.top, p1.bottom);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        p2.top, p1.bottom, p2.bottom,
    );
    T::axiom_eqv_transitive(
        p1.top.add(p1.bottom), p2.top.add(p1.bottom), p2.top.add(p2.bottom),
    );
}

// ══════════════════════════════════════════════════════════════════════
// Layout leaf congruence
// ══════════════════════════════════════════════════════════════════════

/// layout_leaf respects eqv: if limits and leaf fields are eqv,
/// the resulting node is eqv.
pub proof fn lemma_layout_leaf_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    leaf1: LeafWidget<T>, leaf2: LeafWidget<T>,
)
    requires
        limits_eqv(lim1, lim2),
        match (leaf1, leaf2) {
            (LeafWidget::Leaf { size: s1 }, LeafWidget::Leaf { size: s2 }) =>
                size_eqv(s1, s2),
            (LeafWidget::TextInput { preferred_size: s1, text_input_id: id1, .. },
             LeafWidget::TextInput { preferred_size: s2, text_input_id: id2, .. }) =>
                size_eqv(s1, s2) && id1 == id2,
            _ => false,
        },
    ensures
        node_eqv(
            layout_leaf(lim1, leaf1),
            layout_leaf(lim2, leaf2),
        ),
{
    T::axiom_eqv_reflexive(T::zero());
    match (leaf1, leaf2) {
        (LeafWidget::Leaf { size: s1 }, LeafWidget::Leaf { size: s2 }) => {
            lemma_resolve_congruence(lim1, lim2, s1, s2);
        },
        (LeafWidget::TextInput { preferred_size: s1, .. },
         LeafWidget::TextInput { preferred_size: s2, .. }) => {
            lemma_resolve_congruence(lim1, lim2, s1, s2);
        },
        _ => {},
    }
}

} // verus!
