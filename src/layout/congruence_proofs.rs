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
use crate::diff::nodes_deeply_eqv;

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

/// align_offset respects eqv on its rational arguments.
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
    reveal(align_offset);
    match alignment {
        Alignment::Start => {
            T::axiom_eqv_reflexive(T::zero());
        },
        Alignment::Center => {
            lemma_sub_congruence(avail1, avail2, used1, used2);
            T::axiom_eqv_reflexive(two::<T>());
            verus_algebra::convex::lemma_two_nonzero::<T>();
            verus_algebra::quadratic::lemma_div_congruence::<T>(
                avail1.sub(used1), avail2.sub(used2), two::<T>(), two::<T>(),
            );
        },
        Alignment::End => {
            lemma_sub_congruence(avail1, avail2, used1, used2);
        },
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

// ══════════════════════════════════════════════════════════════════════
// Sequence-level eqv predicates
// ══════════════════════════════════════════════════════════════════════

/// Two size sequences are element-wise eqv.
pub open spec fn sizes_eqv<T: OrderedRing>(a: Seq<Size<T>>, b: Seq<Size<T>>) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==> size_eqv(a[i], b[i])
}

// ══════════════════════════════════════════════════════════════════════
// sum_weights congruence (scalar T sequence)
// ══════════════════════════════════════════════════════════════════════

/// sum_weights respects eqv on weight sequences.
pub proof fn lemma_sum_weights_congruence<T: OrderedRing>(
    w1: Seq<T>, w2: Seq<T>, count: nat,
)
    requires
        w1.len() == w2.len(),
        count <= w1.len(),
        forall|i: int| 0 <= i < w1.len() ==> w1[i].eqv(w2[i]),
    ensures
        crate::layout::flex::sum_weights(w1, count)
            .eqv(crate::layout::flex::sum_weights(w2, count)),
    decreases count,
{
    use crate::layout::flex::sum_weights;
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_sum_weights_congruence(w1, w2, (count - 1) as nat);
        T::axiom_add_congruence_left(
            sum_weights(w1, (count - 1) as nat),
            sum_weights(w2, (count - 1) as nat),
            w1[(count - 1) as int]);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            sum_weights(w2, (count - 1) as nat),
            w1[(count - 1) as int],
            w2[(count - 1) as int]);
        T::axiom_eqv_transitive(
            sum_weights(w1, (count - 1) as nat).add(w1[(count - 1) as int]),
            sum_weights(w2, (count - 1) as nat).add(w1[(count - 1) as int]),
            sum_weights(w2, (count - 1) as nat).add(w2[(count - 1) as int]));
    }
}

// ══════════════════════════════════════════════════════════════════════
// sum_heights / sum_widths congruence
// ══════════════════════════════════════════════════════════════════════

/// sum_heights respects eqv on sizes.
pub proof fn lemma_sum_heights_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>, count: nat,
)
    requires
        sizes_eqv(s1, s2),
        count <= s1.len(),
    ensures
        sum_heights(s1, count).eqv(sum_heights(s2, count)),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_sum_heights_congruence(s1, s2, (count - 1) as nat);
        // IH: sum_heights(s1, count-1) eqv sum_heights(s2, count-1)
        // s1[count-1].height eqv s2[count-1].height
        T::axiom_add_congruence_left(
            sum_heights(s1, (count - 1) as nat),
            sum_heights(s2, (count - 1) as nat),
            s1[(count - 1) as int].height,
        );
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            sum_heights(s2, (count - 1) as nat),
            s1[(count - 1) as int].height,
            s2[(count - 1) as int].height,
        );
        T::axiom_eqv_transitive(
            sum_heights(s1, (count - 1) as nat).add(s1[(count - 1) as int].height),
            sum_heights(s2, (count - 1) as nat).add(s1[(count - 1) as int].height),
            sum_heights(s2, (count - 1) as nat).add(s2[(count - 1) as int].height),
        );
    }
}

/// repeated_add respects eqv.
pub proof fn lemma_repeated_add_congruence<T: OrderedRing>(
    v1: T, v2: T, n: nat,
)
    requires v1.eqv(v2),
    ensures repeated_add(v1, n).eqv(repeated_add(v2, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_repeated_add_congruence(v1, v2, (n - 1) as nat);
        T::axiom_add_congruence_left(
            repeated_add(v1, (n - 1) as nat),
            repeated_add(v2, (n - 1) as nat),
            v1,
        );
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            repeated_add(v2, (n - 1) as nat), v1, v2,
        );
        T::axiom_eqv_transitive(
            repeated_add(v1, (n - 1) as nat).add(v1),
            repeated_add(v2, (n - 1) as nat).add(v1),
            repeated_add(v2, (n - 1) as nat).add(v2),
        );
    }
}

/// column_content_height respects eqv.
pub proof fn lemma_column_content_height_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    sp1: T, sp2: T,
)
    requires
        sizes_eqv(s1, s2),
        sp1.eqv(sp2),
    ensures
        column_content_height(s1, sp1).eqv(column_content_height(s2, sp2)),
{
    if s1.len() == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_sum_heights_congruence(s1, s2, s1.len() as nat);
        lemma_repeated_add_congruence(sp1, sp2, (s1.len() - 1) as nat);
        T::axiom_add_congruence_left(
            sum_heights(s1, s1.len() as nat),
            sum_heights(s2, s2.len() as nat),
            repeated_add(sp1, (s1.len() - 1) as nat),
        );
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            sum_heights(s2, s2.len() as nat),
            repeated_add(sp1, (s1.len() - 1) as nat),
            repeated_add(sp2, (s2.len() - 1) as nat),
        );
        T::axiom_eqv_transitive(
            sum_heights(s1, s1.len() as nat).add(repeated_add(sp1, (s1.len() - 1) as nat)),
            sum_heights(s2, s2.len() as nat).add(repeated_add(sp1, (s1.len() - 1) as nat)),
            sum_heights(s2, s2.len() as nat).add(repeated_add(sp2, (s2.len() - 1) as nat)),
        );
    }
}

/// child_y_position respects eqv on all arguments.
pub proof fn lemma_child_y_position_congruence<T: OrderedRing>(
    pt1: T, pt2: T,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    sp1: T, sp2: T,
    k: nat,
)
    requires
        pt1.eqv(pt2),
        sizes_eqv(s1, s2),
        sp1.eqv(sp2),
        k <= s1.len(),
    ensures
        child_y_position(pt1, s1, sp1, k)
            .eqv(child_y_position(pt2, s2, sp2, k)),
    decreases k,
{
    if k == 0 {
        // child_y(pt, 0) = pt
    } else {
        // IH
        lemma_child_y_position_congruence(pt1, pt2, s1, s2, sp1, sp2, (k - 1) as nat);
        let y1 = child_y_position(pt1, s1, sp1, (k - 1) as nat);
        let y2 = child_y_position(pt2, s2, sp2, (k - 1) as nat);
        // y1 eqv y2, s1[k-1].height eqv s2[k-1].height, sp1 eqv sp2
        // y1 + h1 eqv y2 + h2
        T::axiom_add_congruence_left(y1, y2, s1[(k-1) as int].height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            y2, s1[(k-1) as int].height, s2[(k-1) as int].height,
        );
        T::axiom_eqv_transitive(
            y1.add(s1[(k-1) as int].height), y2.add(s1[(k-1) as int].height),
            y2.add(s2[(k-1) as int].height),
        );
        // (y1+h1) + sp1 eqv (y2+h2) + sp2
        T::axiom_add_congruence_left(
            y1.add(s1[(k-1) as int].height), y2.add(s2[(k-1) as int].height), sp1,
        );
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            y2.add(s2[(k-1) as int].height), sp1, sp2,
        );
        T::axiom_eqv_transitive(
            y1.add(s1[(k-1) as int].height).add(sp1),
            y2.add(s2[(k-1) as int].height).add(sp1),
            y2.add(s2[(k-1) as int].height).add(sp2),
        );
    }
}

/// sum_main respects eqv (axis-parameterized version of sum_heights).
pub proof fn lemma_sum_main_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>, axis: Axis, count: nat,
)
    requires sizes_eqv(s1, s2), count <= s1.len(),
    ensures sum_main(s1, axis, count).eqv(sum_main(s2, axis, count)),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_sum_main_congruence(s1, s2, axis, (count - 1) as nat);
        // s1[count-1].main_dim(axis) eqv s2[count-1].main_dim(axis)
        // main_dim for Vertical = height, for Horizontal = width
        match axis {
            Axis::Vertical => {
                // main_dim = height
            },
            Axis::Horizontal => {
                // main_dim = width
            },
        }
        T::axiom_add_congruence_left(
            sum_main(s1, axis, (count - 1) as nat),
            sum_main(s2, axis, (count - 1) as nat),
            s1[(count - 1) as int].main_dim(axis));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            sum_main(s2, axis, (count - 1) as nat),
            s1[(count - 1) as int].main_dim(axis),
            s2[(count - 1) as int].main_dim(axis));
        T::axiom_eqv_transitive(
            sum_main(s1, axis, (count - 1) as nat).add(s1[(count - 1) as int].main_dim(axis)),
            sum_main(s2, axis, (count - 1) as nat).add(s1[(count - 1) as int].main_dim(axis)),
            sum_main(s2, axis, (count - 1) as nat).add(s2[(count - 1) as int].main_dim(axis)));
    }
}

// ══════════════════════════════════════════════════════════════════════
// column_children congruence
// ══════════════════════════════════════════════════════════════════════

/// column_children produces eqv nodes when all inputs are eqv.
pub proof fn lemma_column_children_congruence<T: OrderedField>(
    pad1: Padding<T>, pad2: Padding<T>,
    sp1: T, sp2: T,
    alignment: Alignment,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    avail_w1: T, avail_w2: T,
    index: nat,
)
    requires
        padding_eqv(pad1, pad2),
        sp1.eqv(sp2),
        sizes_eqv(s1, s2),
        avail_w1.eqv(avail_w2),
        index <= s1.len(),
    ensures
        column_children(pad1, sp1, alignment, s1, avail_w1, index).len()
            == column_children(pad2, sp2, alignment, s2, avail_w2, index).len(),
    decreases s1.len() - index,
{
    if index >= s1.len() {
        // Both return Seq::empty()
    } else {
        lemma_column_children_congruence(
            pad1, pad2, sp1, sp2, alignment, s1, s2, avail_w1, avail_w2, index + 1,
        );
    }
}

// ══════════════════════════════════════════════════════════════════════
// column_layout congruence
// ══════════════════════════════════════════════════════════════════════

/// column_layout produces an eqv-sized node when limits, padding, spacing,
/// and child sizes are all eqv.
pub proof fn lemma_column_layout_size_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    pad1: Padding<T>, pad2: Padding<T>,
    sp1: T, sp2: T,
    alignment: Alignment,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
)
    requires
        limits_eqv(lim1, lim2),
        padding_eqv(pad1, pad2),
        sp1.eqv(sp2),
        sizes_eqv(s1, s2),
    ensures
        size_eqv(
            column_layout(lim1, pad1, sp1, alignment, s1).size,
            column_layout(lim2, pad2, sp2, alignment, s2).size,
        ),
{
    reveal(column_layout);
    // column_layout produces:
    //   parent_size = limits.resolve(Size::new(limits.max.width, pad.vertical() + content_height))
    // The content_height depends on child_sizes and spacing.
    lemma_column_content_height_congruence(s1, s2, sp1, sp2);
    lemma_padding_vertical_congruence(pad1, pad2);
    // pad1.vertical() + content_height(s1, sp1) eqv pad2.vertical() + content_height(s2, sp2)
    T::axiom_add_congruence_left(
        pad1.vertical(), pad2.vertical(),
        column_content_height(s1, sp1),
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        pad2.vertical(),
        column_content_height(s1, sp1),
        column_content_height(s2, sp2),
    );
    T::axiom_eqv_transitive(
        pad1.vertical().add(column_content_height(s1, sp1)),
        pad2.vertical().add(column_content_height(s1, sp1)),
        pad2.vertical().add(column_content_height(s2, sp2)),
    );
    // Size::new(lim.max.width, total_height) is eqv
    let total_h1 = pad1.vertical().add(column_content_height(s1, sp1));
    let total_h2 = pad2.vertical().add(column_content_height(s2, sp2));
    let desired1 = Size::new(lim1.max.width, total_h1);
    let desired2 = Size::new(lim2.max.width, total_h2);
    // desired sizes are eqv
    assert(size_eqv(desired1, desired2));
    lemma_resolve_congruence(lim1, lim2, desired1, desired2);
}

// ══════════════════════════════════════════════════════════════════════
// Widget-level eqv predicate
// ══════════════════════════════════════════════════════════════════════

/// Two widgets are field-wise eqv (same variant, eqv rational fields,
/// recursively eqv children).
pub open spec fn widget_eqv<T: OrderedField>(
    a: Widget<T>, b: Widget<T>, fuel: nat,
) -> bool
    decreases fuel,
{
    if fuel == 0 {
        false
    } else {
        match (a, b) {
            (Widget::Leaf(la), Widget::Leaf(lb)) => match (la, lb) {
                (LeafWidget::Leaf { size: s1 }, LeafWidget::Leaf { size: s2 }) =>
                    size_eqv(s1, s2),
                (LeafWidget::TextInput { preferred_size: s1, text_input_id: id1, config: c1 },
                 LeafWidget::TextInput { preferred_size: s2, text_input_id: id2, config: c2 }) =>
                    size_eqv(s1, s2) && id1 == id2 && c1 == c2,
                _ => false,
            },
            (Widget::Wrapper(w1), Widget::Wrapper(w2)) => match (w1, w2) {
                (WrapperWidget::Margin { margin: m1, child: c1 },
                 WrapperWidget::Margin { margin: m2, child: c2 }) =>
                    padding_eqv(m1, m2) && widget_eqv(*c1, *c2, (fuel - 1) as nat),
                (WrapperWidget::Conditional { visible: v1, child: c1 },
                 WrapperWidget::Conditional { visible: v2, child: c2 }) =>
                    v1 == v2 && widget_eqv(*c1, *c2, (fuel - 1) as nat),
                (WrapperWidget::SizedBox { inner_limits: l1, child: c1 },
                 WrapperWidget::SizedBox { inner_limits: l2, child: c2 }) =>
                    limits_eqv(l1, l2) && widget_eqv(*c1, *c2, (fuel - 1) as nat),
                (WrapperWidget::AspectRatio { ratio: r1, child: c1 },
                 WrapperWidget::AspectRatio { ratio: r2, child: c2 }) =>
                    r1.eqv(r2) && !r1.eqv(T::zero())
                    && widget_eqv(*c1, *c2, (fuel - 1) as nat),
                (WrapperWidget::ScrollView { viewport: v1, scroll_x: sx1, scroll_y: sy1, child: c1 },
                 WrapperWidget::ScrollView { viewport: v2, scroll_x: sx2, scroll_y: sy2, child: c2 }) =>
                    size_eqv(v1, v2) && sx1.eqv(sx2) && sy1.eqv(sy2)
                    && widget_eqv(*c1, *c2, (fuel - 1) as nat),
                _ => false,
            },
            (Widget::Container(c1), Widget::Container(c2)) => match (c1, c2) {
                (ContainerWidget::Column { padding: p1, spacing: s1, alignment: a1, children: ch1 },
                 ContainerWidget::Column { padding: p2, spacing: s2, alignment: a2, children: ch2 }) =>
                    padding_eqv(p1, p2) && s1.eqv(s2) && a1 == a2
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::Row { padding: p1, spacing: s1, alignment: a1, children: ch1 },
                 ContainerWidget::Row { padding: p2, spacing: s2, alignment: a2, children: ch2 }) =>
                    padding_eqv(p1, p2) && s1.eqv(s2) && a1 == a2
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::Stack { padding: p1, h_align: ha1, v_align: va1, children: ch1 },
                 ContainerWidget::Stack { padding: p2, h_align: ha2, v_align: va2, children: ch2 }) =>
                    padding_eqv(p1, p2) && ha1 == ha2 && va1 == va2
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::Wrap { padding: p1, h_spacing: hs1, v_spacing: vs1, children: ch1 },
                 ContainerWidget::Wrap { padding: p2, h_spacing: hs2, v_spacing: vs2, children: ch2 }) =>
                    padding_eqv(p1, p2) && hs1.eqv(hs2) && vs1.eqv(vs2)
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::ListView { spacing: s1, scroll_y: sy1, viewport: v1, children: ch1 },
                 ContainerWidget::ListView { spacing: s2, scroll_y: sy2, viewport: v2, children: ch2 }) =>
                    s1.eqv(s2) && sy1.eqv(sy2) && size_eqv(v1, v2)
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::Flex { padding: p1, spacing: s1, alignment: a1, direction: d1, children: ch1 },
                 ContainerWidget::Flex { padding: p2, spacing: s2, alignment: a2, direction: d2, children: ch2 }) =>
                    padding_eqv(p1, p2) && s1.eqv(s2) && a1 == a2 && d1 == d2
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==> {
                        &&& ch1[i].weight.eqv(ch2[i].weight)
                        &&& widget_eqv(ch1[i].child, ch2[i].child, (fuel - 1) as nat)
                    },
                (ContainerWidget::Grid { padding: p1, h_spacing: hs1, v_spacing: vs1,
                    h_align: ha1, v_align: va1, col_widths: cw1, row_heights: rh1, children: ch1 },
                 ContainerWidget::Grid { padding: p2, h_spacing: hs2, v_spacing: vs2,
                    h_align: ha2, v_align: va2, col_widths: cw2, row_heights: rh2, children: ch2 }) =>
                    padding_eqv(p1, p2) && hs1.eqv(hs2) && vs1.eqv(vs2)
                    && ha1 == ha2 && va1 == va2
                    && sizes_eqv(cw1, cw2) && sizes_eqv(rh1, rh2)
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==>
                        widget_eqv(ch1[i], ch2[i], (fuel - 1) as nat),
                (ContainerWidget::Absolute { padding: p1, children: ch1 },
                 ContainerWidget::Absolute { padding: p2, children: ch2 }) =>
                    padding_eqv(p1, p2)
                    && ch1.len() == ch2.len()
                    && forall|i: int| 0 <= i < ch1.len() ==> {
                        &&& ch1[i].x.eqv(ch2[i].x)
                        &&& ch1[i].y.eqv(ch2[i].y)
                        &&& widget_eqv(ch1[i].child, ch2[i].child, (fuel - 1) as nat)
                    },
                _ => false,
            },
            _ => false,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════
// Limits::shrink congruence
// ══════════════════════════════════════════════════════════════════════

/// Limits::shrink respects eqv.
pub proof fn lemma_shrink_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: T, w2: T, h1: T, h2: T,
)
    requires
        limits_eqv(lim1, lim2),
        w1.eqv(w2), h1.eqv(h2),
    ensures
        limits_eqv(lim1.shrink(w1, h1), lim2.shrink(w2, h2)),
{
    // shrink keeps min the same, max = Size { max(min.w, max.w - w), max(min.h, max.h - h) }
    lemma_sub_congruence(lim1.max.width, lim2.max.width, w1, w2);
    lemma_max_congruence(
        lim1.min.width, lim2.min.width,
        lim1.max.width.sub(w1), lim2.max.width.sub(w2),
    );
    lemma_sub_congruence(lim1.max.height, lim2.max.height, h1, h2);
    lemma_max_congruence(
        lim1.min.height, lim2.min.height,
        lim1.max.height.sub(h1), lim2.max.height.sub(h2),
    );
}

// ══════════════════════════════════════════════════════════════════════
// Master layout congruence theorem
// ══════════════════════════════════════════════════════════════════════

/// Bridge: layout_widget for Column produces a size equal to column_layout's size.
/// Factored out to give Z3 a focused unfolding context (per rlimit optimization guide).
proof fn lemma_layout_widget_column_size_bridge<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, sp: T, al: Alignment,
    children: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures ({
        let inner = lim.shrink(pad.horizontal(), pad.vertical());
        let cs = Seq::new(children.len(), |i: int|
            layout_widget(inner, children[i], (fuel - 1) as nat).size);
        layout_widget(lim, Widget::Container(ContainerWidget::Column {
            padding: pad, spacing: sp, alignment: al, children,
        }), fuel).size == column_layout(lim, pad, sp, al, cs).size
    }),
{
    reveal(linear_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let cs = Seq::new(children.len(), |i: int|
        layout_widget(inner, children[i], (fuel - 1) as nat).size);

    // Expand step by step to help Z3:
    // 1. layout_widget → layout_container (fuel > 0, Container variant)
    let col = ContainerWidget::Column {
        padding: pad, spacing: sp, alignment: al, children,
    };
    let w = Widget::Container(col);
    assert(layout_widget(lim, w, fuel)
        == layout_container(lim, col, fuel));

    // 2. layout_container → layout_linear_body (fuel > 0, Column match arm)
    assert(layout_container(lim, col, fuel)
        == layout_linear_body(lim, pad, sp, al, cn, Axis::Vertical));

    // 3. layout_linear_body → merge_layout(linear_layout(...), cn)
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    assert(layout_linear_body(lim, pad, sp, al, cn, Axis::Vertical)
        == merge_layout(
            linear_layout(lim, pad, sp, al, child_sizes, Axis::Vertical), cn));

    // 4. merge_layout preserves .size
    // 5. child_sizes == cs (definitional — cn[i].size = layout_widget(inner, children[i], fuel-1).size)
    assert(child_sizes =~= cs);

    // 6. linear_layout == column_layout (bridge lemma)
    lemma_column_layout_is_linear(lim, pad, sp, al, cs);
}

/// row_layout produces an eqv-sized node (symmetric to column).
pub proof fn lemma_row_layout_size_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    pad1: Padding<T>, pad2: Padding<T>,
    sp1: T, sp2: T,
    alignment: Alignment,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
)
    requires
        limits_eqv(lim1, lim2),
        padding_eqv(pad1, pad2),
        sp1.eqv(sp2),
        sizes_eqv(s1, s2),
    ensures
        size_eqv(
            row_layout(lim1, pad1, sp1, alignment, s1).size,
            row_layout(lim2, pad2, sp2, alignment, s2).size,
        ),
{
    reveal(row_layout);
    // row_layout: parent_size = limits.resolve(Size::new(pad.horizontal() + content_width, limits.max.height))
    // content_width = row_content_width(child_sizes, spacing)
    //              = sum_widths(child_sizes, n) + repeated_add(spacing, n-1)  [for n > 0]
    // sum_widths congruence follows from sum_main congruence with Horizontal axis
    lemma_sum_main_congruence(s1, s2, Axis::Horizontal, s1.len() as nat);
    // Bridge: sum_main(Horizontal) == sum_widths
    lemma_sum_main_eq_sum_widths(s1, s1.len() as nat);
    lemma_sum_main_eq_sum_widths(s2, s2.len() as nat);
    // Now sum_widths(s1, n) == sum_main(s1, H, n) eqv sum_main(s2, H, n) == sum_widths(s2, n)
    lemma_repeated_add_congruence(sp1, sp2,
        if s1.len() > 0 { (s1.len() - 1) as nat } else { 0 });
    // row_content_width eqv
    if s1.len() == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        T::axiom_add_congruence_left(
            sum_widths(s1, s1.len() as nat),
            sum_widths(s2, s2.len() as nat),
            repeated_add(sp1, (s1.len() - 1) as nat));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            sum_widths(s2, s2.len() as nat),
            repeated_add(sp1, (s1.len() - 1) as nat),
            repeated_add(sp2, (s2.len() - 1) as nat));
        T::axiom_eqv_transitive(
            row_content_width(s1, sp1),
            sum_widths(s2, s2.len() as nat).add(repeated_add(sp1, (s1.len() - 1) as nat)),
            row_content_width(s2, sp2));
    }
    lemma_padding_horizontal_congruence(pad1, pad2);
    T::axiom_add_congruence_left(
        pad1.horizontal(), pad2.horizontal(), row_content_width(s1, sp1));
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        pad2.horizontal(), row_content_width(s1, sp1), row_content_width(s2, sp2));
    T::axiom_eqv_transitive(
        pad1.horizontal().add(row_content_width(s1, sp1)),
        pad2.horizontal().add(row_content_width(s1, sp1)),
        pad2.horizontal().add(row_content_width(s2, sp2)));
    lemma_resolve_congruence(lim1, lim2,
        Size::new(pad1.horizontal().add(row_content_width(s1, sp1)), lim1.max.height),
        Size::new(pad2.horizontal().add(row_content_width(s2, sp2)), lim2.max.height));
}

/// Bridge: layout_widget for Row produces size == row_layout size.
proof fn lemma_layout_widget_row_size_bridge<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, sp: T, al: Alignment,
    children: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures ({
        let inner = lim.shrink(pad.horizontal(), pad.vertical());
        let cs = Seq::new(children.len(), |i: int|
            layout_widget(inner, children[i], (fuel - 1) as nat).size);
        layout_widget(lim, Widget::Container(ContainerWidget::Row {
            padding: pad, spacing: sp, alignment: al, children,
        }), fuel).size == row_layout(lim, pad, sp, al, cs).size
    }),
{
    reveal(linear_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let cs = Seq::new(children.len(), |i: int|
        layout_widget(inner, children[i], (fuel - 1) as nat).size);

    let row = ContainerWidget::Row {
        padding: pad, spacing: sp, alignment: al, children,
    };
    let w = Widget::Container(row);
    assert(layout_widget(lim, w, fuel)
        == layout_container(lim, row, fuel));
    assert(layout_container(lim, row, fuel)
        == layout_linear_body(lim, pad, sp, al, cn, Axis::Horizontal));
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    assert(layout_linear_body(lim, pad, sp, al, cn, Axis::Horizontal)
        == merge_layout(
            linear_layout(lim, pad, sp, al, child_sizes, Axis::Horizontal), cn));
    assert(child_sizes =~= cs);
    lemma_row_layout_is_linear(lim, pad, sp, al, cs);
}

/// le is congruent in both arguments: a1.le(b1) == a2.le(b2) when eqv.
pub proof fn lemma_le_congruence_iff<T: OrderedRing>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2),
    ensures a1.le(b1) == a2.le(b2),
{
    T::axiom_le_total(a1, b1);
    if a1.le(b1) {
        T::axiom_le_congruence(a1, a2, b1, b2);
    } else {
        // ¬a1.le(b1) → b1.le(a1) by totality
        T::axiom_le_congruence(b1, b2, a1, a2);
        // b2.le(a2). If a2.le(b2), then antisymmetric → a2.eqv(b2).
        // a1.eqv(a2).eqv(b2).eqv(b1) → a1.eqv(b1) → a1.le(b1), contradiction.
        if a2.le(b2) {
            T::axiom_le_antisymmetric(a2, b2);
            T::axiom_eqv_transitive(a1, a2, b2);
            T::axiom_eqv_symmetric(b1, b2);
            T::axiom_eqv_transitive(a1, b2, b1);
            // a1.eqv(b1) → a1.le(b1):
            T::axiom_le_reflexive(a1);
            T::axiom_eqv_reflexive(a1);
            T::axiom_le_congruence(a1, a1, a1, b1);
            // a1.le(b1) contradicts our assumption
        }
    }
}

/// WrapCursor field-wise eqv.
pub open spec fn wrap_cursor_eqv<T: OrderedRing>(
    a: crate::layout::wrap::WrapCursor<T>,
    b: crate::layout::wrap::WrapCursor<T>,
) -> bool {
    a.x.eqv(b.x) && a.y.eqv(b.y) && a.line_height.eqv(b.line_height)
    && a.content_width.eqv(b.content_width)
}

/// wrap_cursor respects eqv on all arguments.
pub proof fn lemma_wrap_cursor_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    hs1: T, hs2: T, vs1: T, vs2: T,
    aw1: T, aw2: T,
    count: nat,
)
    requires
        sizes_eqv(s1, s2),
        hs1.eqv(hs2), vs1.eqv(vs2), aw1.eqv(aw2),
        count <= s1.len(),
    ensures
        wrap_cursor_eqv(
            crate::layout::wrap::wrap_cursor(s1, hs1, vs1, aw1, count),
            crate::layout::wrap::wrap_cursor(s2, hs2, vs2, aw2, count)),
    decreases count,
{
    use crate::layout::wrap::{wrap_cursor, wrap_needs_break};
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_wrap_cursor_congruence(s1, s2, hs1, hs2, vs1, vs2, aw1, aw2, (count - 1) as nat);
        let prev1 = wrap_cursor(s1, hs1, vs1, aw1, (count - 1) as nat);
        let prev2 = wrap_cursor(s2, hs2, vs2, aw2, (count - 1) as nat);
        let c1 = s1[(count - 1) as int];
        let c2 = s2[(count - 1) as int];
        // wrap_needs_break is congruent (uses le which is congruent)
        // needs_break(x, w, avail) = !x.le(0) && !(x+w).le(avail)
        T::axiom_eqv_reflexive(T::zero());
        lemma_le_congruence_iff(prev1.x, prev2.x, T::zero(), T::zero());
        T::axiom_add_congruence_left(prev1.x, prev2.x, c1.width);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            prev2.x, c1.width, c2.width);
        T::axiom_eqv_transitive(prev1.x.add(c1.width), prev2.x.add(c1.width), prev2.x.add(c2.width));
        lemma_le_congruence_iff(prev1.x.add(c1.width), prev2.x.add(c2.width), aw1, aw2);
        // So wrap_needs_break(prev1, c1, aw1) == wrap_needs_break(prev2, c2, aw2)
        if wrap_needs_break(prev1.x, c1.width, aw1) {
            // New line: x = c.width + hs, y = prev.y + prev.lh + vs, lh = c.height, cw = max(prev.cw, c.width)
            T::axiom_add_congruence_left(c1.width, c2.width, hs1);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                c2.width, hs1, hs2);
            T::axiom_eqv_transitive(c1.width.add(hs1), c2.width.add(hs1), c2.width.add(hs2));
            // y: prev.y + prev.lh + vs
            T::axiom_add_congruence_left(prev1.y, prev2.y, prev1.line_height);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                prev2.y, prev1.line_height, prev2.line_height);
            T::axiom_eqv_transitive(prev1.y.add(prev1.line_height), prev2.y.add(prev1.line_height),
                prev2.y.add(prev2.line_height));
            T::axiom_add_congruence_left(prev1.y.add(prev1.line_height), prev2.y.add(prev2.line_height), vs1);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                prev2.y.add(prev2.line_height), vs1, vs2);
            T::axiom_eqv_transitive(
                prev1.y.add(prev1.line_height).add(vs1),
                prev2.y.add(prev2.line_height).add(vs1),
                prev2.y.add(prev2.line_height).add(vs2));
            // content_width: max(prev.cw, c.width)
            lemma_max_congruence(prev1.content_width, prev2.content_width, c1.width, c2.width);
        } else {
            // Same line: x = prev.x + c.width + hs, y = prev.y, lh = max(prev.lh, c.height), cw = max(prev.cw, prev.x + c.width)
            T::axiom_add_congruence_left(prev1.x, prev2.x, c1.width);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                prev2.x, c1.width, c2.width);
            T::axiom_eqv_transitive(prev1.x.add(c1.width), prev2.x.add(c1.width), prev2.x.add(c2.width));
            T::axiom_add_congruence_left(prev1.x.add(c1.width), prev2.x.add(c2.width), hs1);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                prev2.x.add(c2.width), hs1, hs2);
            T::axiom_eqv_transitive(
                prev1.x.add(c1.width).add(hs1), prev2.x.add(c2.width).add(hs1),
                prev2.x.add(c2.width).add(hs2));
            // lh: max(prev.lh, c.height)
            lemma_max_congruence(prev1.line_height, prev2.line_height, c1.height, c2.height);
            // cw: max(prev.cw, prev.x + c.width) — reuse prev.x + c.width eqv from above
            lemma_max_congruence(prev1.content_width, prev2.content_width,
                prev1.x.add(c1.width), prev2.x.add(c2.width));
        }
    }
}

/// wrap_layout size congruence.
pub proof fn lemma_wrap_layout_size_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    pad1: Padding<T>, pad2: Padding<T>,
    hs1: T, hs2: T, vs1: T, vs2: T,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
)
    requires limits_eqv(lim1, lim2), padding_eqv(pad1, pad2),
        hs1.eqv(hs2), vs1.eqv(vs2), sizes_eqv(s1, s2),
    ensures
        size_eqv(
            crate::layout::wrap::wrap_layout(lim1, pad1, hs1, vs1, s1).size,
            crate::layout::wrap::wrap_layout(lim2, pad2, hs2, vs2, s2).size),
{
    reveal(crate::layout::wrap::wrap_layout);
    lemma_padding_horizontal_congruence(pad1, pad2);
    lemma_sub_congruence(lim1.max.width, lim2.max.width, pad1.horizontal(), pad2.horizontal());
    let aw1 = lim1.max.width.sub(pad1.horizontal());
    let aw2 = lim2.max.width.sub(pad2.horizontal());
    // wrap_content_size uses wrap_cursor at n
    if s1.len() == 0 {
        T::axiom_eqv_reflexive(T::zero());
        let z = Size::new(T::zero(), T::zero());
        lemma_padding_vertical_congruence(pad1, pad2);
        T::axiom_add_congruence_left(pad1.horizontal(), pad2.horizontal(), T::zero());
        T::axiom_add_congruence_left(pad1.vertical(), pad2.vertical(), T::zero());
        lemma_resolve_congruence(lim1, lim2,
            Size::new(pad1.horizontal().add(T::zero()), pad1.vertical().add(T::zero())),
            Size::new(pad2.horizontal().add(T::zero()), pad2.vertical().add(T::zero())));
    } else {
        lemma_wrap_cursor_congruence(s1, s2, hs1, hs2, vs1, vs2, aw1, aw2, s1.len() as nat);
        let cur1 = crate::layout::wrap::wrap_cursor(s1, hs1, vs1, aw1, s1.len() as nat);
        let cur2 = crate::layout::wrap::wrap_cursor(s2, hs2, vs2, aw2, s2.len() as nat);
        // content.width = cursor.content_width (eqv)
        // content.height = cursor.y + cursor.line_height (eqv)
        T::axiom_add_congruence_left(cur1.y, cur2.y, cur1.line_height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            cur2.y, cur1.line_height, cur2.line_height);
        T::axiom_eqv_transitive(
            cur1.y.add(cur1.line_height), cur2.y.add(cur1.line_height),
            cur2.y.add(cur2.line_height));
        // total_width = pad.horizontal() + content.width, total_height = pad.vertical() + content.height
        lemma_padding_vertical_congruence(pad1, pad2);
        T::axiom_add_congruence_left(pad1.horizontal(), pad2.horizontal(), cur1.content_width);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            pad2.horizontal(), cur1.content_width, cur2.content_width);
        T::axiom_eqv_transitive(
            pad1.horizontal().add(cur1.content_width),
            pad2.horizontal().add(cur1.content_width),
            pad2.horizontal().add(cur2.content_width));
        T::axiom_add_congruence_left(pad1.vertical(), pad2.vertical(), cur1.y.add(cur1.line_height));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            pad2.vertical(), cur1.y.add(cur1.line_height), cur2.y.add(cur2.line_height));
        T::axiom_eqv_transitive(
            pad1.vertical().add(cur1.y.add(cur1.line_height)),
            pad2.vertical().add(cur1.y.add(cur1.line_height)),
            pad2.vertical().add(cur2.y.add(cur2.line_height)));
        lemma_resolve_congruence(lim1, lim2,
            Size::new(
                pad1.horizontal().add(cur1.content_width),
                pad1.vertical().add(cur1.y.add(cur1.line_height))),
            Size::new(
                pad2.horizontal().add(cur2.content_width),
                pad2.vertical().add(cur2.y.add(cur2.line_height))));
    }
}

/// Bridge: layout_widget for Wrap produces size == wrap_layout size.
proof fn lemma_layout_widget_wrap_size_bridge<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, hs: T, vs: T,
    children: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures ({
        let inner = lim.shrink(pad.horizontal(), pad.vertical());
        let cs = Seq::new(children.len(), |i: int|
            layout_widget(inner, children[i], (fuel - 1) as nat).size);
        layout_widget(lim, Widget::Container(ContainerWidget::Wrap {
            padding: pad, h_spacing: hs, v_spacing: vs, children,
        }), fuel).size == crate::layout::wrap::wrap_layout(lim, pad, hs, vs, cs).size
    }),
{
    reveal(crate::layout::wrap::wrap_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let cs = Seq::new(children.len(), |i: int|
        layout_widget(inner, children[i], (fuel - 1) as nat).size);
    let wrp = ContainerWidget::Wrap {
        padding: pad, h_spacing: hs, v_spacing: vs, children,
    };
    let w = Widget::Container(wrp);
    assert(layout_widget(lim, w, fuel) == layout_container(lim, wrp, fuel));
    assert(layout_container(lim, wrp, fuel)
        == layout_wrap_body(lim, pad, hs, vs, cn));
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    assert(child_sizes =~= cs);
}

/// max_width respects eqv.
pub proof fn lemma_max_width_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>, count: nat,
)
    requires sizes_eqv(s1, s2), count <= s1.len(),
    ensures crate::layout::stack::max_width(s1, count)
        .eqv(crate::layout::stack::max_width(s2, count)),
    decreases count,
{
    reveal(crate::layout::stack::max_width);
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_max_width_congruence(s1, s2, (count - 1) as nat);
        lemma_max_congruence(
            crate::layout::stack::max_width(s1, (count - 1) as nat),
            crate::layout::stack::max_width(s2, (count - 1) as nat),
            s1[(count - 1) as int].width,
            s2[(count - 1) as int].width);
    }
}

/// max_height respects eqv.
pub proof fn lemma_max_height_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>, count: nat,
)
    requires sizes_eqv(s1, s2), count <= s1.len(),
    ensures crate::layout::stack::max_height(s1, count)
        .eqv(crate::layout::stack::max_height(s2, count)),
    decreases count,
{
    reveal(crate::layout::stack::max_height);
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_max_height_congruence(s1, s2, (count - 1) as nat);
        lemma_max_congruence(
            crate::layout::stack::max_height(s1, (count - 1) as nat),
            crate::layout::stack::max_height(s2, (count - 1) as nat),
            s1[(count - 1) as int].height,
            s2[(count - 1) as int].height);
    }
}

/// stack_layout size congruence.
pub proof fn lemma_stack_layout_size_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    pad1: Padding<T>, pad2: Padding<T>,
    ha: Alignment, va: Alignment,
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
)
    requires limits_eqv(lim1, lim2), padding_eqv(pad1, pad2), sizes_eqv(s1, s2),
    ensures
        size_eqv(
            crate::layout::stack::stack_layout(lim1, pad1, ha, va, s1).size,
            crate::layout::stack::stack_layout(lim2, pad2, ha, va, s2).size,
        ),
{
    reveal(crate::layout::stack::stack_layout);
    reveal(crate::layout::stack::stack_content_size);
    lemma_max_width_congruence(s1, s2, s1.len() as nat);
    lemma_max_height_congruence(s1, s2, s1.len() as nat);
    lemma_padding_horizontal_congruence(pad1, pad2);
    lemma_padding_vertical_congruence(pad1, pad2);
    // total_width = pad.horizontal() + content.width
    T::axiom_add_congruence_left(
        pad1.horizontal(), pad2.horizontal(),
        crate::layout::stack::max_width(s1, s1.len() as nat));
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        pad2.horizontal(),
        crate::layout::stack::max_width(s1, s1.len() as nat),
        crate::layout::stack::max_width(s2, s2.len() as nat));
    T::axiom_eqv_transitive(
        pad1.horizontal().add(crate::layout::stack::max_width(s1, s1.len() as nat)),
        pad2.horizontal().add(crate::layout::stack::max_width(s1, s1.len() as nat)),
        pad2.horizontal().add(crate::layout::stack::max_width(s2, s2.len() as nat)));
    // total_height = pad.vertical() + content.height
    T::axiom_add_congruence_left(
        pad1.vertical(), pad2.vertical(),
        crate::layout::stack::max_height(s1, s1.len() as nat));
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        pad2.vertical(),
        crate::layout::stack::max_height(s1, s1.len() as nat),
        crate::layout::stack::max_height(s2, s2.len() as nat));
    T::axiom_eqv_transitive(
        pad1.vertical().add(crate::layout::stack::max_height(s1, s1.len() as nat)),
        pad2.vertical().add(crate::layout::stack::max_height(s1, s1.len() as nat)),
        pad2.vertical().add(crate::layout::stack::max_height(s2, s2.len() as nat)));
    lemma_resolve_congruence(lim1, lim2,
        Size::new(
            pad1.horizontal().add(crate::layout::stack::max_width(s1, s1.len() as nat)),
            pad1.vertical().add(crate::layout::stack::max_height(s1, s1.len() as nat))),
        Size::new(
            pad2.horizontal().add(crate::layout::stack::max_width(s2, s2.len() as nat)),
            pad2.vertical().add(crate::layout::stack::max_height(s2, s2.len() as nat))));
}

/// Bridge: layout_widget for Stack produces size == stack_layout size.
proof fn lemma_layout_widget_stack_size_bridge<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, ha: Alignment, va: Alignment,
    children: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures ({
        let inner = lim.shrink(pad.horizontal(), pad.vertical());
        let cs = Seq::new(children.len(), |i: int|
            layout_widget(inner, children[i], (fuel - 1) as nat).size);
        layout_widget(lim, Widget::Container(ContainerWidget::Stack {
            padding: pad, h_align: ha, v_align: va, children,
        }), fuel).size == crate::layout::stack::stack_layout(lim, pad, ha, va, cs).size
    }),
{
    reveal(crate::layout::stack::stack_layout);
    reveal(crate::layout::stack::stack_content_size);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let cs = Seq::new(children.len(), |i: int|
        layout_widget(inner, children[i], (fuel - 1) as nat).size);
    let stk = ContainerWidget::Stack {
        padding: pad, h_align: ha, v_align: va, children,
    };
    let w = Widget::Container(stk);
    assert(layout_widget(lim, w, fuel) == layout_container(lim, stk, fuel));
    assert(layout_container(lim, stk, fuel)
        == layout_stack_body(lim, pad, ha, va, cn));
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    assert(child_sizes =~= cs);
}

/// Eqv predicate for absolute child_data sequences.
pub open spec fn abs_data_eqv<T: OrderedRing>(
    a: Seq<(T, T, Size<T>)>, b: Seq<(T, T, Size<T>)>,
) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==> {
        &&& a[i].0.eqv(b[i].0)  // x eqv
        &&& a[i].1.eqv(b[i].1)  // y eqv
        &&& size_eqv(a[i].2, b[i].2)  // size eqv
    }
}

/// absolute_max_right respects eqv on child_data.
pub proof fn lemma_absolute_max_right_congruence<T: OrderedRing>(
    d1: Seq<(T, T, Size<T>)>, d2: Seq<(T, T, Size<T>)>, count: nat,
)
    requires abs_data_eqv(d1, d2), count <= d1.len(),
    ensures crate::layout::absolute::absolute_max_right(d1, count)
        .eqv(crate::layout::absolute::absolute_max_right(d2, count)),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_absolute_max_right_congruence(d1, d2, (count - 1) as nat);
        // x + width eqv for entry count-1
        T::axiom_add_congruence_left(d1[(count-1) as int].0, d2[(count-1) as int].0, d1[(count-1) as int].2.width);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            d2[(count-1) as int].0, d1[(count-1) as int].2.width, d2[(count-1) as int].2.width);
        T::axiom_eqv_transitive(
            d1[(count-1) as int].0.add(d1[(count-1) as int].2.width),
            d2[(count-1) as int].0.add(d1[(count-1) as int].2.width),
            d2[(count-1) as int].0.add(d2[(count-1) as int].2.width));
        lemma_max_congruence(
            crate::layout::absolute::absolute_max_right(d1, (count-1) as nat),
            crate::layout::absolute::absolute_max_right(d2, (count-1) as nat),
            d1[(count-1) as int].0.add(d1[(count-1) as int].2.width),
            d2[(count-1) as int].0.add(d2[(count-1) as int].2.width));
    }
}

/// absolute_max_bottom respects eqv on child_data.
pub proof fn lemma_absolute_max_bottom_congruence<T: OrderedRing>(
    d1: Seq<(T, T, Size<T>)>, d2: Seq<(T, T, Size<T>)>, count: nat,
)
    requires abs_data_eqv(d1, d2), count <= d1.len(),
    ensures crate::layout::absolute::absolute_max_bottom(d1, count)
        .eqv(crate::layout::absolute::absolute_max_bottom(d2, count)),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_absolute_max_bottom_congruence(d1, d2, (count - 1) as nat);
        T::axiom_add_congruence_left(d1[(count-1) as int].1, d2[(count-1) as int].1, d1[(count-1) as int].2.height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            d2[(count-1) as int].1, d1[(count-1) as int].2.height, d2[(count-1) as int].2.height);
        T::axiom_eqv_transitive(
            d1[(count-1) as int].1.add(d1[(count-1) as int].2.height),
            d2[(count-1) as int].1.add(d1[(count-1) as int].2.height),
            d2[(count-1) as int].1.add(d2[(count-1) as int].2.height));
        lemma_max_congruence(
            crate::layout::absolute::absolute_max_bottom(d1, (count-1) as nat),
            crate::layout::absolute::absolute_max_bottom(d2, (count-1) as nat),
            d1[(count-1) as int].1.add(d1[(count-1) as int].2.height),
            d2[(count-1) as int].1.add(d2[(count-1) as int].2.height));
    }
}

/// Bridge: layout_widget for Absolute produces size == absolute_layout size.
proof fn lemma_layout_widget_absolute_size_bridge<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>,
    children: Seq<AbsoluteChild<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures ({
        let inner = lim.shrink(pad.horizontal(), pad.vertical());
        let cd = Seq::new(children.len(), |i: int|
            (children[i].x, children[i].y,
             layout_widget(inner, children[i].child, (fuel - 1) as nat).size));
        layout_widget(lim, Widget::Container(ContainerWidget::Absolute {
            padding: pad, children,
        }), fuel).size == crate::layout::absolute::absolute_layout(lim, pad, cd).size
    }),
{
    reveal(crate::layout::absolute::absolute_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
    let offsets = Seq::new(children.len(), |i: int| (children[i].x, children[i].y));
    let cd = Seq::new(children.len(), |i: int|
        (children[i].x, children[i].y,
         layout_widget(inner, children[i].child, (fuel - 1) as nat).size));
    let abs = ContainerWidget::Absolute { padding: pad, children };
    let w = Widget::Container(abs);
    assert(layout_widget(lim, w, fuel) == layout_container(lim, abs, fuel));
    assert(layout_container(lim, abs, fuel)
        == layout_absolute_body(lim, pad, cn, offsets));
    // layout_absolute_body constructs child_data from cn sizes + offsets
    // then calls absolute_layout. The child_data matches cd.
    let child_data = Seq::new(cn.len(), |i: int| (offsets[i].0, offsets[i].1, cn[i].size));
    assert(child_data =~= cd);
}

/// If two widgets are eqv, layout_widget produces nodes with eqv sizes.
/// This is the master layout congruence theorem.
pub proof fn lemma_layout_widget_size_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(w1, w2, fuel),
    ensures
        size_eqv(
            layout_widget(lim1, w1, fuel).size,
            layout_widget(lim2, w2, fuel).size,
        ),
    decreases fuel, 1nat,
{
    assert(fuel > 0); // widget_eqv(_, _, 0) == false
    match (w1, w2) {
        (Widget::Leaf(l1), Widget::Leaf(l2)) => {
            lemma_layout_leaf_congruence(lim1, lim2, l1, l2);
        },
        // ── Wrappers ──
        (Widget::Wrapper(WrapperWidget::Margin { margin: m1, child: c1 }),
         Widget::Wrapper(WrapperWidget::Margin { margin: m2, child: c2 })) => {
            lemma_padding_horizontal_congruence(m1, m2);
            lemma_padding_vertical_congruence(m1, m2);
            lemma_shrink_congruence(lim1, lim2,
                m1.horizontal(), m2.horizontal(), m1.vertical(), m2.vertical());
            lemma_layout_widget_size_congruence(
                lim1.shrink(m1.horizontal(), m1.vertical()),
                lim2.shrink(m2.horizontal(), m2.vertical()),
                *c1, *c2, (fuel - 1) as nat);
            let cs1 = layout_widget(lim1.shrink(m1.horizontal(), m1.vertical()), *c1, (fuel - 1) as nat).size;
            let cs2 = layout_widget(lim2.shrink(m2.horizontal(), m2.vertical()), *c2, (fuel - 1) as nat).size;
            T::axiom_add_congruence_left(m1.horizontal(), m2.horizontal(), cs1.width);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                m2.horizontal(), cs1.width, cs2.width);
            T::axiom_eqv_transitive(
                m1.horizontal().add(cs1.width), m2.horizontal().add(cs1.width),
                m2.horizontal().add(cs2.width));
            T::axiom_add_congruence_left(m1.vertical(), m2.vertical(), cs1.height);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                m2.vertical(), cs1.height, cs2.height);
            T::axiom_eqv_transitive(
                m1.vertical().add(cs1.height), m2.vertical().add(cs1.height),
                m2.vertical().add(cs2.height));
            lemma_resolve_congruence(lim1, lim2,
                Size::new(m1.horizontal().add(cs1.width), m1.vertical().add(cs1.height)),
                Size::new(m2.horizontal().add(cs2.width), m2.vertical().add(cs2.height)));
        },
        (Widget::Wrapper(WrapperWidget::Conditional { visible: v1, child: c1 }),
         Widget::Wrapper(WrapperWidget::Conditional { visible: v2, child: c2 })) => {
            if v1 {
                lemma_layout_widget_size_congruence(lim1, lim2, *c1, *c2, (fuel - 1) as nat);
                lemma_resolve_congruence(lim1, lim2,
                    layout_widget(lim1, *c1, (fuel - 1) as nat).size,
                    layout_widget(lim2, *c2, (fuel - 1) as nat).size);
            } else {
                T::axiom_eqv_reflexive(T::zero());
                lemma_resolve_congruence(lim1, lim2, Size::zero_size(), Size::zero_size());
            }
        },
        (Widget::Wrapper(WrapperWidget::ScrollView { viewport: v1, child: c1, .. }),
         Widget::Wrapper(WrapperWidget::ScrollView { viewport: v2, child: c2, .. })) => {
            lemma_resolve_congruence(lim1, lim2, v1, v2);
        },
        (Widget::Wrapper(WrapperWidget::SizedBox { inner_limits: il1, child: c1 }),
         Widget::Wrapper(WrapperWidget::SizedBox { inner_limits: il2, child: c2 })) => {
            // intersect uses max/min which we've proved congruent
            lemma_max_congruence(lim1.min.width, lim2.min.width, il1.min.width, il2.min.width);
            lemma_max_congruence(lim1.min.height, lim2.min.height, il1.min.height, il2.min.height);
            lemma_min_congruence(lim1.max.width, lim2.max.width, il1.max.width, il2.max.width);
            lemma_min_congruence(lim1.max.height, lim2.max.height, il1.max.height, il2.max.height);
            let nmw1 = max::<T>(lim1.min.width, il1.min.width);
            let nmw2 = max::<T>(lim2.min.width, il2.min.width);
            let nmh1 = max::<T>(lim1.min.height, il1.min.height);
            let nmh2 = max::<T>(lim2.min.height, il2.min.height);
            lemma_max_congruence(nmw1, nmw2,
                min::<T>(lim1.max.width, il1.max.width),
                min::<T>(lim2.max.width, il2.max.width));
            lemma_max_congruence(nmh1, nmh2,
                min::<T>(lim1.max.height, il1.max.height),
                min::<T>(lim2.max.height, il2.max.height));
            let eff1 = lim1.intersect(il1);
            let eff2 = lim2.intersect(il2);
            assert(limits_eqv(eff1, eff2));
            lemma_layout_widget_size_congruence(eff1, eff2, *c1, *c2, (fuel - 1) as nat);
            lemma_resolve_congruence(lim1, lim2,
                layout_widget(eff1, *c1, (fuel - 1) as nat).size,
                layout_widget(eff2, *c2, (fuel - 1) as nat).size);
        },
        (Widget::Wrapper(WrapperWidget::AspectRatio { ratio: r1, child: c1 }),
         Widget::Wrapper(WrapperWidget::AspectRatio { ratio: r2, child: c2 })) => {
            // h1 = max.width / ratio, h2 = max.width / ratio (eqv)
            // widget_eqv guarantees r1.eqv(r2) && !r1.eqv(T::zero())
            verus_algebra::quadratic::lemma_div_congruence::<T>(
                lim1.max.width, lim2.max.width, r1, r2);
            let h1 = lim1.max.width.div(r1);
            let h2 = lim2.max.width.div(r2);
            // h1 eqv h2. Branch on h1.le(max.height):
            // le_congruence: h1 eqv h2 && max.height1 eqv max.height2 && h1.le(mh1) → h2.le(mh2)
            T::axiom_le_total(h1, lim1.max.height);
            if h1.le(lim1.max.height) {
                // h2 ≤ max.height2 by le_congruence
                T::axiom_le_congruence(h1, h2, lim1.max.height, lim2.max.height);
                // Effective limits: { min, max: (w, h1/h2) }
                let eff1 = Limits { min: lim1.min, max: Size::new(lim1.max.width, h1) };
                let eff2 = Limits { min: lim2.min, max: Size::new(lim2.max.width, h2) };
                assert(limits_eqv(eff1, eff2));
                lemma_layout_widget_size_congruence(eff1, eff2, *c1, *c2, (fuel - 1) as nat);
                lemma_resolve_congruence(lim1, lim2,
                    layout_widget(eff1, *c1, (fuel - 1) as nat).size,
                    layout_widget(eff2, *c2, (fuel - 1) as nat).size);
            } else {
                // ¬(h1 ≤ max.height1). Need ¬(h2 ≤ max.height2) for same branch.
                // If h2.le(max.height2) were true, then le_congruence(h2,h1,mh2,mh1) → h1.le(mh1), contradiction.
                T::axiom_eqv_symmetric(h1, h2);
                T::axiom_eqv_symmetric(lim1.max.height, lim2.max.height);
                if h2.le(lim2.max.height) {
                    T::axiom_le_congruence(h2, h1, lim2.max.height, lim1.max.height);
                    // h1 ≤ mh1 — contradicts ¬(h1 ≤ mh1)
                    assert(false);
                }
                // w2 = max.height * ratio
                verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence_right::<T>(
                    lim1.max.height, r1, r2);
                T::axiom_mul_congruence_left(lim1.max.height, lim2.max.height, r2);
                T::axiom_eqv_transitive(
                    lim1.max.height.mul(r1), lim1.max.height.mul(r2),
                    lim2.max.height.mul(r2));
                let eff1 = Limits { min: lim1.min, max: Size::new(lim1.max.height.mul(r1), lim1.max.height) };
                let eff2 = Limits { min: lim2.min, max: Size::new(lim2.max.height.mul(r2), lim2.max.height) };
                assert(limits_eqv(eff1, eff2));
                lemma_layout_widget_size_congruence(eff1, eff2, *c1, *c2, (fuel - 1) as nat);
                lemma_resolve_congruence(lim1, lim2,
                    layout_widget(eff1, *c1, (fuel - 1) as nat).size,
                    layout_widget(eff2, *c2, (fuel - 1) as nat).size);
            }
        },
        // ── Containers ──
        (Widget::Container(ContainerWidget::Column { padding: p1, spacing: sp1, alignment: al, children: ch1 }),
         Widget::Container(ContainerWidget::Column { padding: p2, spacing: sp2, alignment: _, children: ch2 })) => {
            // Setup: compute eqv inner limits
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            lemma_shrink_congruence(lim1, lim2,
                p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
            let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
            let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());

            // Child sizes eqv by recursive IH (scoped)
            assert forall|i: int| 0 <= i < ch1.len() implies
                size_eqv(
                    layout_widget(inner1, ch1[i], (fuel - 1) as nat).size,
                    layout_widget(inner2, ch2[i], (fuel - 1) as nat).size,
                )
            by {
                lemma_layout_widget_size_congruence(
                    inner1, inner2, ch1[i], ch2[i], (fuel - 1) as nat);
            }
            let cs1 = Seq::new(ch1.len(), |i: int|
                layout_widget(inner1, ch1[i], (fuel - 1) as nat).size);
            let cs2 = Seq::new(ch2.len(), |i: int|
                layout_widget(inner2, ch2[i], (fuel - 1) as nat).size);
            assert(sizes_eqv(cs1, cs2));

            // Bridge: layout_widget.size == column_layout.size (focused lemma)
            lemma_layout_widget_column_size_bridge(lim1, p1, sp1, al, ch1, fuel);
            lemma_layout_widget_column_size_bridge(lim2, p2, sp2, al, ch2, fuel);
            // Column layout size congruence (already proved)
            lemma_column_layout_size_congruence(lim1, lim2, p1, p2, sp1, sp2, al, cs1, cs2);
        },
        // Row: same pattern as Column via row bridge
        (Widget::Container(ContainerWidget::Row { padding: p1, spacing: sp1, alignment: al, children: ch1 }),
         Widget::Container(ContainerWidget::Row { padding: p2, spacing: sp2, alignment: _, children: ch2 })) => {
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            lemma_shrink_congruence(lim1, lim2,
                p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
            let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
            let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
            assert forall|i: int| 0 <= i < ch1.len() implies
                size_eqv(
                    layout_widget(inner1, ch1[i], (fuel - 1) as nat).size,
                    layout_widget(inner2, ch2[i], (fuel - 1) as nat).size,
                )
            by {
                lemma_layout_widget_size_congruence(
                    inner1, inner2, ch1[i], ch2[i], (fuel - 1) as nat);
            }
            let cs1 = Seq::new(ch1.len(), |i: int|
                layout_widget(inner1, ch1[i], (fuel - 1) as nat).size);
            let cs2 = Seq::new(ch2.len(), |i: int|
                layout_widget(inner2, ch2[i], (fuel - 1) as nat).size);
            assert(sizes_eqv(cs1, cs2));
            lemma_layout_widget_row_size_bridge(lim1, p1, sp1, al, ch1, fuel);
            lemma_layout_widget_row_size_bridge(lim2, p2, sp2, al, ch2, fuel);
            lemma_row_layout_size_congruence(lim1, lim2, p1, p2, sp1, sp2, al, cs1, cs2);
        },
        // Stack: same pattern via stack bridge
        (Widget::Container(ContainerWidget::Stack { padding: p1, h_align: ha, v_align: va, children: ch1 }),
         Widget::Container(ContainerWidget::Stack { padding: p2, h_align: _, v_align: _, children: ch2 })) => {
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            lemma_shrink_congruence(lim1, lim2,
                p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
            let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
            let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
            assert forall|i: int| 0 <= i < ch1.len() implies
                size_eqv(
                    layout_widget(inner1, ch1[i], (fuel - 1) as nat).size,
                    layout_widget(inner2, ch2[i], (fuel - 1) as nat).size,
                )
            by {
                lemma_layout_widget_size_congruence(
                    inner1, inner2, ch1[i], ch2[i], (fuel - 1) as nat);
            }
            let cs1 = Seq::new(ch1.len(), |i: int|
                layout_widget(inner1, ch1[i], (fuel - 1) as nat).size);
            let cs2 = Seq::new(ch2.len(), |i: int|
                layout_widget(inner2, ch2[i], (fuel - 1) as nat).size);
            assert(sizes_eqv(cs1, cs2));
            lemma_layout_widget_stack_size_bridge(lim1, p1, ha, va, ch1, fuel);
            lemma_layout_widget_stack_size_bridge(lim2, p2, ha, va, ch2, fuel);
            lemma_stack_layout_size_congruence(lim1, lim2, p1, p2, ha, va, cs1, cs2);
        },
        // Wrap: via wrap bridge
        (Widget::Container(ContainerWidget::Wrap { padding: p1, h_spacing: hs1, v_spacing: vs1, children: ch1 }),
         Widget::Container(ContainerWidget::Wrap { padding: p2, h_spacing: hs2, v_spacing: vs2, children: ch2 })) => {
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            lemma_shrink_congruence(lim1, lim2,
                p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
            let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
            let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
            assert forall|i: int| 0 <= i < ch1.len() implies
                size_eqv(
                    layout_widget(inner1, ch1[i], (fuel - 1) as nat).size,
                    layout_widget(inner2, ch2[i], (fuel - 1) as nat).size,
                )
            by {
                lemma_layout_widget_size_congruence(
                    inner1, inner2, ch1[i], ch2[i], (fuel - 1) as nat);
            }
            let cs1 = Seq::new(ch1.len(), |i: int|
                layout_widget(inner1, ch1[i], (fuel - 1) as nat).size);
            let cs2 = Seq::new(ch2.len(), |i: int|
                layout_widget(inner2, ch2[i], (fuel - 1) as nat).size);
            assert(sizes_eqv(cs1, cs2));
            lemma_layout_widget_wrap_size_bridge(lim1, p1, hs1, vs1, ch1, fuel);
            lemma_layout_widget_wrap_size_bridge(lim2, p2, hs2, vs2, ch2, fuel);
            lemma_wrap_layout_size_congruence(lim1, lim2, p1, p2, hs1, hs2, vs1, vs2, cs1, cs2);
        },
        // ListView: size = resolve(viewport), which is trivially congruent
        (Widget::Container(ContainerWidget::ListView { viewport: v1, children: ch1, .. }),
         Widget::Container(ContainerWidget::ListView { viewport: v2, children: ch2, .. })) => {
            reveal(crate::layout::listview::layout_listview_body);
            lemma_resolve_congruence(lim1, lim2, v1, v2);
        },
        // Flex: parent_size = resolve(limits.max) — trivially congruent
        (Widget::Container(ContainerWidget::Flex { padding: p1, children: ch1, .. }),
         Widget::Container(ContainerWidget::Flex { padding: p2, children: ch2, .. })) => {
            // Flex size is always resolve(limits.max), regardless of children
            reveal(crate::layout::flex::flex_column_layout);
            reveal(crate::layout::flex::flex_row_layout);
            lemma_resolve_congruence(lim1, lim2, lim1.max, lim2.max);
        },
        // Grid: content size from col_widths/row_heights sums
        (Widget::Container(ContainerWidget::Grid {
            padding: p1, h_spacing: hs1, v_spacing: vs1, col_widths: cw1, row_heights: rh1, children: ch1, ..
        }),
         Widget::Container(ContainerWidget::Grid {
            padding: p2, h_spacing: hs2, v_spacing: vs2, col_widths: cw2, row_heights: rh2, children: ch2, ..
        })) => {
            reveal(crate::layout::grid::grid_layout);
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            // grid_content_width = sum_widths(col_widths, n) + repeated_add(h_spacing, n-1)
            lemma_sum_main_congruence(cw1, cw2, Axis::Horizontal, cw1.len() as nat);
            lemma_sum_main_eq_sum_widths(cw1, cw1.len() as nat);
            lemma_sum_main_eq_sum_widths(cw2, cw2.len() as nat);
            lemma_repeated_add_congruence(hs1, hs2,
                if cw1.len() > 0 { (cw1.len() - 1) as nat } else { 0 });
            // grid_content_height = sum_heights(row_heights, n) + repeated_add(v_spacing, n-1)
            lemma_sum_heights_congruence(rh1, rh2, rh1.len() as nat);
            lemma_repeated_add_congruence(vs1, vs2,
                if rh1.len() > 0 { (rh1.len() - 1) as nat } else { 0 });
            // Chain content_w eqv
            if cw1.len() == 0 {
                T::axiom_eqv_reflexive(T::zero());
            } else {
                T::axiom_add_congruence_left(
                    sum_widths(cw1, cw1.len() as nat), sum_widths(cw2, cw2.len() as nat),
                    repeated_add(hs1, (cw1.len() - 1) as nat));
                verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                    sum_widths(cw2, cw2.len() as nat),
                    repeated_add(hs1, (cw1.len() - 1) as nat),
                    repeated_add(hs2, (cw2.len() - 1) as nat));
                T::axiom_eqv_transitive(
                    crate::layout::grid::grid_content_width(cw1, hs1),
                    sum_widths(cw2, cw2.len() as nat).add(repeated_add(hs1, (cw1.len() - 1) as nat)),
                    crate::layout::grid::grid_content_width(cw2, hs2));
            }
            // Chain content_h eqv
            if rh1.len() == 0 {
                T::axiom_eqv_reflexive(T::zero());
            } else {
                T::axiom_add_congruence_left(
                    sum_heights(rh1, rh1.len() as nat), sum_heights(rh2, rh2.len() as nat),
                    repeated_add(vs1, (rh1.len() - 1) as nat));
                verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                    sum_heights(rh2, rh2.len() as nat),
                    repeated_add(vs1, (rh1.len() - 1) as nat),
                    repeated_add(vs2, (rh2.len() - 1) as nat));
                T::axiom_eqv_transitive(
                    crate::layout::grid::grid_content_height(rh1, vs1),
                    sum_heights(rh2, rh2.len() as nat).add(repeated_add(vs1, (rh1.len() - 1) as nat)),
                    crate::layout::grid::grid_content_height(rh2, vs2));
            }
            // total = padding + content → resolve
            let cw_1 = crate::layout::grid::grid_content_width(cw1, hs1);
            let cw_2 = crate::layout::grid::grid_content_width(cw2, hs2);
            let ch_1 = crate::layout::grid::grid_content_height(rh1, vs1);
            let ch_2 = crate::layout::grid::grid_content_height(rh2, vs2);
            T::axiom_add_congruence_left(p1.horizontal(), p2.horizontal(), cw_1);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                p2.horizontal(), cw_1, cw_2);
            T::axiom_eqv_transitive(
                p1.horizontal().add(cw_1), p2.horizontal().add(cw_1), p2.horizontal().add(cw_2));
            T::axiom_add_congruence_left(p1.vertical(), p2.vertical(), ch_1);
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                p2.vertical(), ch_1, ch_2);
            T::axiom_eqv_transitive(
                p1.vertical().add(ch_1), p2.vertical().add(ch_1), p2.vertical().add(ch_2));
            lemma_resolve_congruence(lim1, lim2,
                Size::new(p1.horizontal().add(cw_1), p1.vertical().add(ch_1)),
                Size::new(p2.horizontal().add(cw_2), p2.vertical().add(ch_2)));
        },
        // Absolute: content size from max of (offset + child_size)
        (Widget::Container(ContainerWidget::Absolute { padding: p1, children: ch1 }),
         Widget::Container(ContainerWidget::Absolute { padding: p2, children: ch2 })) => {
            // Use bridge to connect layout_widget.size to absolute_layout.size
            lemma_layout_widget_absolute_size_bridge(lim1, p1, ch1, fuel);
            lemma_layout_widget_absolute_size_bridge(lim2, p2, ch2, fuel);
            reveal(crate::layout::absolute::absolute_layout);
            reveal(crate::layout::absolute::absolute_content_size);
            lemma_padding_horizontal_congruence(p1, p2);
            lemma_padding_vertical_congruence(p1, p2);
            lemma_shrink_congruence(lim1, lim2,
                p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
            let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
            let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
            // Build child_data with eqv entries
            assert forall|i: int| 0 <= i < ch1.len() implies
                size_eqv(
                    layout_widget(inner1, ch1[i].child, (fuel - 1) as nat).size,
                    layout_widget(inner2, ch2[i].child, (fuel - 1) as nat).size,
                )
            by {
                lemma_layout_widget_size_congruence(
                    inner1, inner2, ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            }
            // Build eqv child_data
            let d1 = Seq::new(ch1.len(), |i: int|
                (ch1[i].x, ch1[i].y, layout_widget(inner1, ch1[i].child, (fuel - 1) as nat).size));
            let d2 = Seq::new(ch2.len(), |i: int|
                (ch2[i].x, ch2[i].y, layout_widget(inner2, ch2[i].child, (fuel - 1) as nat).size));
            assert(abs_data_eqv(d1, d2));
            // content size eqv
            lemma_absolute_max_right_congruence(d1, d2, d1.len() as nat);
            lemma_absolute_max_bottom_congruence(d1, d2, d1.len() as nat);
            // total = padding + content
            T::axiom_add_congruence_left(p1.horizontal(), p2.horizontal(),
                crate::layout::absolute::absolute_max_right(d1, d1.len() as nat));
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                p2.horizontal(),
                crate::layout::absolute::absolute_max_right(d1, d1.len() as nat),
                crate::layout::absolute::absolute_max_right(d2, d2.len() as nat));
            T::axiom_eqv_transitive(
                p1.horizontal().add(crate::layout::absolute::absolute_max_right(d1, d1.len() as nat)),
                p2.horizontal().add(crate::layout::absolute::absolute_max_right(d1, d1.len() as nat)),
                p2.horizontal().add(crate::layout::absolute::absolute_max_right(d2, d2.len() as nat)));
            T::axiom_add_congruence_left(p1.vertical(), p2.vertical(),
                crate::layout::absolute::absolute_max_bottom(d1, d1.len() as nat));
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
                p2.vertical(),
                crate::layout::absolute::absolute_max_bottom(d1, d1.len() as nat),
                crate::layout::absolute::absolute_max_bottom(d2, d2.len() as nat));
            T::axiom_eqv_transitive(
                p1.vertical().add(crate::layout::absolute::absolute_max_bottom(d1, d1.len() as nat)),
                p2.vertical().add(crate::layout::absolute::absolute_max_bottom(d1, d1.len() as nat)),
                p2.vertical().add(crate::layout::absolute::absolute_max_bottom(d2, d2.len() as nat)));
            lemma_resolve_congruence(lim1, lim2,
                Size::new(
                    p1.horizontal().add(crate::layout::absolute::absolute_max_right(d1, d1.len() as nat)),
                    p1.vertical().add(crate::layout::absolute::absolute_max_bottom(d1, d1.len() as nat))),
                Size::new(
                    p2.horizontal().add(crate::layout::absolute::absolute_max_right(d2, d2.len() as nat)),
                    p2.vertical().add(crate::layout::absolute::absolute_max_bottom(d2, d2.len() as nat))));
        },
        // Cross-variant mismatches: widget_eqv returns false → vacuously true
        _ => {},
    }
}

// ══════════════════════════════════════════════════════════════════════
// Full node congruence (x, y, size, children.len())
// ══════════════════════════════════════════════════════════════════════

/// layout_widget always produces x = T::zero() and y = T::zero() at the top level.
pub proof fn lemma_layout_widget_xy_zero<T: OrderedField>(
    lim: Limits<T>, w: Widget<T>, fuel: nat,
)
    ensures
        layout_widget(lim, w, fuel).x == T::zero(),
        layout_widget(lim, w, fuel).y == T::zero(),
{
    // All layout functions construct Node { x: T::zero(), y: T::zero(), ... }
    // This follows from unfolding layout_widget → layout_leaf/wrapper/container
    // Each returns Node { x: T::zero(), y: T::zero(), ... }
    if fuel == 0 {
        // Base case: Node { x: T::zero(), ... }
    } else {
        match w {
            Widget::Leaf(_) => {},
            Widget::Wrapper(wrapper) => match wrapper {
                WrapperWidget::Conditional { visible, child } => {
                    if visible {} else {}
                },
                _ => {},
            },
            Widget::Container(container) => match container {
                ContainerWidget::Column { .. } => { reveal(linear_layout); },
                ContainerWidget::Row { .. } => { reveal(linear_layout); },
                ContainerWidget::Stack { .. } => {
                    reveal(crate::layout::stack::stack_layout);
                },
                ContainerWidget::Wrap { .. } => {
                    reveal(crate::layout::wrap::wrap_layout);
                },
                ContainerWidget::Flex { direction, .. } => match direction {
                    FlexDirection::Column => { reveal(crate::layout::flex::flex_column_layout); },
                    FlexDirection::Row => { reveal(crate::layout::flex::flex_row_layout); },
                },
                ContainerWidget::Grid { .. } => {
                    reveal(crate::layout::grid::grid_layout);
                },
                ContainerWidget::Absolute { .. } => {
                    reveal(crate::layout::absolute::absolute_layout);
                },
                ContainerWidget::ListView { .. } => {
                    reveal(crate::layout::listview::layout_listview_body);
                },
            },
        }
    }
}

/// Helper: get widget children count (structural, no layout needed).
pub open spec fn widget_children_count<T: OrderedField>(w: Widget<T>) -> nat {
    match w {
        Widget::Leaf(_) => 0,
        Widget::Wrapper(WrapperWidget::Conditional { visible: false, .. }) => 0,
        Widget::Wrapper(_) => 1,
        Widget::Container(c) => match c {
            ContainerWidget::Column { children, .. } => children.len(),
            ContainerWidget::Row { children, .. } => children.len(),
            ContainerWidget::Stack { children, .. } => children.len(),
            ContainerWidget::Wrap { children, .. } => children.len(),
            ContainerWidget::Flex { children, .. } => children.len(),
            ContainerWidget::Grid { children, .. } => children.len(),
            ContainerWidget::Absolute { children, .. } => children.len(),
            ContainerWidget::ListView { children, .. } => children.len(),
        },
    }
}

// ══════════════════════════════════════════════════════════════════════
// ListView visible range congruence
// ══════════════════════════════════════════════════════════════════════

/// listview_child_y respects eqv on sizes and spacing.
pub proof fn lemma_listview_child_y_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    sp1: T, sp2: T, i: nat,
)
    requires sizes_eqv(s1, s2), sp1.eqv(sp2), i <= s1.len(),
    ensures
        crate::layout::listview::listview_child_y(s1, sp1, i)
            .eqv(crate::layout::listview::listview_child_y(s2, sp2, i)),
    decreases i,
{
    use crate::layout::listview::listview_child_y;
    if i == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        lemma_listview_child_y_congruence(s1, s2, sp1, sp2, (i - 1) as nat);
        let y1 = listview_child_y(s1, sp1, (i - 1) as nat);
        let y2 = listview_child_y(s2, sp2, (i - 1) as nat);
        T::axiom_add_congruence_left(y1, y2, s1[(i-1) as int].height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            y2, s1[(i-1) as int].height, s2[(i-1) as int].height);
        T::axiom_eqv_transitive(y1.add(s1[(i-1) as int].height), y2.add(s1[(i-1) as int].height),
            y2.add(s2[(i-1) as int].height));
        T::axiom_add_congruence_left(y1.add(s1[(i-1) as int].height), y2.add(s2[(i-1) as int].height), sp1);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            y2.add(s2[(i-1) as int].height), sp1, sp2);
        T::axiom_eqv_transitive(
            y1.add(s1[(i-1) as int].height).add(sp1),
            y2.add(s2[(i-1) as int].height).add(sp1),
            y2.add(s2[(i-1) as int].height).add(sp2));
    }
}

/// listview_first_visible_from produces the same index for eqv inputs.
pub proof fn lemma_listview_first_visible_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    sp1: T, sp2: T,
    sy1: T, sy2: T,
    from: nat,
)
    requires sizes_eqv(s1, s2), sp1.eqv(sp2), sy1.eqv(sy2),
    ensures
        crate::layout::listview::listview_first_visible_from(s1, sp1, sy1, from)
            == crate::layout::listview::listview_first_visible_from(s2, sp2, sy2, from),
    decreases s1.len() - from,
{
    use crate::layout::listview::{listview_first_visible_from, listview_child_bottom, listview_child_y};
    if from >= s1.len() {
    } else {
        // listview_child_bottom(s, sp, from) = child_y(s, sp, from) + s[from].height
        lemma_listview_child_y_congruence(s1, s2, sp1, sp2, from);
        T::axiom_add_congruence_left(
            listview_child_y(s1, sp1, from), listview_child_y(s2, sp2, from),
            s1[from as int].height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
            listview_child_y(s2, sp2, from), s1[from as int].height, s2[from as int].height);
        T::axiom_eqv_transitive(
            listview_child_bottom(s1, sp1, from),
            listview_child_y(s2, sp2, from).add(s1[from as int].height),
            listview_child_bottom(s2, sp2, from));
        // scroll_y.lt(bottom) is the same for eqv scroll_y and eqv bottom
        lemma_le_congruence_iff(sy1, sy2,
            listview_child_bottom(s1, sp1, from), listview_child_bottom(s2, sp2, from));
        // lt(a, b) = !b.le(a), so le_congruence_iff on (bottom, scroll_y) gives lt congruence
        lemma_le_congruence_iff(
            listview_child_bottom(s1, sp1, from), listview_child_bottom(s2, sp2, from),
            sy1, sy2);
        if sy1.lt(listview_child_bottom(s1, sp1, from)) {
            // Both return `from`
        } else {
            // Both recurse
            lemma_listview_first_visible_congruence(s1, s2, sp1, sp2, sy1, sy2, from + 1);
        }
    }
}

/// listview_end_visible_from produces the same index for eqv inputs.
pub proof fn lemma_listview_end_visible_congruence<T: OrderedRing>(
    s1: Seq<Size<T>>, s2: Seq<Size<T>>,
    sp1: T, sp2: T,
    sy1: T, sy2: T,
    vh1: T, vh2: T,
    from: nat,
)
    requires sizes_eqv(s1, s2), sp1.eqv(sp2), sy1.eqv(sy2), vh1.eqv(vh2),
    ensures
        crate::layout::listview::listview_end_visible_from(s1, sp1, sy1, vh1, from)
            == crate::layout::listview::listview_end_visible_from(s2, sp2, sy2, vh2, from),
    decreases s1.len() - from,
{
    use crate::layout::listview::{listview_end_visible_from, listview_child_y};
    if from >= s1.len() {
    } else {
        // scroll_bottom = scroll_y + viewport_h
        T::axiom_add_congruence_left(sy1, sy2, vh1);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(sy2, vh1, vh2);
        T::axiom_eqv_transitive(sy1.add(vh1), sy2.add(vh1), sy2.add(vh2));
        lemma_listview_child_y_congruence(s1, s2, sp1, sp2, from);
        // le_congruence_iff on scroll_bottom vs child_y
        lemma_le_congruence_iff(
            sy1.add(vh1), sy2.add(vh2),
            listview_child_y(s1, sp1, from), listview_child_y(s2, sp2, from));
        if sy1.add(vh1).le(listview_child_y(s1, sp1, from)) {
            // Both return `from`
        } else {
            lemma_listview_end_visible_congruence(s1, s2, sp1, sp2, sy1, sy2, vh1, vh2, from + 1);
        }
    }
}

/// Column layout produces children.len() == ch.len().
proof fn lemma_column_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, sp: T, al: Alignment,
    ch: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Column {
            padding: pad, spacing: sp, alignment: al, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(linear_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, ch, (fuel - 1) as nat);
    let col = ContainerWidget::Column { padding: pad, spacing: sp, alignment: al, children: ch };
    assert(layout_widget(lim, Widget::Container(col), fuel) == layout_container(lim, col, fuel));
    assert(layout_container(lim, col, fuel) == layout_linear_body(lim, pad, sp, al, cn, Axis::Vertical));
}

/// Row layout produces children.len() == ch.len().
proof fn lemma_row_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, sp: T, al: Alignment,
    ch: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Row {
            padding: pad, spacing: sp, alignment: al, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(linear_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = widget_child_nodes(inner, ch, (fuel - 1) as nat);
    let row = ContainerWidget::Row { padding: pad, spacing: sp, alignment: al, children: ch };
    assert(layout_widget(lim, Widget::Container(row), fuel) == layout_container(lim, row, fuel));
    assert(layout_container(lim, row, fuel) == layout_linear_body(lim, pad, sp, al, cn, Axis::Horizontal));
}

/// Stack layout produces children.len() == ch.len().
proof fn lemma_stack_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, ha: Alignment, va: Alignment,
    ch: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Stack {
            padding: pad, h_align: ha, v_align: va, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(crate::layout::stack::stack_layout);
    let cn = widget_child_nodes(lim.shrink(pad.horizontal(), pad.vertical()), ch, (fuel-1) as nat);
    let stk = ContainerWidget::Stack { padding: pad, h_align: ha, v_align: va, children: ch };
    assert(layout_widget(lim, Widget::Container(stk), fuel) == layout_container(lim, stk, fuel));
    assert(layout_container(lim, stk, fuel) == layout_stack_body(lim, pad, ha, va, cn));
}

/// Wrap layout produces children.len() == ch.len().
proof fn lemma_wrap_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, hs: T, vs: T,
    ch: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Wrap {
            padding: pad, h_spacing: hs, v_spacing: vs, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(crate::layout::wrap::wrap_layout);
    let cn = widget_child_nodes(lim.shrink(pad.horizontal(), pad.vertical()), ch, (fuel-1) as nat);
    let wrp = ContainerWidget::Wrap { padding: pad, h_spacing: hs, v_spacing: vs, children: ch };
    assert(layout_widget(lim, Widget::Container(wrp), fuel) == layout_container(lim, wrp, fuel));
    assert(layout_container(lim, wrp, fuel) == layout_wrap_body(lim, pad, hs, vs, cn));
}

/// Absolute layout produces children.len() == ch.len().
proof fn lemma_absolute_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>,
    ch: Seq<AbsoluteChild<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Absolute {
            padding: pad, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(crate::layout::absolute::absolute_layout);
    let inner = lim.shrink(pad.horizontal(), pad.vertical());
    let cn = absolute_widget_child_nodes(inner, ch, (fuel-1) as nat);
    let abs = ContainerWidget::Absolute { padding: pad, children: ch };
    assert(layout_widget(lim, Widget::Container(abs), fuel) == layout_container(lim, abs, fuel));
}

/// Flex layout produces children.len() == ch.len().
proof fn lemma_flex_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, sp: T, al: Alignment, dir: FlexDirection,
    ch: Seq<FlexItem<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Flex {
            padding: pad, spacing: sp, alignment: al, direction: dir, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(crate::layout::flex::flex_column_layout);
    reveal(crate::layout::flex::flex_row_layout);
    let flx = ContainerWidget::Flex { padding: pad, spacing: sp, alignment: al, direction: dir, children: ch };
    assert(layout_widget(lim, Widget::Container(flx), fuel) == layout_container(lim, flx, fuel));
}

/// Grid layout produces children.len() == ch.len().
proof fn lemma_grid_children_count<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, hs: T, vs: T, ha: Alignment, va: Alignment,
    cw: Seq<Size<T>>, rh: Seq<Size<T>>, ch: Seq<Widget<T>>, fuel: nat,
)
    requires fuel > 0,
    ensures
        layout_widget(lim, Widget::Container(ContainerWidget::Grid {
            padding: pad, h_spacing: hs, v_spacing: vs, h_align: ha, v_align: va,
            col_widths: cw, row_heights: rh, children: ch,
        }), fuel).children.len() == ch.len(),
{
    reveal(crate::layout::grid::grid_layout);
    let g = ContainerWidget::Grid { padding: pad, h_spacing: hs, v_spacing: vs,
        h_align: ha, v_align: va, col_widths: cw, row_heights: rh, children: ch };
    assert(layout_widget(lim, Widget::Container(g), fuel) == layout_container(lim, g, fuel));
}

/// Container children.len() equality dispatcher (focused context).
proof fn lemma_container_children_len_eq<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    c1: ContainerWidget<T>, c2: ContainerWidget<T>, fuel: nat,
)
    requires fuel > 0, limits_eqv(lim1, lim2),
        widget_eqv(Widget::Container(c1), Widget::Container(c2), fuel),
    ensures layout_container(lim1, c1, fuel).children.len()
        == layout_container(lim2, c2, fuel).children.len(),
{
    match (c1, c2) {
        (ContainerWidget::Column { padding: p1, spacing: s1, alignment: a, children: ch1 },
         ContainerWidget::Column { padding: p2, spacing: s2, children: ch2, .. }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_column_children_count(lim1, p1, s1, a, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_column_children_count(lim2, p2, s2, a, ch2, fuel); };
        },
        (ContainerWidget::Row { padding: p1, spacing: s1, alignment: a, children: ch1 },
         ContainerWidget::Row { padding: p2, spacing: s2, children: ch2, .. }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_row_children_count(lim1, p1, s1, a, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_row_children_count(lim2, p2, s2, a, ch2, fuel); };
        },
        (ContainerWidget::Stack { padding: p1, h_align: h, v_align: v, children: ch1 },
         ContainerWidget::Stack { padding: p2, children: ch2, .. }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_stack_children_count(lim1, p1, h, v, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_stack_children_count(lim2, p2, h, v, ch2, fuel); };
        },
        (ContainerWidget::Wrap { padding: p1, h_spacing: h1, v_spacing: v1, children: ch1 },
         ContainerWidget::Wrap { padding: p2, h_spacing: h2, v_spacing: v2, children: ch2 }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_wrap_children_count(lim1, p1, h1, v1, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_wrap_children_count(lim2, p2, h2, v2, ch2, fuel); };
        },
        (ContainerWidget::Flex { padding: p1, spacing: s1, alignment: a, direction: d, children: ch1 },
         ContainerWidget::Flex { padding: p2, spacing: s2, children: ch2, .. }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_flex_children_count(lim1, p1, s1, a, d, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_flex_children_count(lim2, p2, s2, a, d, ch2, fuel); };
        },
        (ContainerWidget::Grid { padding: p1, h_spacing: h1, v_spacing: v1,
            h_align: ha, v_align: va, col_widths: w1c, row_heights: r1, children: ch1 },
         ContainerWidget::Grid { padding: p2, h_spacing: h2, v_spacing: v2,
            col_widths: w2c, row_heights: r2, children: ch2, .. }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_grid_children_count(lim1, p1, h1, v1, ha, va, w1c, r1, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_grid_children_count(lim2, p2, h2, v2, ha, va, w2c, r2, ch2, fuel); };
        },
        (ContainerWidget::Absolute { padding: p1, children: ch1 },
         ContainerWidget::Absolute { padding: p2, children: ch2 }) => {
            assert(ch1.len() == ch2.len()); // from widget_eqv
            assert(layout_container(lim1, c1, fuel).children.len() == ch1.len()) by {
                lemma_absolute_children_count(lim1, p1, ch1, fuel); };
            assert(layout_container(lim2, c2, fuel).children.len() == ch2.len()) by {
                lemma_absolute_children_count(lim2, p2, ch2, fuel); };
        },
        _ => {},
    }
}

/// children.len() equality for eqv widgets.
proof fn lemma_layout_widget_children_len_eq<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
)
    requires limits_eqv(lim1, lim2), widget_eqv(w1, w2, fuel),
    ensures layout_widget(lim1, w1, fuel).children.len()
        == layout_widget(lim2, w2, fuel).children.len(),
    decreases fuel, 1nat,
{
    assert(fuel > 0);
    match (w1, w2) {
        (Widget::Leaf(_), Widget::Leaf(_)) => {},
        (Widget::Wrapper(WrapperWidget::Conditional { visible: v1, child: c1 }),
         Widget::Wrapper(WrapperWidget::Conditional { visible: v2, child: c2 })) => {
            if v1 { lemma_layout_widget_children_len_eq(lim1, lim2, *c1, *c2, (fuel-1) as nat); }
        },
        (Widget::Wrapper(_), Widget::Wrapper(_)) => {},
        (Widget::Container(c1), Widget::Container(c2)) => {
            lemma_container_children_len_eq(lim1, lim2, c1, c2, fuel);
        },
        _ => {},
    }
}

/// Full top-level congruence: eqv widgets produce nodes with eqv x, y, size
/// and same children count. (Children's deep eqv follows from recursive application.)
pub proof fn lemma_layout_widget_node_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(w1, w2, fuel),
    ensures
        node_eqv(
            layout_widget(lim1, w1, fuel),
            layout_widget(lim2, w2, fuel),
        ),
    decreases fuel, 1nat,
{
    // Combine the four components of node_eqv (each scoped to minimize context):
    assert(layout_widget(lim1, w1, fuel).x.eqv(layout_widget(lim2, w2, fuel).x)) by {
        lemma_layout_widget_xy_zero(lim1, w1, fuel);
        lemma_layout_widget_xy_zero(lim2, w2, fuel);
        T::axiom_eqv_reflexive(T::zero());
    };
    assert(layout_widget(lim1, w1, fuel).y.eqv(layout_widget(lim2, w2, fuel).y)) by {
        lemma_layout_widget_xy_zero(lim1, w1, fuel);
        lemma_layout_widget_xy_zero(lim2, w2, fuel);
        T::axiom_eqv_reflexive(T::zero());
    };
    assert(size_eqv(layout_widget(lim1, w1, fuel).size, layout_widget(lim2, w2, fuel).size)) by {
        lemma_layout_widget_size_congruence(lim1, lim2, w1, w2, fuel);
    };
    assert(layout_widget(lim1, w1, fuel).children.len()
        == layout_widget(lim2, w2, fuel).children.len()) by {
        lemma_layout_widget_children_len_eq(lim1, lim2, w1, w2, fuel);
    };
}

// ══════════════════════════════════════════════════════════════════════
// Measure congruence
// ══════════════════════════════════════════════════════════════════════

/// measure_widget respects eqv: eqv widgets produce eqv sizes.
/// Follows directly from layout congruence + measure == layout.size.
pub proof fn lemma_measure_widget_congruence<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(w1, w2, fuel),
    ensures
        size_eqv(
            crate::measure::measure_widget(lim1, w1, fuel),
            crate::measure::measure_widget(lim2, w2, fuel),
        ),
{
    crate::measure::lemma_measure_is_layout_size(lim1, w1, fuel);
    crate::measure::lemma_measure_is_layout_size(lim2, w2, fuel);
    lemma_layout_widget_size_congruence(lim1, lim2, w1, w2, fuel);
}

} // verus!
