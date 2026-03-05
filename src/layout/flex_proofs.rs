use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::layout::flex::*;

verus! {

// ── sum_weights lemmas ──────────────────────────────────────────────

/// sum_weights(weights, 0) ≡ zero.
pub proof fn lemma_sum_weights_zero<T: OrderedRing>(weights: Seq<T>)
    ensures
        sum_weights(weights, 0).eqv(T::zero()),
{
    T::axiom_eqv_reflexive(T::zero());
}

/// sum_weights is non-negative when all weights are non-negative.
pub proof fn lemma_sum_weights_nonneg<T: OrderedRing>(
    weights: Seq<T>,
    n: nat,
)
    requires
        n <= weights.len(),
        forall|i: int| 0 <= i < weights.len() ==> T::zero().le(weights[i]),
    ensures
        T::zero().le(sum_weights(weights, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_weights_nonneg(weights, (n - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_weights(weights, (n - 1) as nat),
            T::zero(), weights[(n - 1) as int],
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        T::axiom_eqv_reflexive(
            sum_weights(weights, (n - 1) as nat).add(weights[(n - 1) as int])
        );
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            sum_weights(weights, (n - 1) as nat).add(weights[(n - 1) as int]),
            sum_weights(weights, (n - 1) as nat).add(weights[(n - 1) as int]),
        );
    }
}

// ── flex_main_sum lemmas ────────────────────────────────────────────

/// flex_main_sum(weights, tw, avail, 0) ≡ zero.
pub proof fn lemma_flex_main_sum_zero<T: OrderedField>(
    weights: Seq<T>,
    total_weight: T,
    available: T,
)
    ensures
        flex_main_sum(weights, total_weight, available, 0).eqv(T::zero()),
{
    T::axiom_eqv_reflexive(T::zero());
}

/// flex_main_sum is non-negative when weights, total_weight, and available are non-negative.
pub proof fn lemma_flex_main_sum_nonneg<T: OrderedField>(
    weights: Seq<T>,
    total_weight: T,
    available: T,
    n: nat,
)
    requires
        n <= weights.len(),
        forall|i: int| 0 <= i < weights.len() ==> T::zero().le(weights[i]),
        T::zero().lt(total_weight),
        T::zero().le(available),
    ensures
        T::zero().le(flex_main_sum(weights, total_weight, available, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_flex_main_sum_nonneg(weights, total_weight, available, (n - 1) as nat);

        // Show 0 <= flex_child_main_size(w, tw, avail) = (w/tw) * avail
        let w = weights[(n - 1) as int];

        // 0 <= w and 0 < tw => 0/tw <= w/tw
        verus_algebra::lemmas::ordered_field_lemmas::lemma_le_div_monotone::<T>(
            T::zero(), w, total_weight,
        );
        // 0/tw ≡ 0
        T::axiom_div_is_mul_recip(T::zero(), total_weight);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(total_weight.recip());
        T::axiom_eqv_transitive(
            T::zero().div(total_weight),
            T::zero().mul(total_weight.recip()),
            T::zero(),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().div(total_weight), T::zero(), w.div(total_weight),
        );
        // 0 <= w/tw

        // 0 <= w/tw and 0 <= avail => 0 <= (w/tw) * avail
        T::axiom_le_mul_nonneg_monotone(T::zero(), w.div(total_weight), available);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(available);
        T::axiom_eqv_symmetric(T::zero().mul(available), T::zero());
        T::axiom_eqv_reflexive(w.div(total_weight).mul(available));
        T::axiom_le_congruence(
            T::zero().mul(available), T::zero(),
            w.div(total_weight).mul(available), w.div(total_weight).mul(available),
        );

        // prev_sum >= 0 and child_size >= 0 => sum >= 0
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), flex_main_sum(weights, total_weight, available, (n - 1) as nat),
            T::zero(), flex_child_main_size(w, total_weight, available),
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        let total = flex_main_sum(weights, total_weight, available, (n - 1) as nat)
            .add(flex_child_main_size(w, total_weight, available));
        T::axiom_eqv_reflexive(total);
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            total, total,
        );
    }
}

// ── flex_main_sum distributes as sum_weights / total_weight * available ──

/// flex_main_sum(weights, tw, avail, n) ≡ sum_weights(weights, n) / tw * avail.
///
/// The key identity: flex_main_sum is the partial sum of the proportional allocation.
pub proof fn lemma_flex_main_sum_identity<T: OrderedField>(
    weights: Seq<T>,
    total_weight: T,
    available: T,
    n: nat,
)
    requires
        n <= weights.len(),
        !total_weight.eqv(T::zero()),
    ensures
        flex_main_sum(weights, total_weight, available, n).eqv(
            sum_weights(weights, n).div(total_weight).mul(available)
        ),
    decreases n,
{
    if n == 0 {
        // LHS = 0, RHS = 0/tw * avail
        // 0/tw = 0*recip(tw) ≡ 0
        T::axiom_div_is_mul_recip(T::zero(), total_weight);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(total_weight.recip());
        T::axiom_eqv_transitive(
            T::zero().div(total_weight),
            T::zero().mul(total_weight.recip()),
            T::zero(),
        );
        // 0/tw * avail ≡ 0 * avail ≡ 0
        T::axiom_mul_congruence_left(T::zero().div(total_weight), T::zero(), available);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(available);
        T::axiom_eqv_transitive(
            T::zero().div(total_weight).mul(available),
            T::zero().mul(available),
            T::zero(),
        );
        T::axiom_eqv_symmetric(
            T::zero().div(total_weight).mul(available),
            T::zero(),
        );
    } else {
        let tw = total_weight;
        let av = available;
        let sw = sum_weights(weights, (n - 1) as nat);
        let w = weights[(n - 1) as int];
        let a = sw.div(tw);
        let b = w.div(tw);

        // IH: flex_main_sum(n-1) ≡ sw/tw * avail
        lemma_flex_main_sum_identity(weights, tw, av, (n - 1) as nat);

        // Step A: flex_main_sum(n) = flex_main_sum(n-1) + (w/tw)*avail
        //       ≡ (sw/tw)*avail + (w/tw)*avail  [by IH + congruence]
        T::axiom_add_congruence_left(
            flex_main_sum(weights, tw, av, (n - 1) as nat),
            a.mul(av),
            b.mul(av),
        );

        // Step B: a*av + b*av ≡ (a+b)*av  [right distributivity, reversed]
        verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<T>(a, b, av);
        T::axiom_eqv_symmetric(
            a.add(b).mul(av),
            a.mul(av).add(b.mul(av)),
        );

        // Step C: (sw+w)/tw ≡ sw/tw + w/tw  [div distributes over add]
        verus_algebra::lemmas::field_lemmas::lemma_div_distributes_over_add::<T>(sw, w, tw);
        // so sw.add(w).div(tw).eqv(a.add(b))

        // Step D: (sw+w)/tw ≡ a+b, so (sw+w)/tw * av ≡ (a+b)*av
        T::axiom_mul_congruence_left(sw.add(w).div(tw), a.add(b), av);
        // Reverse: (a+b)*av ≡ (sw+w)/tw * av
        T::axiom_eqv_symmetric(sw.add(w).div(tw).mul(av), a.add(b).mul(av));

        // Chain: a*av + b*av ≡ (a+b)*av ≡ (sw+w)/tw * av
        T::axiom_eqv_transitive(
            a.mul(av).add(b.mul(av)),
            a.add(b).mul(av),
            sw.add(w).div(tw).mul(av),
        );
        T::axiom_eqv_transitive(
            flex_main_sum(weights, tw, av, (n - 1) as nat).add(b.mul(av)),
            a.mul(av).add(b.mul(av)),
            sw.add(w).div(tw).mul(av),
        );
    }
}

/// When total_weight = sum_weights(n), the flex sizes sum to available:
/// flex_main_sum(weights, tw, avail, n) ≡ avail.
pub proof fn lemma_flex_sizes_sum_to_available<T: OrderedField>(
    weights: Seq<T>,
    available: T,
)
    requires
        weights.len() > 0,
        !sum_weights(weights, weights.len() as nat).eqv(T::zero()),
    ensures
        flex_main_sum(
            weights,
            sum_weights(weights, weights.len() as nat),
            available,
            weights.len() as nat,
        ).eqv(available),
{
    let n = weights.len() as nat;
    let tw = sum_weights(weights, n);

    // flex_main_sum(n) ≡ tw/tw * avail
    lemma_flex_main_sum_identity(weights, tw, available, n);

    // tw/tw ≡ 1
    verus_algebra::lemmas::field_lemmas::lemma_div_self::<T>(tw);

    // tw/tw * avail ≡ 1 * avail
    T::axiom_mul_congruence_left(tw.div(tw), T::one(), available);

    // 1 * avail ≡ avail
    T::axiom_mul_commutative(T::one(), available);
    T::axiom_mul_one_right(available);
    T::axiom_eqv_transitive(T::one().mul(available), available.mul(T::one()), available);

    // Chain: flex_main_sum(n) ≡ tw/tw*avail ≡ 1*avail ≡ avail
    T::axiom_eqv_transitive(
        tw.div(tw).mul(available),
        T::one().mul(available),
        available,
    );
    T::axiom_eqv_transitive(
        flex_main_sum(weights, tw, available, n),
        tw.div(tw).mul(available),
        available,
    );
}

// ── Flex children length/element lemmas ───────────────────────────

/// Length of flex_column_children sequence.
pub proof fn lemma_flex_column_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    h_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    index: nat,
)
    requires
        index <= weights.len(),
    ensures
        flex_column_children(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, index,
        ).len() == weights.len() - index,
    decreases weights.len() - index,
{
    if index >= weights.len() {
    } else {
        lemma_flex_column_children_len(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, index + 1,
        );
    }
}

/// Element access into flex_column_children.
pub proof fn lemma_flex_column_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    h_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    k: nat,
)
    requires
        k < weights.len(),
    ensures
        flex_column_children(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, 0,
        )[k as int]
            == crate::node::Node::leaf(
                padding.left.add(crate::alignment::align_offset(
                    h_align, available_width, child_cross_sizes[k as int],
                )),
                flex_column_child_y(
                    padding.top, weights, total_weight, available_height, spacing, k,
                ),
                crate::size::Size::new(
                    child_cross_sizes[k as int],
                    flex_child_main_size(weights[k as int], total_weight, available_height),
                ),
            ),
{
    lemma_flex_column_children_element_shifted(
        padding, spacing, h_align, weights, child_cross_sizes,
        total_weight, available_width, available_height, 0, k,
    );
}

proof fn lemma_flex_column_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    h_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < weights.len(),
    ensures
        flex_column_children(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        )[(k - start) as int]
            == crate::node::Node::leaf(
                padding.left.add(crate::alignment::align_offset(
                    h_align, available_width, child_cross_sizes[k as int],
                )),
                flex_column_child_y(
                    padding.top, weights, total_weight, available_height, spacing, k,
                ),
                crate::size::Size::new(
                    child_cross_sizes[k as int],
                    flex_child_main_size(weights[k as int], total_weight, available_height),
                ),
            ),
    decreases k - start,
{
    if start == k {
    } else {
        lemma_flex_column_children_len(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1,
        );
        lemma_flex_column_children_len(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        );
        lemma_flex_column_children_element_shifted(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1, k,
        );
        let tail = flex_column_children(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1,
        );
        let fc = flex_column_children(
            padding, spacing, h_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        );
        assert(fc[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

/// Length of flex_row_children sequence.
pub proof fn lemma_flex_row_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    v_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    index: nat,
)
    requires
        index <= weights.len(),
    ensures
        flex_row_children(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, index,
        ).len() == weights.len() - index,
    decreases weights.len() - index,
{
    if index >= weights.len() {
    } else {
        lemma_flex_row_children_len(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, index + 1,
        );
    }
}

/// Element access into flex_row_children.
pub proof fn lemma_flex_row_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    v_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    k: nat,
)
    requires
        k < weights.len(),
    ensures
        flex_row_children(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, 0,
        )[k as int]
            == crate::node::Node::leaf(
                flex_row_child_x(
                    padding.left, weights, total_weight, available_width, spacing, k,
                ),
                padding.top.add(crate::alignment::align_offset(
                    v_align, available_height, child_cross_sizes[k as int],
                )),
                crate::size::Size::new(
                    flex_child_main_size(weights[k as int], total_weight, available_width),
                    child_cross_sizes[k as int],
                ),
            ),
{
    lemma_flex_row_children_element_shifted(
        padding, spacing, v_align, weights, child_cross_sizes,
        total_weight, available_width, available_height, 0, k,
    );
}

proof fn lemma_flex_row_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    v_align: crate::alignment::Alignment,
    weights: Seq<T>,
    child_cross_sizes: Seq<T>,
    total_weight: T,
    available_width: T,
    available_height: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < weights.len(),
    ensures
        flex_row_children(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        )[(k - start) as int]
            == crate::node::Node::leaf(
                flex_row_child_x(
                    padding.left, weights, total_weight, available_width, spacing, k,
                ),
                padding.top.add(crate::alignment::align_offset(
                    v_align, available_height, child_cross_sizes[k as int],
                )),
                crate::size::Size::new(
                    flex_child_main_size(weights[k as int], total_weight, available_width),
                    child_cross_sizes[k as int],
                ),
            ),
    decreases k - start,
{
    if start == k {
    } else {
        lemma_flex_row_children_len(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1,
        );
        lemma_flex_row_children_len(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        );
        lemma_flex_row_children_element_shifted(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1, k,
        );
        let tail = flex_row_children(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start + 1,
        );
        let fr = flex_row_children(
            padding, spacing, v_align, weights, child_cross_sizes,
            total_weight, available_width, available_height, start,
        );
        assert(fr[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

} // verus!
