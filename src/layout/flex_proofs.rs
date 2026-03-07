use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::layout::flex::*;
use crate::layout::repeated_add;

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

// ── flex_child_main_size non-negativity ─────────────────────────

/// Each flex child's main-axis allocation is non-negative.
pub proof fn lemma_flex_child_main_size_nonneg<T: OrderedField>(
    weight: T,
    total_weight: T,
    available: T,
)
    requires
        T::zero().le(weight),
        T::zero().lt(total_weight),
        T::zero().le(available),
    ensures
        T::zero().le(flex_child_main_size(weight, total_weight, available)),
{
    // 0/tw ≡ 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), total_weight);
    verus_algebra::lemmas::ordered_field_lemmas::lemma_le_div_monotone::<T>(
        T::zero(), weight, total_weight,
    );
    T::axiom_div_is_mul_recip(T::zero(), total_weight);
    verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(total_weight.recip());
    T::axiom_eqv_transitive(
        T::zero().div(total_weight),
        T::zero().mul(total_weight.recip()),
        T::zero(),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero().div(total_weight), T::zero(), weight.div(total_weight),
    );
    // 0 <= weight/tw, 0 <= avail => 0 <= (weight/tw) * avail
    T::axiom_le_mul_nonneg_monotone(T::zero(), weight.div(total_weight), available);
    verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(available);
    T::axiom_eqv_symmetric(T::zero().mul(available), T::zero());
    T::axiom_eqv_reflexive(weight.div(total_weight).mul(available));
    T::axiom_le_congruence(
        T::zero().mul(available), T::zero(),
        weight.div(total_weight).mul(available),
        weight.div(total_weight).mul(available),
    );
}

// ── flex_main_sum monotonicity ────────────────────────────────────

/// flex_main_sum is monotone: i <= j implies flex_main_sum(i) <= flex_main_sum(j).
pub proof fn lemma_flex_main_sum_monotone<T: OrderedField>(
    weights: Seq<T>,
    total_weight: T,
    available: T,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= weights.len(),
        forall|k: int| 0 <= k < weights.len() ==> T::zero().le(weights[k]),
        T::zero().lt(total_weight),
        T::zero().le(available),
    ensures
        flex_main_sum(weights, total_weight, available, i).le(
            flex_main_sum(weights, total_weight, available, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(flex_main_sum(weights, total_weight, available, i));
    } else {
        lemma_flex_main_sum_monotone(weights, total_weight, available, i, (j - 1) as nat);
        // flex_main_sum(j) = flex_main_sum(j-1) + flex_child_main_size(j-1)
        // Show flex_main_sum(j-1) <= flex_main_sum(j) since the added term is nonneg
        let prev = flex_main_sum(weights, total_weight, available, (j - 1) as nat);
        let term = flex_child_main_size(weights[(j - 1) as int], total_weight, available);
        lemma_flex_child_main_size_nonneg(weights[(j - 1) as int], total_weight, available);
        // 0 <= term, so prev <= prev + term
        T::axiom_le_add_monotone(T::zero(), term, prev);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(prev);
        T::axiom_add_commutative(term, prev);
        T::axiom_le_congruence(
            T::zero().add(prev), prev,
            term.add(prev), prev.add(term),
        );
        // Chain: flex_main_sum(i) <= prev <= prev + term = flex_main_sum(j)
        T::axiom_le_transitive(
            flex_main_sum(weights, total_weight, available, i),
            prev,
            flex_main_sum(weights, total_weight, available, j),
        );
    }
}

// ── Flex column CWB ───────────────────────────────────────────────

/// Flex column layout has children_within_bounds.
///
/// Preconditions: padding fits, nonneg spacings/weights, total_weight > 0,
/// spacing fits, and min.height = 0 (so each child's effective limits are wf).
pub proof fn lemma_flex_column_children_within_bounds<T: OrderedField>(
    limits: crate::limits::Limits<T>,
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: crate::alignment::Alignment,
    children: Seq<crate::widget::FlexItem<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        limits.min.height.eqv(T::zero()),
        children.len() > 0,
        forall|i: int| 0 <= i < children.len() ==>
            T::zero().le(children[i].weight),
        ({
            let weights = Seq::new(children.len(), |i: int| children[i].weight);
            T::zero().lt(sum_weights(weights, weights.len() as nat))
        }),
        ({
            let v = padding.vertical();
            let total_spacing = repeated_add(spacing, (children.len() - 1) as nat);
            v.add(total_spacing).le(limits.max.height)
        }),
    ensures
        crate::widget::layout_widget(limits, crate::widget::Widget::Flex {
            padding, spacing, alignment,
            direction: crate::widget::FlexDirection::Column,
            children,
        }, fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let weights = Seq::new(children.len(), |i: int| children[i].weight);
    let tw = sum_weights(weights, weights.len() as nat);
    let total_spacing = repeated_add(spacing, (children.len() - 1) as nat);
    let n = children.len() as nat;

    // h >= 0, v >= 0
    crate::layout::proofs::lemma_nonneg_sum(padding.left, padding.right);
    crate::layout::proofs::lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf
    crate::layout::proofs::lemma_shrink_wf(limits, h, v);
    crate::layout::proofs::lemma_add_comm_le(h, limits.min.width, limits.max.width);
    crate::layout::proofs::lemma_add_comm_le(v, limits.min.height, limits.max.height);

    // min.h ≡ 0 and padding fits → min.h.le(max.h - v), unfolds inner.max.h = max.h - v
    // v + 0 ≡ v, v + min.h ≡ v, v.le(max.h) from padding fits + min.h ≡ 0
    T::axiom_add_zero_right(v);
    T::axiom_eqv_symmetric(v.add(T::zero()), v);
    T::axiom_add_congruence_left(limits.min.height, T::zero(), v);
    T::axiom_eqv_symmetric(limits.min.height.add(v), T::zero().add(v));
    T::axiom_add_commutative(T::zero(), v);
    T::axiom_eqv_transitive(limits.min.height.add(v), T::zero().add(v), v.add(T::zero()));
    T::axiom_eqv_transitive(limits.min.height.add(v), v.add(T::zero()), v);
    // limits.min.height.add(v) ≡ v
    // v ≡ limits.min.height.add(v), so v.le(max.h) from min.h.add(v).le(max.h) + congruence
    crate::layout::proofs::lemma_add_comm_le(v, limits.min.height, limits.max.height);
    // limits.min.height.add(v).le(limits.max.height)
    T::axiom_eqv_symmetric(limits.min.height.add(v), v);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        limits.min.height.add(v), v, limits.max.height,
    );
    // v.le(max.h)
    // 0 <= max.h - v from v <= max.h
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        v, limits.max.height, v,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self::<T>(v);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        v.sub(v), T::zero(), limits.max.height.sub(v),
    );
    // T::zero().le(max.h.sub(v))

    // min.h.le(max.h - v): min.h ≡ 0 <= max.h - v
    T::axiom_eqv_symmetric(limits.min.height, T::zero());
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero(), limits.min.height, limits.max.height.sub(v),
    );
    // This unfolds inner.max.height = max(min.h, max.h - v) = max.h - v

    // avail_h = inner.max.h - total_spacing = max.h - v - total_spacing
    let avail_h = inner.max.height.sub(total_spacing);
    let avail_w = limits.max.width.sub(h);

    // avail_h >= 0: v + total_spacing <= max.h from precondition
    assert(v.add(total_spacing).le(limits.max.height));
    // total_spacing <= max.h - v
    // From precond: v + ts <= max.h → ts + v <= max.h (by comm)
    T::axiom_add_commutative(v, total_spacing);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        v.add(total_spacing), total_spacing.add(v), limits.max.height,
    );
    // (ts + v) - v <= max.h - v
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        total_spacing.add(v), limits.max.height, v,
    );
    // (ts + v) - v ≡ ts
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<T>(total_spacing, v);
    // ts <= max.h - v
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        total_spacing.add(v).sub(v), total_spacing, limits.max.height.sub(v),
    );
    // total_spacing.le(max.h - v)
    // Since min.h.le(max.h - v), inner.max.h = max.h - v, so total_spacing.le(inner.max.h)

    // avail_h = inner.max.h - total_spacing >= 0
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        total_spacing, limits.max.height.sub(v), total_spacing,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self::<T>(total_spacing);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        total_spacing.sub(total_spacing), T::zero(), limits.max.height.sub(v).sub(total_spacing),
    );
    // T::zero().le(avail_h)

    // tw > 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), tw);
    assert(!tw.eqv(T::zero())) by {
        if tw.eqv(T::zero()) { T::axiom_eqv_symmetric(tw, T::zero()); }
    };

    // shrink max bound
    crate::layout::proofs::lemma_shrink_max_bound(limits, h, v);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.width, h,
    );
    T::axiom_eqv_symmetric(avail_w.add(h), limits.max.width);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        inner.max.width.add(h), limits.max.width, avail_w.add(h),
    );
    crate::layout::proofs::lemma_le_add_cancel_right(inner.max.width, avail_w, h);
    // inner.max.width.le(avail_w)

    // cn = widget child nodes
    let cn = crate::widget::flex_column_widget_child_nodes(
        inner, children, weights, tw, avail_h, (fuel - 1) as nat,
    );
    let child_cross_sizes = Seq::new(cn.len(), |i: int| cn[i].size.width);

    // Each child: bound on size
    assert forall|k: int| 0 <= k < cn.len() implies
        cn[k].size.width.le(avail_w)
        && cn[k].size.height.le(
            flex_child_main_size(weights[k], tw, avail_h))
        && T::zero().le(cn[k].size.width)
        && T::zero().le(cn[k].size.height)
    by {
        let main_alloc = flex_child_main_size(weights[k], tw, avail_h);
        lemma_flex_child_main_size_nonneg(weights[k], tw, avail_h);
        // child_lim = {min: inner.min, max: (inner.max.w, main_alloc)}
        let child_lim = crate::limits::Limits {
            min: inner.min,
            max: crate::size::Size::new(inner.max.width, main_alloc),
        };
        // child_lim.wf: inner.min.w <= inner.max.w (from inner.wf)
        // inner.min.h = limits.min.h ≡ 0 <= main_alloc
        T::axiom_eqv_symmetric(limits.min.height, T::zero());
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero(), limits.min.height, main_alloc,
        );
        // nonneg for wf
        T::axiom_le_transitive(T::zero(), inner.min.width, inner.max.width);
        crate::layout::proofs::lemma_layout_respects_limits(
            child_lim, children[k].child, (fuel - 1) as nat,
        );
        // cn[k].size <= child_lim.max
        T::axiom_le_transitive(cn[k].size.width, inner.max.width, avail_w);
        T::axiom_le_transitive(T::zero(), inner.min.width, cn[k].size.width);
        T::axiom_le_transitive(T::zero(), inner.min.height, cn[k].size.height);
    };

    // parent.size = limits.resolve(limits.max) = limits.max
    // (resolve(max) = max for wf limits since min <= max)

    // left + avail_w <= max.w
    crate::layout::proofs::lemma_le_add_nonneg(padding.left, padding.right);
    T::axiom_le_add_monotone(padding.left, h, avail_w);
    T::axiom_add_commutative(h, avail_w);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.width, h,
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding.left.add(avail_w), h.add(avail_w), avail_w.add(h),
    );
    T::axiom_le_transitive(
        padding.left.add(avail_w), avail_w.add(h), limits.max.width,
    );

    // top + avail_h + total_spacing <= max.h:
    // avail_h + total_spacing ≡ inner.max.h = max.h - v (by sub_then_add_cancel)
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        inner.max.height, total_spacing,
    );
    // avail_h.add(total_spacing).eqv(inner.max.height) = max.h - v
    // top + (max.h - v) = max.h - bottom <= max.h
    crate::layout::proofs::lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, v, inner.max.height);
    // padding.top.add(inner.max.height).le(v.add(inner.max.height))
    // v + inner.max.h = v + (max.h - v) ≡ max.h
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.height, v,
    );
    T::axiom_add_commutative(v, limits.max.height.sub(v));
    T::axiom_eqv_transitive(
        v.add(inner.max.height),
        limits.max.height.sub(v).add(v),
        limits.max.height,
    );
    // padding.top.add(inner.max.height).le(v.add(inner.max.height))
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding.top.add(inner.max.height), v.add(inner.max.height), limits.max.height,
    );
    // padding.top.add(inner.max.height).le(limits.max.height)

    // Layout children structure
    lemma_flex_column_children_len(
        padding, spacing, alignment, weights, child_cross_sizes,
        tw, avail_w, avail_h, 0,
    );

    let layout = flex_column_layout(
        limits, padding, spacing, alignment, weights, child_cross_sizes,
    );

    // Per-child bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        lemma_flex_column_children_element(
            padding, spacing, alignment, weights, child_cross_sizes,
            tw, avail_w, avail_h, i as nat,
        );

        // X lower: left <= left + align_offset, 0 <= left
        crate::layout::proofs::lemma_column_child_x_lower_bound(
            padding.left, alignment, avail_w, child_cross_sizes[i],
        );
        T::axiom_le_transitive(T::zero(), padding.left, layout.children[i].x);

        // X upper: left + align_offset + w <= left + avail_w <= max.w
        crate::layout::proofs::lemma_column_child_x_upper_bound(
            padding.left, alignment, avail_w, child_cross_sizes[i],
        );
        T::axiom_le_transitive(
            layout.children[i].x.add(cn[i].size.width),
            padding.left.add(avail_w),
            limits.max.width,
        );

        // Y lower: 0 <= top (nonneg padding), flex_main_sum >= 0, repeated_add >= 0
        lemma_flex_main_sum_nonneg(weights, tw, avail_h, i as nat);
        crate::layout::proofs::lemma_repeated_add_nonneg(spacing, i as nat);
        crate::layout::proofs::lemma_nonneg_sum(
            padding.top,
            flex_main_sum(weights, tw, avail_h, i as nat),
        );
        crate::layout::proofs::lemma_nonneg_sum(
            padding.top.add(flex_main_sum(weights, tw, avail_h, i as nat)),
            repeated_add(spacing, i as nat),
        );
        // 0 <= y_i

        // Y upper bound: y_i + cn[i].size.height <= max.h
        // Strategy: y_i + h_i <= y_i + fms_i (child bound)
        //   y_i + fms_i = top + sum(i+1) + rep(i) (algebra)
        //   top + sum(i+1) + rep(i) <= top + sum(n) + rep(n-1) (monotone)
        //   = top + avail_h + total_spacing = top + inner.max.h <= max.h

        let fms_i = flex_child_main_size(weights[i], tw, avail_h);
        let sum_i = flex_main_sum(weights, tw, avail_h, i as nat);
        let sum_i1 = flex_main_sum(weights, tw, avail_h, (i + 1) as nat);
        let sum_n = flex_main_sum(weights, tw, avail_h, n);
        let rep_i = repeated_add(spacing, i as nat);

        // Step 1: y_i + cn[i].size.height <= y_i + fms_i
        // le_add_monotone gives h+y <= fms+y; flip to y+h <= y+fms
        T::axiom_le_add_monotone(cn[i].size.height, fms_i, layout.children[i].y);
        T::axiom_add_commutative(cn[i].size.height, layout.children[i].y);
        T::axiom_add_commutative(fms_i, layout.children[i].y);
        T::axiom_le_congruence(
            cn[i].size.height.add(layout.children[i].y),
            layout.children[i].y.add(cn[i].size.height),
            fms_i.add(layout.children[i].y),
            layout.children[i].y.add(fms_i),
        );

        // Step 2: y_i + fms_i ≡ top + sum(i+1) + rep(i) via algebra
        // y_i = top + sum_i + rep_i, so y_i + fms_i = (top + sum_i + rep_i) + fms_i
        // = (top + sum_i) + rep_i + fms_i [by assoc of padding.top.add(sum_i)]
        // = (top + sum_i) + fms_i + rep_i [comm rep_i, fms_i]
        // = top + (sum_i + fms_i) + rep_i [assoc]
        // = top + sum_i1 + rep_i [definitional: sum_i + fms_i = sum_i1]
        let yi_fms = layout.children[i].y.add(fms_i);
        // Rearrange: (A + B) + C = A + (B + C) = A + (C + B) = (A + C) + B
        // where A = top + sum_i, B = rep_i, C = fms_i
        T::axiom_add_associative(padding.top.add(sum_i), rep_i, fms_i);
        T::axiom_add_commutative(rep_i, fms_i);
        T::axiom_eqv_reflexive(padding.top.add(sum_i));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.top.add(sum_i), padding.top.add(sum_i),
            rep_i.add(fms_i), fms_i.add(rep_i),
        );
        T::axiom_eqv_transitive(
            yi_fms,
            padding.top.add(sum_i).add(rep_i.add(fms_i)),
            padding.top.add(sum_i).add(fms_i.add(rep_i)),
        );
        T::axiom_add_associative(padding.top.add(sum_i), fms_i, rep_i);
        T::axiom_eqv_symmetric(
            padding.top.add(sum_i).add(fms_i).add(rep_i),
            padding.top.add(sum_i).add(fms_i.add(rep_i)),
        );
        T::axiom_eqv_transitive(
            yi_fms,
            padding.top.add(sum_i).add(fms_i.add(rep_i)),
            padding.top.add(sum_i).add(fms_i).add(rep_i),
        );
        // yi_fms ≡ (top + sum_i + fms_i) + rep_i
        // sum_i + fms_i == sum_i1 (definitional), top + sum_i + fms_i ≡ top + sum_i1
        T::axiom_add_associative(padding.top, sum_i, fms_i);
        T::axiom_add_congruence_left(
            padding.top.add(sum_i).add(fms_i), padding.top.add(sum_i1), rep_i,
        );
        T::axiom_eqv_transitive(
            yi_fms,
            padding.top.add(sum_i).add(fms_i).add(rep_i),
            padding.top.add(sum_i1).add(rep_i),
        );
        // yi_fms ≡ top + sum_i1 + rep_i

        // Step 3: top + sum(i+1) + rep(i) <= top + sum(n) + total_spacing
        lemma_flex_main_sum_monotone(weights, tw, avail_h, (i + 1) as nat, n);
        crate::layout::proofs::lemma_repeated_add_monotone(spacing, i as nat, (n - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            sum_i1, sum_n, rep_i, total_spacing,
        );
        T::axiom_le_add_monotone(
            sum_i1.add(rep_i), sum_n.add(total_spacing), padding.top,
        );
        // Flip: (a)+top <= (b)+top → top+(a) <= top+(b) via commutativity
        T::axiom_add_commutative(sum_i1.add(rep_i), padding.top);
        T::axiom_add_commutative(sum_n.add(total_spacing), padding.top);
        T::axiom_le_congruence(
            sum_i1.add(rep_i).add(padding.top), padding.top.add(sum_i1.add(rep_i)),
            sum_n.add(total_spacing).add(padding.top), padding.top.add(sum_n.add(total_spacing)),
        );
        // top.add(sum_i1.add(rep_i)).le(top.add(sum_n.add(total_spacing)))
        // Congruence: top.add(sum_i1.add(rep_i)) → top + sum_i1 + rep_i
        T::axiom_add_associative(padding.top, sum_i1, rep_i);
        T::axiom_eqv_symmetric(
            padding.top.add(sum_i1).add(rep_i),
            padding.top.add(sum_i1.add(rep_i)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.top.add(sum_i1.add(rep_i)),
            padding.top.add(sum_i1).add(rep_i),
            padding.top.add(sum_n.add(total_spacing)),
        );
        // and top.add(sum_n.add(total_spacing)) → top + sum_n + total_spacing
        T::axiom_add_associative(padding.top, sum_n, total_spacing);
        T::axiom_eqv_symmetric(
            padding.top.add(sum_n).add(total_spacing),
            padding.top.add(sum_n.add(total_spacing)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.top.add(sum_i1).add(rep_i),
            padding.top.add(sum_n.add(total_spacing)),
            padding.top.add(sum_n).add(total_spacing),
        );

        // Step 4: sum_n ≡ avail_h → top + sum_n + ts ≡ top + avail_h + ts
        lemma_flex_sizes_sum_to_available(weights, avail_h);
        // top.add(sum_n).eqv(top.add(avail_h)) via lemma_add_congruence
        T::axiom_eqv_reflexive(padding.top);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.top, padding.top, sum_n, avail_h,
        );
        // top.add(sum_n).add(ts).eqv(top.add(avail_h).add(ts))
        T::axiom_add_congruence_left(
            padding.top.add(sum_n), padding.top.add(avail_h), total_spacing,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.top.add(sum_i1).add(rep_i),
            padding.top.add(sum_n).add(total_spacing),
            padding.top.add(avail_h).add(total_spacing),
        );

        // Step 5: top + avail_h + ts ≡ top + inner.max.h <= max.h
        // avail_h + ts ≡ inner.max.h (sub_then_add_cancel from outer scope)
        // top + (avail_h + ts) ≡ top + inner.max.h
        T::axiom_eqv_reflexive(padding.top);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.top, padding.top,
            avail_h.add(total_spacing), inner.max.height,
        );
        // top.add(avail_h).add(ts) ≡ top.add(avail_h.add(ts)) by assoc
        T::axiom_add_associative(padding.top, avail_h, total_spacing);
        // Chain: top+avail_h+ts ≡ top+(avail_h+ts) ≡ top+inner.max.h
        T::axiom_eqv_transitive(
            padding.top.add(avail_h).add(total_spacing),
            padding.top.add(avail_h.add(total_spacing)),
            padding.top.add(inner.max.height),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.top.add(sum_i1).add(rep_i),
            padding.top.add(avail_h).add(total_spacing),
            padding.top.add(inner.max.height),
        );

        // Full chain: y_i + cn[i].h <= yi_fms ≡ top+sum_i1+rep_i <= top+inner.max.h <= max.h
        // We have: yi_fms.eqv(top+sum_i1+rep_i) from Step 2
        // Symmetric: top+sum_i1+rep_i.eqv(yi_fms)
        T::axiom_eqv_symmetric(yi_fms, padding.top.add(sum_i1).add(rep_i));
        // le_congruence_left: top+sum_i1+rep_i ≡ yi_fms AND top+sum_i1+rep_i ≤ top+inner.max.h → yi_fms ≤ top+inner.max.h
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.top.add(sum_i1).add(rep_i), yi_fms,
            padding.top.add(inner.max.height),
        );
        T::axiom_le_transitive(
            layout.children[i].y.add(cn[i].size.height),
            yi_fms,
            padding.top.add(inner.max.height),
        );
        T::axiom_le_transitive(
            layout.children[i].y.add(cn[i].size.height),
            padding.top.add(inner.max.height),
            limits.max.height,
        );

        // Connect cn[i].size to child_cross_sizes[i]
        assert(child_cross_sizes[i] === cn[i].size.width);
    };

    crate::layout::proofs::lemma_merge_layout_cwb(layout, cn);
}

// ── Flex row CWB ─────────────────────────────────────────────────

/// Flex row layout has children_within_bounds.
///
/// Symmetric to column: main axis = width (X), cross axis = height (Y).
pub proof fn lemma_flex_row_children_within_bounds<T: OrderedField>(
    limits: crate::limits::Limits<T>,
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: crate::alignment::Alignment,
    children: Seq<crate::widget::FlexItem<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        limits.min.width.eqv(T::zero()),
        children.len() > 0,
        forall|i: int| 0 <= i < children.len() ==>
            T::zero().le(children[i].weight),
        ({
            let weights = Seq::new(children.len(), |i: int| children[i].weight);
            T::zero().lt(sum_weights(weights, weights.len() as nat))
        }),
        ({
            let h = padding.horizontal();
            let total_spacing = repeated_add(spacing, (children.len() - 1) as nat);
            h.add(total_spacing).le(limits.max.width)
        }),
    ensures
        crate::widget::layout_widget(limits, crate::widget::Widget::Flex {
            padding, spacing, alignment,
            direction: crate::widget::FlexDirection::Row,
            children,
        }, fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let weights = Seq::new(children.len(), |i: int| children[i].weight);
    let tw = sum_weights(weights, weights.len() as nat);
    let total_spacing = repeated_add(spacing, (children.len() - 1) as nat);
    let n = children.len() as nat;

    // h >= 0, v >= 0
    crate::layout::proofs::lemma_nonneg_sum(padding.left, padding.right);
    crate::layout::proofs::lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf
    crate::layout::proofs::lemma_shrink_wf(limits, h, v);
    crate::layout::proofs::lemma_add_comm_le(h, limits.min.width, limits.max.width);
    crate::layout::proofs::lemma_add_comm_le(v, limits.min.height, limits.max.height);

    // min.w ≡ 0 → min.w.le(max.w - h), so inner.max.w = max.w - h
    T::axiom_add_zero_right(h);
    T::axiom_eqv_symmetric(h.add(T::zero()), h);
    T::axiom_add_congruence_left(limits.min.width, T::zero(), h);
    T::axiom_eqv_symmetric(limits.min.width.add(h), T::zero().add(h));
    T::axiom_add_commutative(T::zero(), h);
    T::axiom_eqv_transitive(limits.min.width.add(h), T::zero().add(h), h.add(T::zero()));
    T::axiom_eqv_transitive(limits.min.width.add(h), h.add(T::zero()), h);
    crate::layout::proofs::lemma_add_comm_le(h, limits.min.width, limits.max.width);
    T::axiom_eqv_symmetric(limits.min.width.add(h), h);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        limits.min.width.add(h), h, limits.max.width,
    );
    // h.le(max.w)
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        h, limits.max.width, h,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self::<T>(h);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        h.sub(h), T::zero(), limits.max.width.sub(h),
    );
    // 0 <= max.w - h
    T::axiom_eqv_symmetric(limits.min.width, T::zero());
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero(), limits.min.width, limits.max.width.sub(h),
    );
    // min.w.le(max.w - h) → inner.max.w = max.w - h

    // avail_w = inner.max.w - total_spacing, avail_h = inner.max.h
    let avail_w = inner.max.width.sub(total_spacing);
    let avail_h = limits.max.height.sub(v);

    // avail_w >= 0: h + total_spacing <= max.w from precondition
    assert(h.add(total_spacing).le(limits.max.width));
    T::axiom_add_commutative(h, total_spacing);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        h.add(total_spacing), total_spacing.add(h), limits.max.width,
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        total_spacing.add(h), limits.max.width, h,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<T>(total_spacing, h);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        total_spacing.add(h).sub(h), total_spacing, limits.max.width.sub(h),
    );
    // total_spacing.le(max.w - h) = total_spacing.le(inner.max.w)

    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        total_spacing, limits.max.width.sub(h), total_spacing,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self::<T>(total_spacing);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        total_spacing.sub(total_spacing), T::zero(), limits.max.width.sub(h).sub(total_spacing),
    );
    // 0 <= avail_w

    // tw > 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), tw);
    assert(!tw.eqv(T::zero())) by {
        if tw.eqv(T::zero()) { T::axiom_eqv_symmetric(tw, T::zero()); }
    };

    // shrink max bound (height side)
    crate::layout::proofs::lemma_shrink_max_bound(limits, h, v);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.height, v,
    );
    T::axiom_eqv_symmetric(avail_h.add(v), limits.max.height);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        inner.max.height.add(v), limits.max.height, avail_h.add(v),
    );
    crate::layout::proofs::lemma_le_add_cancel_right(inner.max.height, avail_h, v);
    // inner.max.height.le(avail_h)

    // cn = widget child nodes
    let cn = crate::widget::flex_row_widget_child_nodes(
        inner, children, weights, tw, avail_w, (fuel - 1) as nat,
    );
    let child_cross_sizes = Seq::new(cn.len(), |i: int| cn[i].size.height);

    // Each child: bound on size
    assert forall|k: int| 0 <= k < cn.len() implies
        cn[k].size.height.le(avail_h)
        && cn[k].size.width.le(
            flex_child_main_size(weights[k], tw, avail_w))
        && T::zero().le(cn[k].size.width)
        && T::zero().le(cn[k].size.height)
    by {
        let main_alloc = flex_child_main_size(weights[k], tw, avail_w);
        lemma_flex_child_main_size_nonneg(weights[k], tw, avail_w);
        let child_lim = crate::limits::Limits {
            min: inner.min,
            max: crate::size::Size::new(main_alloc, inner.max.height),
        };
        // child_lim.wf: inner.min.w ≡ 0 <= main_alloc
        T::axiom_eqv_symmetric(limits.min.width, T::zero());
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero(), limits.min.width, main_alloc,
        );
        T::axiom_le_transitive(T::zero(), inner.min.height, inner.max.height);
        crate::layout::proofs::lemma_layout_respects_limits(
            child_lim, children[k].child, (fuel - 1) as nat,
        );
        T::axiom_le_transitive(cn[k].size.height, inner.max.height, avail_h);
        T::axiom_le_transitive(T::zero(), inner.min.width, cn[k].size.width);
        T::axiom_le_transitive(T::zero(), inner.min.height, cn[k].size.height);
    };

    // top + avail_h <= max.h
    crate::layout::proofs::lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, v, avail_h);
    T::axiom_add_commutative(v, limits.max.height.sub(v));
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.height, v,
    );
    T::axiom_eqv_transitive(
        v.add(inner.max.height),
        limits.max.height.sub(v).add(v),
        limits.max.height,
    );
    T::axiom_add_commutative(padding.top, padding.bottom);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding.top.add(inner.max.height), v.add(inner.max.height), limits.max.height,
    );
    // padding.top.add(inner.max.height).le(limits.max.height)

    // left + avail_w + total_spacing <= max.w:
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        inner.max.width, total_spacing,
    );
    // avail_w.add(total_spacing).eqv(inner.max.width)
    crate::layout::proofs::lemma_le_add_nonneg(padding.left, padding.right);
    T::axiom_le_add_monotone(padding.left, h, inner.max.width);
    // left.add(inner.max.w).le(h.add(inner.max.w))
    // h + inner.max.w = h + (max.w - h) ≡ max.w
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.width, h,
    );
    T::axiom_add_commutative(h, limits.max.width.sub(h));
    T::axiom_eqv_transitive(
        h.add(inner.max.width),
        limits.max.width.sub(h).add(h),
        limits.max.width,
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding.left.add(inner.max.width), h.add(inner.max.width), limits.max.width,
    );
    // padding.left.add(inner.max.width).le(limits.max.width)

    // Layout children structure
    lemma_flex_row_children_len(
        padding, spacing, alignment, weights, child_cross_sizes,
        tw, avail_w, avail_h, 0,
    );

    let layout = flex_row_layout(
        limits, padding, spacing, alignment, weights, child_cross_sizes,
    );

    // Per-child bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        lemma_flex_row_children_element(
            padding, spacing, alignment, weights, child_cross_sizes,
            tw, avail_w, avail_h, i as nat,
        );

        // Y lower: top <= top + align_offset, 0 <= top
        crate::layout::proofs::lemma_row_child_y_lower_bound(
            padding.top, alignment, avail_h, child_cross_sizes[i],
        );
        T::axiom_le_transitive(T::zero(), padding.top, layout.children[i].y);

        // Y upper: top + align_offset + h <= top + avail_h <= max.h
        crate::layout::proofs::lemma_row_child_y_upper_bound(
            padding.top, alignment, avail_h, child_cross_sizes[i],
        );
        T::axiom_le_transitive(
            layout.children[i].y.add(cn[i].size.height),
            padding.top.add(avail_h),
            limits.max.height,
        );

        // X lower: 0 <= left (nonneg padding), flex_main_sum >= 0, repeated_add >= 0
        lemma_flex_main_sum_nonneg(weights, tw, avail_w, i as nat);
        crate::layout::proofs::lemma_repeated_add_nonneg(spacing, i as nat);
        crate::layout::proofs::lemma_nonneg_sum(
            padding.left,
            flex_main_sum(weights, tw, avail_w, i as nat),
        );
        crate::layout::proofs::lemma_nonneg_sum(
            padding.left.add(flex_main_sum(weights, tw, avail_w, i as nat)),
            repeated_add(spacing, i as nat),
        );
        // 0 <= x_i

        // X upper bound: x_i + cn[i].size.width <= max.w
        let fms_i = flex_child_main_size(weights[i], tw, avail_w);
        let sum_i = flex_main_sum(weights, tw, avail_w, i as nat);
        let sum_i1 = flex_main_sum(weights, tw, avail_w, (i + 1) as nat);
        let sum_n = flex_main_sum(weights, tw, avail_w, n);
        let rep_i = repeated_add(spacing, i as nat);

        // Step 1: x_i + cn[i].size.width <= x_i + fms_i
        T::axiom_le_add_monotone(cn[i].size.width, fms_i, layout.children[i].x);
        T::axiom_add_commutative(cn[i].size.width, layout.children[i].x);
        T::axiom_add_commutative(fms_i, layout.children[i].x);
        T::axiom_le_congruence(
            cn[i].size.width.add(layout.children[i].x),
            layout.children[i].x.add(cn[i].size.width),
            fms_i.add(layout.children[i].x),
            layout.children[i].x.add(fms_i),
        );

        // Step 2: x_i + fms_i ≡ left + sum(i+1) + rep(i)
        let xi_fms = layout.children[i].x.add(fms_i);
        T::axiom_add_associative(padding.left.add(sum_i), rep_i, fms_i);
        T::axiom_add_commutative(rep_i, fms_i);
        T::axiom_eqv_reflexive(padding.left.add(sum_i));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.left.add(sum_i), padding.left.add(sum_i),
            rep_i.add(fms_i), fms_i.add(rep_i),
        );
        T::axiom_eqv_transitive(
            xi_fms,
            padding.left.add(sum_i).add(rep_i.add(fms_i)),
            padding.left.add(sum_i).add(fms_i.add(rep_i)),
        );
        T::axiom_add_associative(padding.left.add(sum_i), fms_i, rep_i);
        T::axiom_eqv_symmetric(
            padding.left.add(sum_i).add(fms_i).add(rep_i),
            padding.left.add(sum_i).add(fms_i.add(rep_i)),
        );
        T::axiom_eqv_transitive(
            xi_fms,
            padding.left.add(sum_i).add(fms_i.add(rep_i)),
            padding.left.add(sum_i).add(fms_i).add(rep_i),
        );
        T::axiom_add_associative(padding.left, sum_i, fms_i);
        T::axiom_add_congruence_left(
            padding.left.add(sum_i).add(fms_i), padding.left.add(sum_i1), rep_i,
        );
        T::axiom_eqv_transitive(
            xi_fms,
            padding.left.add(sum_i).add(fms_i).add(rep_i),
            padding.left.add(sum_i1).add(rep_i),
        );

        // Step 3: left + sum(i+1) + rep(i) <= left + sum(n) + total_spacing
        lemma_flex_main_sum_monotone(weights, tw, avail_w, (i + 1) as nat, n);
        crate::layout::proofs::lemma_repeated_add_monotone(spacing, i as nat, (n - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            sum_i1, sum_n, rep_i, total_spacing,
        );
        T::axiom_le_add_monotone(
            sum_i1.add(rep_i), sum_n.add(total_spacing), padding.left,
        );
        T::axiom_add_commutative(sum_i1.add(rep_i), padding.left);
        T::axiom_add_commutative(sum_n.add(total_spacing), padding.left);
        T::axiom_le_congruence(
            sum_i1.add(rep_i).add(padding.left), padding.left.add(sum_i1.add(rep_i)),
            sum_n.add(total_spacing).add(padding.left), padding.left.add(sum_n.add(total_spacing)),
        );
        T::axiom_add_associative(padding.left, sum_i1, rep_i);
        T::axiom_eqv_symmetric(
            padding.left.add(sum_i1).add(rep_i),
            padding.left.add(sum_i1.add(rep_i)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.left.add(sum_i1.add(rep_i)),
            padding.left.add(sum_i1).add(rep_i),
            padding.left.add(sum_n.add(total_spacing)),
        );
        T::axiom_add_associative(padding.left, sum_n, total_spacing);
        T::axiom_eqv_symmetric(
            padding.left.add(sum_n).add(total_spacing),
            padding.left.add(sum_n.add(total_spacing)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.left.add(sum_i1).add(rep_i),
            padding.left.add(sum_n.add(total_spacing)),
            padding.left.add(sum_n).add(total_spacing),
        );

        // Step 4: sum_n ≡ avail_w → left + sum_n + ts ≡ left + avail_w + ts
        lemma_flex_sizes_sum_to_available(weights, avail_w);
        T::axiom_eqv_reflexive(padding.left);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.left, padding.left, sum_n, avail_w,
        );
        T::axiom_add_congruence_left(
            padding.left.add(sum_n), padding.left.add(avail_w), total_spacing,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.left.add(sum_i1).add(rep_i),
            padding.left.add(sum_n).add(total_spacing),
            padding.left.add(avail_w).add(total_spacing),
        );

        // Step 5: left + avail_w + ts ≡ left + inner.max.w <= max.w
        T::axiom_eqv_reflexive(padding.left);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.left, padding.left,
            avail_w.add(total_spacing), inner.max.width,
        );
        T::axiom_add_associative(padding.left, avail_w, total_spacing);
        T::axiom_eqv_transitive(
            padding.left.add(avail_w).add(total_spacing),
            padding.left.add(avail_w.add(total_spacing)),
            padding.left.add(inner.max.width),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            padding.left.add(sum_i1).add(rep_i),
            padding.left.add(avail_w).add(total_spacing),
            padding.left.add(inner.max.width),
        );

        // Full chain: x_i + w <= xi_fms ≡ left+sum_i1+rep_i <= left+inner.max.w <= max.w
        T::axiom_eqv_symmetric(xi_fms, padding.left.add(sum_i1).add(rep_i));
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.left.add(sum_i1).add(rep_i), xi_fms,
            padding.left.add(inner.max.width),
        );
        T::axiom_le_transitive(
            layout.children[i].x.add(cn[i].size.width),
            xi_fms,
            padding.left.add(inner.max.width),
        );
        T::axiom_le_transitive(
            layout.children[i].x.add(cn[i].size.width),
            padding.left.add(inner.max.width),
            limits.max.width,
        );

        // Connect cn[i].size to child_cross_sizes[i]
        assert(child_cross_sizes[i] === cn[i].size.height);
    };

    crate::layout::proofs::lemma_merge_layout_cwb(layout, cn);
}

} // verus!
