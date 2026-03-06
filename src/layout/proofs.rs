use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::convex::{two, lemma_two_nonzero};
use verus_algebra::min_max::*;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::flex::*;
use crate::layout::grid::*;
use crate::layout::wrap::*;
use crate::layout::absolute::*;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};
use crate::widget::*;

verus! {

// ── Limits resolve lemmas ───────────────────────────────────────────

/// Resolved width is >= min width.
pub proof fn lemma_resolve_ge_min_width<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
    ensures
        limits.min.width.le(limits.resolve(size).width),
{
    // resolve(size).width = max(min_w, min(size.width, max_w))
    // max(min_w, _) >= min_w
    lemma_max_ge_left::<T>(limits.min.width, min::<T>(size.width, limits.max.width));
}

/// Resolved width is <= max width.
pub proof fn lemma_resolve_le_max_width<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
    ensures
        limits.resolve(size).width.le(limits.max.width),
{
    // min(size.width, max_w) <= max_w
    lemma_min_le_right::<T>(size.width, limits.max.width);
    // max(min_w, min(size.width, max_w)) <= max_w ?
    // We need: max(min_w, X) <= max_w where X <= max_w and min_w <= max_w
    // If min_w <= X: max = X <= max_w. If X < min_w: max = min_w <= max_w.
    T::axiom_le_total(limits.min.width, min::<T>(size.width, limits.max.width));
    if limits.min.width.le(min::<T>(size.width, limits.max.width)) {
        // max = min(size.width, max_w), which is <= max_w
    } else {
        // max = min_w, which is <= max_w by wf
    }
}

/// Resolved height is >= min height.
pub proof fn lemma_resolve_ge_min_height<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
    ensures
        limits.min.height.le(limits.resolve(size).height),
{
    lemma_max_ge_left::<T>(limits.min.height, min::<T>(size.height, limits.max.height));
}

/// Resolved height is <= max height.
pub proof fn lemma_resolve_le_max_height<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
    ensures
        limits.resolve(size).height.le(limits.max.height),
{
    lemma_min_le_right::<T>(size.height, limits.max.height);
    T::axiom_le_total(limits.min.height, min::<T>(size.height, limits.max.height));
}

/// Combined: resolve produces a size within [min, max].
pub proof fn lemma_resolve_bounds<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
    ensures
        limits.min.le(limits.resolve(size)),
        limits.resolve(size).le(limits.max),
{
    lemma_resolve_ge_min_width(limits, size);
    lemma_resolve_le_max_width(limits, size);
    lemma_resolve_ge_min_height(limits, size);
    lemma_resolve_le_max_height(limits, size);
}

// ── Column: children non-overlapping ────────────────────────────────

/// In a column layout, consecutive children do not overlap vertically:
/// child_y(i) + child_sizes[i].height + spacing == child_y(i+1).
///
/// This holds by construction of child_y_position.
pub proof fn lemma_column_children_nonoverlapping<T: OrderedRing>(
    padding_top: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
)
    requires
        (i + 1) < child_sizes.len(),
        T::zero().le(spacing),
    ensures
        child_y_position(padding_top, child_sizes, spacing, i)
            .add(child_sizes[i as int].height)
            .le(
                child_y_position(padding_top, child_sizes, spacing, i + 1)
            ),
{
    // By definition: child_y(i+1) = child_y(i) + child_sizes[i].height + spacing
    // We need: x <= x + spacing where x = child_y(i) + child_sizes[i].height
    // This follows from 0 <= spacing via add_monotone.
    let x = child_y_position(padding_top, child_sizes, spacing, i)
        .add(child_sizes[i as int].height);

    // Step 1: 0 <= spacing => 0 + x <= spacing + x
    T::axiom_le_add_monotone(T::zero(), spacing, x);

    // Step 2: 0 + x ≡ x (via commutativity and zero identity)
    T::axiom_add_commutative(T::zero(), x);
    T::axiom_add_zero_right(x);
    T::axiom_eqv_transitive(T::zero().add(x), x.add(T::zero()), x);

    // Step 3: spacing + x ≡ x + spacing
    T::axiom_add_commutative(spacing, x);

    // Step 4: congruence gives x <= x + spacing
    T::axiom_le_congruence(
        T::zero().add(x), x,
        spacing.add(x), x.add(spacing),
    );
}

// ── Column: total allocation ────────────────────────────────────────

/// repeated_add(val, 0) == zero.
pub proof fn lemma_repeated_add_zero<T: OrderedRing>(val: T)
    ensures
        repeated_add(val, 0).eqv(T::zero()),
{
    T::axiom_eqv_reflexive(T::zero());
}

/// sum_heights(sizes, 0) == zero.
pub proof fn lemma_sum_heights_zero<T: OrderedRing>(sizes: Seq<Size<T>>)
    ensures
        sum_heights(sizes, 0).eqv(T::zero()),
{
    T::axiom_eqv_reflexive(T::zero());
}

/// 0 <= spacing implies 0 <= repeated_add(spacing, n).
pub proof fn lemma_repeated_add_nonneg<T: OrderedRing>(val: T, n: nat)
    requires
        T::zero().le(val),
    ensures
        T::zero().le(repeated_add(val, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_repeated_add_nonneg(val, (n - 1) as nat);
        // 0 <= repeated_add(val, n-1) and 0 <= val
        // repeated_add(val, n) = repeated_add(val, n-1) + val
        // 0 + 0 <= repeated_add(val, n-1) + val
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), repeated_add(val, (n - 1) as nat),
            T::zero(), val,
        );
        // 0 + 0 ≡ 0
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        T::axiom_eqv_reflexive(repeated_add(val, (n - 1) as nat).add(val));
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            repeated_add(val, (n - 1) as nat).add(val),
            repeated_add(val, (n - 1) as nat).add(val),
        );
    }
}

/// If all child heights are non-negative, then sum_heights(sizes, n) is non-negative.
pub proof fn lemma_sum_heights_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].height),
    ensures
        T::zero().le(sum_heights(sizes, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_heights_nonneg(sizes, (n - 1) as nat);
        // 0 <= sum_heights(sizes, n-1) and 0 <= sizes[n-1].height
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_heights(sizes, (n - 1) as nat),
            T::zero(), sizes[(n - 1) as int].height,
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        T::axiom_eqv_reflexive(
            sum_heights(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].height)
        );
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            sum_heights(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].height),
            sum_heights(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].height),
        );
    }
}

/// The column content height is non-negative when spacing and all child heights
/// are non-negative.
pub proof fn lemma_column_content_height_nonneg<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
)
    requires
        T::zero().le(spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> T::zero().le(child_sizes[i].height),
    ensures
        T::zero().le(column_content_height(child_sizes, spacing)),
{
    if child_sizes.len() == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_heights_nonneg(child_sizes, child_sizes.len() as nat);
        lemma_repeated_add_nonneg(spacing, (child_sizes.len() - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_heights(child_sizes, child_sizes.len() as nat),
            T::zero(), repeated_add(spacing, (child_sizes.len() - 1) as nat),
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        let total = sum_heights(child_sizes, child_sizes.len() as nat)
            .add(repeated_add(spacing, (child_sizes.len() - 1) as nat));
        T::axiom_eqv_reflexive(total);
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            total, total,
        );
    }
}

// ── Row: children non-overlapping ───────────────────────────────────

/// In a row layout, consecutive children do not overlap horizontally:
/// child_x(i) + child_sizes[i].width <= child_x(i+1).
pub proof fn lemma_row_children_nonoverlapping<T: OrderedRing>(
    padding_left: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
)
    requires
        (i + 1) < child_sizes.len(),
        T::zero().le(spacing),
    ensures
        child_x_position(padding_left, child_sizes, spacing, i)
            .add(child_sizes[i as int].width)
            .le(
                child_x_position(padding_left, child_sizes, spacing, i + 1)
            ),
{
    // By definition: child_x(i+1) = child_x(i) + child_sizes[i].width + spacing
    // We need: x <= x + spacing where x = child_x(i) + child_sizes[i].width
    let x = child_x_position(padding_left, child_sizes, spacing, i)
        .add(child_sizes[i as int].width);

    // Step 1: 0 <= spacing => 0 + x <= spacing + x
    T::axiom_le_add_monotone(T::zero(), spacing, x);

    // Step 2: 0 + x ≡ x
    T::axiom_add_commutative(T::zero(), x);
    T::axiom_add_zero_right(x);
    T::axiom_eqv_transitive(T::zero().add(x), x.add(T::zero()), x);

    // Step 3: spacing + x ≡ x + spacing
    T::axiom_add_commutative(spacing, x);

    // Step 4: congruence gives x <= x + spacing
    T::axiom_le_congruence(
        T::zero().add(x), x,
        spacing.add(x), x.add(spacing),
    );
}

// ── Helper: adding a non-negative value ───────────────────────────

/// If 0 <= val, then x <= x + val.
pub proof fn lemma_le_add_nonneg<T: OrderedRing>(x: T, val: T)
    requires
        T::zero().le(val),
    ensures
        x.le(x.add(val)),
{
    T::axiom_le_reflexive(x);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        x, x, T::zero(), val,
    );
    // x + 0 <= x + val
    T::axiom_add_zero_right(x);
    // x + 0 ≡ x
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        x.add(T::zero()), x, x.add(val),
    );
}

// ── Alignment offset lemmas ───────────────────────────────────────

/// 0 < two() in any ordered field.
proof fn lemma_two_positive<T: OrderedField>()
    ensures
        T::zero().lt(two::<T>()),
{
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_zero_lt_one::<T>();
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), T::one());
    // 0 < 1 and 0 <= 1 => 0 < 1 + 1
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(T::one(), T::one());
}

/// zero / two() ≡ zero.
proof fn lemma_zero_div_two<T: OrderedField>()
    ensures
        T::zero().div(two::<T>()).eqv(T::zero()),
{
    T::axiom_div_is_mul_recip(T::zero(), two::<T>());
    verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(two::<T>().recip());
    T::axiom_eqv_transitive(
        T::zero().div(two::<T>()),
        T::zero().mul(two::<T>().recip()),
        T::zero(),
    );
}

/// a ≡ b implies a/c ≡ b/c.
proof fn lemma_div_congruence_numerator<T: OrderedField>(a: T, b: T, c: T)
    requires
        a.eqv(b),
    ensures
        a.div(c).eqv(b.div(c)),
{
    T::axiom_div_is_mul_recip(a, c);
    T::axiom_mul_congruence_left(a, b, c.recip());
    T::axiom_eqv_transitive(a.div(c), a.mul(c.recip()), b.mul(c.recip()));
    T::axiom_div_is_mul_recip(b, c);
    T::axiom_eqv_symmetric(b.div(c), b.mul(c.recip()));
    T::axiom_eqv_transitive(a.div(c), b.mul(c.recip()), b.div(c));
}

/// align_offset produces a non-negative offset when the child fits.
pub proof fn lemma_align_offset_nonneg<T: OrderedField>(
    alignment: Alignment,
    available: T,
    used: T,
)
    requires
        used.le(available),
    ensures
        T::zero().le(align_offset(alignment, available, used)),
{
    match alignment {
        Alignment::Start => {
            T::axiom_le_reflexive(T::zero());
        },
        Alignment::Center => {
            let x = available.sub(used);
            // 0 <= x
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<T>(
                used, available,
            );
            // 0 < two()
            lemma_two_positive::<T>();
            // 0 <= x and 0 < two() => 0/two() <= x/two()
            verus_algebra::lemmas::ordered_field_lemmas::lemma_le_div_monotone::<T>(
                T::zero(), x, two::<T>(),
            );
            // 0/two() ≡ 0
            lemma_zero_div_two::<T>();
            // 0 <= x/two()
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().div(two::<T>()), T::zero(), x.div(two::<T>()),
            );
        },
        Alignment::End => {
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<T>(
                used, available,
            );
        },
    }
}

/// align_offset(alignment, available, used) + used <= available
/// when the child fits in the available space.
pub proof fn lemma_align_offset_bounded<T: OrderedField>(
    alignment: Alignment,
    available: T,
    used: T,
)
    requires
        used.le(available),
    ensures
        align_offset(alignment, available, used).add(used).le(available),
{
    match alignment {
        Alignment::Start => {
            // align_offset = 0, so need 0 + used <= available
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(used);
            T::axiom_eqv_symmetric(T::zero().add(used), used);
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                used, T::zero().add(used), available,
            );
        },
        Alignment::Center => {
            let x = available.sub(used);
            // 0 <= x
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg::<T>(
                used, available,
            );

            // midpoint(0, x) <= x via lemma_midpoint_between
            verus_algebra::convex::lemma_midpoint_between::<T>(T::zero(), x);
            // midpoint(0, x) = (0 + x) / two() by definition
            // Need: (0+x)/two() ≡ x/two() via add_zero_left congruence
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(x);
            lemma_div_congruence_numerator::<T>(T::zero().add(x), x, two::<T>());
            // midpoint(0, x) ≡ x/two(), and midpoint(0, x) <= x
            // So x/two() <= x
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                verus_algebra::convex::midpoint::<T>(T::zero(), x),
                x.div(two::<T>()),
                x,
            );

            // x/two() <= x => x/two() + used <= x + used
            T::axiom_le_add_monotone(x.div(two::<T>()), x, used);

            // x + used ≡ available
            verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
                available, used,
            );
            // x/two() + used <= available
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                x.div(two::<T>()).add(used), x.add(used), available,
            );
        },
        Alignment::End => {
            // align_offset = available - used
            // (available - used) + used ≡ available
            verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
                available, used,
            );
            T::axiom_le_reflexive(available);
            T::axiom_eqv_symmetric(available.sub(used).add(used), available);
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                available, available.sub(used).add(used), available,
            );
        },
    }
}

// ── Column: cross-axis containment ────────────────────────────────

/// In a column layout, each child's x-position is >= padding_left.
///
/// Precondition: the child's width fits within the available width.
pub proof fn lemma_column_child_x_lower_bound<T: OrderedField>(
    padding_left: T,
    alignment: Alignment,
    available_width: T,
    child_width: T,
)
    requires
        child_width.le(available_width),
    ensures
        padding_left.le(
            padding_left.add(align_offset(alignment, available_width, child_width))
        ),
{
    lemma_align_offset_nonneg(alignment, available_width, child_width);
    lemma_le_add_nonneg(padding_left, align_offset(alignment, available_width, child_width));
}

/// In a column layout, each child's right edge <= padding_left + available_width.
///
/// Precondition: the child's width fits within the available width.
pub proof fn lemma_column_child_x_upper_bound<T: OrderedField>(
    padding_left: T,
    alignment: Alignment,
    available_width: T,
    child_width: T,
)
    requires
        child_width.le(available_width),
    ensures
        padding_left.add(align_offset(alignment, available_width, child_width))
            .add(child_width)
            .le(padding_left.add(available_width)),
{
    let offset = align_offset(alignment, available_width, child_width);

    // offset + child_width <= available_width
    lemma_align_offset_bounded(alignment, available_width, child_width);

    // (offset + w) + p_l <= aw + p_l
    T::axiom_le_add_monotone(offset.add(child_width), available_width, padding_left);

    // Commute both sides to get p_l + (offset + w) <= p_l + aw
    T::axiom_add_commutative(offset.add(child_width), padding_left);
    T::axiom_add_commutative(available_width, padding_left);
    T::axiom_le_congruence(
        offset.add(child_width).add(padding_left),
        padding_left.add(offset.add(child_width)),
        available_width.add(padding_left),
        padding_left.add(available_width),
    );

    // (p_l + offset) + w ≡ p_l + (offset + w) by associativity
    T::axiom_add_associative(padding_left, offset, child_width);
    // symmetric: p_l + (offset + w) ≡ (p_l + offset) + w
    T::axiom_eqv_symmetric(
        padding_left.add(offset).add(child_width),
        padding_left.add(offset.add(child_width)),
    );

    // (p_l + offset) + w <= p_l + aw
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        padding_left.add(offset.add(child_width)),
        padding_left.add(offset).add(child_width),
        padding_left.add(available_width),
    );
}

// ── Column: layout-axis lower bound ──────────────────────────────

/// In a column layout, each child's y-position is >= padding_top.
pub proof fn lemma_column_child_y_lower_bound<T: OrderedRing>(
    padding_top: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
)
    requires
        i < child_sizes.len(),
        T::zero().le(spacing),
        forall|j: int| 0 <= j < child_sizes.len() ==> T::zero().le(child_sizes[j].height),
    ensures
        padding_top.le(child_y_position(padding_top, child_sizes, spacing, i)),
    decreases i,
{
    if i == 0 {
        // child_y(0) = padding_top
        T::axiom_le_reflexive(padding_top);
    } else {
        // IH: padding_top <= child_y(i-1)
        lemma_column_child_y_lower_bound(padding_top, child_sizes, spacing, (i - 1) as nat);
        let y_prev = child_y_position(padding_top, child_sizes, spacing, (i - 1) as nat);
        let h = child_sizes[(i - 1) as int].height;

        // y_prev <= y_prev + h (since 0 <= h)
        lemma_le_add_nonneg(y_prev, h);
        // y_prev + h <= (y_prev + h) + spacing (since 0 <= spacing)
        lemma_le_add_nonneg(y_prev.add(h), spacing);

        // chain: y_prev <= y_prev + h <= child_y(i)
        T::axiom_le_transitive(y_prev, y_prev.add(h), y_prev.add(h).add(spacing));
        // chain: padding_top <= y_prev <= child_y(i)
        T::axiom_le_transitive(padding_top, y_prev, y_prev.add(h).add(spacing));
    }
}

// ── Row: cross-axis containment ──────────────────────────────────

/// In a row layout, each child's y-position is >= padding_top.
pub proof fn lemma_row_child_y_lower_bound<T: OrderedField>(
    padding_top: T,
    alignment: Alignment,
    available_height: T,
    child_height: T,
)
    requires
        child_height.le(available_height),
    ensures
        padding_top.le(
            padding_top.add(align_offset(alignment, available_height, child_height))
        ),
{
    lemma_align_offset_nonneg(alignment, available_height, child_height);
    lemma_le_add_nonneg(padding_top, align_offset(alignment, available_height, child_height));
}

/// In a row layout, each child's bottom edge <= padding_top + available_height.
pub proof fn lemma_row_child_y_upper_bound<T: OrderedField>(
    padding_top: T,
    alignment: Alignment,
    available_height: T,
    child_height: T,
)
    requires
        child_height.le(available_height),
    ensures
        padding_top.add(align_offset(alignment, available_height, child_height))
            .add(child_height)
            .le(padding_top.add(available_height)),
{
    let offset = align_offset(alignment, available_height, child_height);

    lemma_align_offset_bounded(alignment, available_height, child_height);

    T::axiom_le_add_monotone(offset.add(child_height), available_height, padding_top);

    T::axiom_add_commutative(offset.add(child_height), padding_top);
    T::axiom_add_commutative(available_height, padding_top);
    T::axiom_le_congruence(
        offset.add(child_height).add(padding_top),
        padding_top.add(offset.add(child_height)),
        available_height.add(padding_top),
        padding_top.add(available_height),
    );

    T::axiom_add_associative(padding_top, offset, child_height);
    T::axiom_eqv_symmetric(
        padding_top.add(offset).add(child_height),
        padding_top.add(offset.add(child_height)),
    );

    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        padding_top.add(offset.add(child_height)),
        padding_top.add(offset).add(child_height),
        padding_top.add(available_height),
    );
}

// ── Row: layout-axis lower bound ─────────────────────────────────

/// In a row layout, each child's x-position is >= padding_left.
pub proof fn lemma_row_child_x_lower_bound<T: OrderedRing>(
    padding_left: T,
    child_sizes: Seq<Size<T>>,
    spacing: T,
    i: nat,
)
    requires
        i < child_sizes.len(),
        T::zero().le(spacing),
        forall|j: int| 0 <= j < child_sizes.len() ==> T::zero().le(child_sizes[j].width),
    ensures
        padding_left.le(child_x_position(padding_left, child_sizes, spacing, i)),
    decreases i,
{
    if i == 0 {
        T::axiom_le_reflexive(padding_left);
    } else {
        lemma_row_child_x_lower_bound(padding_left, child_sizes, spacing, (i - 1) as nat);
        let x_prev = child_x_position(padding_left, child_sizes, spacing, (i - 1) as nat);
        let w = child_sizes[(i - 1) as int].width;

        lemma_le_add_nonneg(x_prev, w);
        lemma_le_add_nonneg(x_prev.add(w), spacing);

        T::axiom_le_transitive(x_prev, x_prev.add(w), x_prev.add(w).add(spacing));
        T::axiom_le_transitive(padding_left, x_prev, x_prev.add(w).add(spacing));
    }
}

// ── Helpers for rearrangement ─────────────────────────────────────

/// (a + b) + c ≡ (a + c) + b — swap the last two addends.
pub proof fn lemma_add_swap_last<T: OrderedRing>(a: T, b: T, c: T)
    ensures
        a.add(b).add(c).eqv(a.add(c).add(b)),
{
    T::axiom_add_associative(a, b, c);
    T::axiom_add_commutative(b, c);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, b.add(c), c.add(b),
    );
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(b.add(c)), a.add(c.add(b)));
    T::axiom_add_associative(a, c, b);
    T::axiom_eqv_symmetric(a.add(c).add(b), a.add(c.add(b)));
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(c.add(b)), a.add(c).add(b));
}

// ── Monotonicity lemmas ──────────────────────────────────────────

/// sum_heights is monotone: i <= j implies sum_heights(sizes, i) <= sum_heights(sizes, j).
pub proof fn lemma_sum_heights_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        sum_heights(sizes, i).le(sum_heights(sizes, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(sum_heights(sizes, i));
    } else {
        lemma_sum_heights_monotone(sizes, i, (j - 1) as nat);
        lemma_le_add_nonneg(
            sum_heights(sizes, (j - 1) as nat),
            sizes[(j - 1) as int].height,
        );
        T::axiom_le_transitive(
            sum_heights(sizes, i),
            sum_heights(sizes, (j - 1) as nat),
            sum_heights(sizes, (j - 1) as nat).add(sizes[(j - 1) as int].height),
        );
    }
}

/// repeated_add is monotone: i <= j and 0 <= val implies
/// repeated_add(val, i) <= repeated_add(val, j).
pub proof fn lemma_repeated_add_monotone<T: OrderedRing>(
    val: T,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        T::zero().le(val),
    ensures
        repeated_add(val, i).le(repeated_add(val, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(repeated_add(val, i));
    } else {
        lemma_repeated_add_monotone(val, i, (j - 1) as nat);
        lemma_le_add_nonneg(repeated_add(val, (j - 1) as nat), val);
        T::axiom_le_transitive(
            repeated_add(val, i),
            repeated_add(val, (j - 1) as nat),
            repeated_add(val, (j - 1) as nat).add(val),
        );
    }
}

/// sum_widths is monotone: i <= j implies sum_widths(sizes, i) <= sum_widths(sizes, j).
pub proof fn lemma_sum_widths_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        sum_widths(sizes, i).le(sum_widths(sizes, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(sum_widths(sizes, i));
    } else {
        lemma_sum_widths_monotone(sizes, i, (j - 1) as nat);
        lemma_le_add_nonneg(
            sum_widths(sizes, (j - 1) as nat),
            sizes[(j - 1) as int].width,
        );
        T::axiom_le_transitive(
            sum_widths(sizes, i),
            sum_widths(sizes, (j - 1) as nat),
            sum_widths(sizes, (j - 1) as nat).add(sizes[(j - 1) as int].width),
        );
    }
}

// ── Position identity lemmas ─────────────────────────────────────

/// child_y_position(pt, sizes, sp, i) ≡ pt + sum_heights(sizes, i) + repeated_add(sp, i).
pub proof fn lemma_child_y_position_identity<T: OrderedRing>(
    pt: T,
    sizes: Seq<Size<T>>,
    sp: T,
    i: nat,
)
    requires
        i <= sizes.len(),
    ensures
        child_y_position(pt, sizes, sp, i).eqv(
            pt.add(sum_heights(sizes, i)).add(repeated_add(sp, i))
        ),
    decreases i,
{
    if i == 0 {
        // child_y(0) = pt, RHS = pt + 0 + 0
        // pt ≡ pt + 0
        T::axiom_add_zero_right(pt);
        T::axiom_eqv_symmetric(pt.add(T::zero()), pt);
        // pt + 0 ≡ (pt + 0) + 0
        T::axiom_add_zero_right(pt.add(T::zero()));
        T::axiom_eqv_symmetric(
            pt.add(T::zero()).add(T::zero()),
            pt.add(T::zero()),
        );
        // pt ≡ (pt + 0) + 0
        T::axiom_eqv_transitive(
            pt,
            pt.add(T::zero()),
            pt.add(T::zero()).add(T::zero()),
        );
    } else {
        // IH: child_y(i-1) ≡ pt + SH(i-1) + RA(i-1)
        lemma_child_y_position_identity(pt, sizes, sp, (i - 1) as nat);

        let prev = child_y_position(pt, sizes, sp, (i - 1) as nat);
        let sh = sum_heights(sizes, (i - 1) as nat);
        let ra = repeated_add(sp, (i - 1) as nat);
        let h = sizes[(i - 1) as int].height;

        // child_y(i) = prev + h + sp [by definition]
        // prev ≡ pt + sh + ra [IH]

        // A: prev + h ≡ (pt + sh + ra) + h [congruence from IH]
        T::axiom_add_congruence_left(prev, pt.add(sh).add(ra), h);
        // B: (prev + h) + sp ≡ ((pt + sh + ra) + h) + sp [congruence]
        T::axiom_add_congruence_left(prev.add(h), pt.add(sh).add(ra).add(h), sp);

        // C: ((pt+sh+ra)+h)+sp ≡ (pt+sh+ra)+(h+sp) [assoc]
        T::axiom_add_associative(pt.add(sh).add(ra), h, sp);
        // D: (pt+sh+ra)+(h+sp) ≡ ((pt+sh)+h)+(ra+sp) [rearrange]
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
            pt.add(sh), ra, h, sp,
        );
        // E: (pt+sh)+h ≡ pt+(sh+h) [assoc]
        T::axiom_add_associative(pt, sh, h);
        // F: ((pt+sh)+h)+(ra+sp) ≡ (pt+(sh+h))+(ra+sp) [congruence]
        T::axiom_add_congruence_left(
            pt.add(sh).add(h), pt.add(sh.add(h)), ra.add(sp),
        );

        // Chain C→D→F:
        T::axiom_eqv_transitive(
            pt.add(sh).add(ra).add(h).add(sp),
            pt.add(sh).add(ra).add(h.add(sp)),
            pt.add(sh).add(h).add(ra.add(sp)),
        );
        T::axiom_eqv_transitive(
            pt.add(sh).add(ra).add(h).add(sp),
            pt.add(sh).add(h).add(ra.add(sp)),
            pt.add(sh.add(h)).add(ra.add(sp)),
        );

        // Full: child_y(i) = prev+h+sp ≡ ((pt+sh+ra)+h)+sp ≡ pt+(sh+h)+(ra+sp)
        T::axiom_eqv_transitive(
            prev.add(h).add(sp),
            pt.add(sh).add(ra).add(h).add(sp),
            pt.add(sh.add(h)).add(ra.add(sp)),
        );
        // sh+h = sum_heights(i), ra+sp = repeated_add(sp, i) by definition
    }
}

/// child_x_position(pl, sizes, sp, i) ≡ pl + sum_widths(sizes, i) + repeated_add(sp, i).
pub proof fn lemma_child_x_position_identity<T: OrderedRing>(
    pl: T,
    sizes: Seq<Size<T>>,
    sp: T,
    i: nat,
)
    requires
        i <= sizes.len(),
    ensures
        child_x_position(pl, sizes, sp, i).eqv(
            pl.add(sum_widths(sizes, i)).add(repeated_add(sp, i))
        ),
    decreases i,
{
    if i == 0 {
        T::axiom_add_zero_right(pl);
        T::axiom_eqv_symmetric(pl.add(T::zero()), pl);
        T::axiom_add_zero_right(pl.add(T::zero()));
        T::axiom_eqv_symmetric(
            pl.add(T::zero()).add(T::zero()),
            pl.add(T::zero()),
        );
        T::axiom_eqv_transitive(
            pl,
            pl.add(T::zero()),
            pl.add(T::zero()).add(T::zero()),
        );
    } else {
        lemma_child_x_position_identity(pl, sizes, sp, (i - 1) as nat);

        let prev = child_x_position(pl, sizes, sp, (i - 1) as nat);
        let sw = sum_widths(sizes, (i - 1) as nat);
        let ra = repeated_add(sp, (i - 1) as nat);
        let w = sizes[(i - 1) as int].width;

        T::axiom_add_congruence_left(prev, pl.add(sw).add(ra), w);
        T::axiom_add_congruence_left(prev.add(w), pl.add(sw).add(ra).add(w), sp);

        T::axiom_add_associative(pl.add(sw).add(ra), w, sp);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
            pl.add(sw), ra, w, sp,
        );
        T::axiom_add_associative(pl, sw, w);
        T::axiom_add_congruence_left(
            pl.add(sw).add(w), pl.add(sw.add(w)), ra.add(sp),
        );

        T::axiom_eqv_transitive(
            pl.add(sw).add(ra).add(w).add(sp),
            pl.add(sw).add(ra).add(w.add(sp)),
            pl.add(sw).add(w).add(ra.add(sp)),
        );
        T::axiom_eqv_transitive(
            pl.add(sw).add(ra).add(w).add(sp),
            pl.add(sw).add(w).add(ra.add(sp)),
            pl.add(sw.add(w)).add(ra.add(sp)),
        );

        T::axiom_eqv_transitive(
            prev.add(w).add(sp),
            pl.add(sw).add(ra).add(w).add(sp),
            pl.add(sw.add(w)).add(ra.add(sp)),
        );
    }
}

// ── Column: layout-axis upper bound ──────────────────────────────

/// In a column layout, each child's bottom edge is within the content area:
/// child_y(i) + sizes[i].height <= pt + column_content_height(sizes, sp).
pub proof fn lemma_column_child_y_upper_bound<T: OrderedRing>(
    pt: T,
    sizes: Seq<Size<T>>,
    sp: T,
    i: nat,
)
    requires
        sizes.len() > 0,
        i < sizes.len(),
        T::zero().le(sp),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].height),
    ensures
        child_y_position(pt, sizes, sp, i)
            .add(sizes[i as int].height)
            .le(pt.add(column_content_height(sizes, sp))),
{
    let n = sizes.len() as nat;
    let h = sizes[i as int].height;

    // A: child_y(i) ≡ pt + sum_heights(i) + repeated_add(sp, i)
    lemma_child_y_position_identity(pt, sizes, sp, i);

    // B: child_y(i) + h ≡ (pt + SH(i) + RA(i)) + h
    T::axiom_add_congruence_left(
        child_y_position(pt, sizes, sp, i),
        pt.add(sum_heights(sizes, i)).add(repeated_add(sp, i)),
        h,
    );

    // C: Rearrange (pt + SH + RA) + h to (pt + SH(i+1)) + RA(i)
    //    using swap_last then associativity
    lemma_add_swap_last(pt.add(sum_heights(sizes, i)), repeated_add(sp, i), h);
    T::axiom_add_associative(pt, sum_heights(sizes, i), h);
    T::axiom_add_congruence_left(
        pt.add(sum_heights(sizes, i)).add(h),
        pt.add(sum_heights(sizes, i).add(h)),
        repeated_add(sp, i),
    );
    T::axiom_eqv_transitive(
        pt.add(sum_heights(sizes, i)).add(repeated_add(sp, i)).add(h),
        pt.add(sum_heights(sizes, i)).add(h).add(repeated_add(sp, i)),
        pt.add(sum_heights(sizes, i).add(h)).add(repeated_add(sp, i)),
    );

    // D: child_y(i) + h ≡ pt + SH(i+1) + RA(i)
    //    (since sum_heights(i).add(h) = sum_heights(i+1) by definition)
    T::axiom_eqv_transitive(
        child_y_position(pt, sizes, sp, i).add(h),
        pt.add(sum_heights(sizes, i)).add(repeated_add(sp, i)).add(h),
        pt.add(sum_heights(sizes, i).add(h)).add(repeated_add(sp, i)),
    );

    // E: SH(i+1) <= SH(n)
    lemma_sum_heights_monotone(sizes, (i + 1) as nat, n);

    // F: RA(i) <= RA(n-1)
    lemma_repeated_add_monotone(sp, i, (n - 1) as nat);

    // G: SH(i+1) + RA(i) <= SH(n) + RA(n-1) = column_content_height
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        sum_heights(sizes, (i + 1) as nat), sum_heights(sizes, n),
        repeated_add(sp, i), repeated_add(sp, (n - 1) as nat),
    );

    // H: pt + (SH(i+1) + RA(i)) <= pt + (SH(n) + RA(n-1))
    T::axiom_le_add_monotone(
        sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i)),
        sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat)),
        pt,
    );
    T::axiom_add_commutative(
        sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i)), pt,
    );
    T::axiom_add_commutative(
        sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat)), pt,
    );
    T::axiom_le_congruence(
        sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i)).add(pt),
        pt.add(sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
        sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat)).add(pt),
        pt.add(sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );

    // I: Relate pt + SH(i+1) + RA(i) to pt + (SH(i+1) + RA(i)) via assoc
    T::axiom_add_associative(
        pt,
        sum_heights(sizes, (i + 1) as nat),
        repeated_add(sp, i),
    );
    T::axiom_eqv_symmetric(
        pt.add(sum_heights(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        pt.add(sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        pt.add(sum_heights(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
        pt.add(sum_heights(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        pt.add(sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );
    // Now: pt + SH(i+1) + RA(i) <= pt + (SH(n) + RA(n-1))

    // J: child_y(i)+h ≡ pt+SH(i+1)+RA(i), apply congruence to get final le
    //    (sum_heights(i).add(h) = sum_heights(i+1) by definition)
    T::axiom_eqv_symmetric(
        child_y_position(pt, sizes, sp, i).add(h),
        pt.add(sum_heights(sizes, i).add(h)).add(repeated_add(sp, i)),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        pt.add(sum_heights(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        child_y_position(pt, sizes, sp, i).add(h),
        pt.add(sum_heights(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );
    // pt.add(SH(n).add(RA(n-1))) = pt.add(column_content_height) by definition
}

// ── Row: layout-axis upper bound ─────────────────────────────────

/// In a row layout, each child's right edge is within the content area:
/// child_x(i) + sizes[i].width <= pl + row_content_width(sizes, sp).
pub proof fn lemma_row_child_x_upper_bound<T: OrderedRing>(
    pl: T,
    sizes: Seq<Size<T>>,
    sp: T,
    i: nat,
)
    requires
        sizes.len() > 0,
        i < sizes.len(),
        T::zero().le(sp),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].width),
    ensures
        child_x_position(pl, sizes, sp, i)
            .add(sizes[i as int].width)
            .le(pl.add(row_content_width(sizes, sp))),
{
    let n = sizes.len() as nat;
    let w = sizes[i as int].width;

    lemma_child_x_position_identity(pl, sizes, sp, i);

    T::axiom_add_congruence_left(
        child_x_position(pl, sizes, sp, i),
        pl.add(sum_widths(sizes, i)).add(repeated_add(sp, i)),
        w,
    );

    lemma_add_swap_last(pl.add(sum_widths(sizes, i)), repeated_add(sp, i), w);
    T::axiom_add_associative(pl, sum_widths(sizes, i), w);
    T::axiom_add_congruence_left(
        pl.add(sum_widths(sizes, i)).add(w),
        pl.add(sum_widths(sizes, i).add(w)),
        repeated_add(sp, i),
    );
    T::axiom_eqv_transitive(
        pl.add(sum_widths(sizes, i)).add(repeated_add(sp, i)).add(w),
        pl.add(sum_widths(sizes, i)).add(w).add(repeated_add(sp, i)),
        pl.add(sum_widths(sizes, i).add(w)).add(repeated_add(sp, i)),
    );

    T::axiom_eqv_transitive(
        child_x_position(pl, sizes, sp, i).add(w),
        pl.add(sum_widths(sizes, i)).add(repeated_add(sp, i)).add(w),
        pl.add(sum_widths(sizes, i).add(w)).add(repeated_add(sp, i)),
    );

    lemma_sum_widths_monotone(sizes, (i + 1) as nat, n);
    lemma_repeated_add_monotone(sp, i, (n - 1) as nat);

    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        sum_widths(sizes, (i + 1) as nat), sum_widths(sizes, n),
        repeated_add(sp, i), repeated_add(sp, (n - 1) as nat),
    );

    T::axiom_le_add_monotone(
        sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i)),
        sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat)),
        pl,
    );
    T::axiom_add_commutative(
        sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i)), pl,
    );
    T::axiom_add_commutative(
        sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat)), pl,
    );
    T::axiom_le_congruence(
        sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i)).add(pl),
        pl.add(sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
        sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat)).add(pl),
        pl.add(sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );

    T::axiom_add_associative(
        pl, sum_widths(sizes, (i + 1) as nat), repeated_add(sp, i),
    );
    T::axiom_eqv_symmetric(
        pl.add(sum_widths(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        pl.add(sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        pl.add(sum_widths(sizes, (i + 1) as nat).add(repeated_add(sp, i))),
        pl.add(sum_widths(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        pl.add(sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );

    T::axiom_eqv_symmetric(
        child_x_position(pl, sizes, sp, i).add(w),
        pl.add(sum_widths(sizes, i).add(w)).add(repeated_add(sp, i)),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        pl.add(sum_widths(sizes, (i + 1) as nat)).add(repeated_add(sp, i)),
        child_x_position(pl, sizes, sp, i).add(w),
        pl.add(sum_widths(sizes, n).add(repeated_add(sp, (n - 1) as nat))),
    );
}

// ── Children sequence lemmas ──────────────────────────────────────

/// Length of column_children sequence.
pub proof fn lemma_column_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    index: nat,
)
    requires
        index <= child_sizes.len(),
    ensures
        column_children(padding, spacing, alignment, child_sizes, available_width, index).len()
            == child_sizes.len() - index,
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
    } else {
        lemma_column_children_len(padding, spacing, alignment, child_sizes, available_width, index + 1);
    }
}

/// Element access into column_children: the k-th child (from start) has the expected fields.
pub proof fn lemma_column_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    k: nat,
)
    requires
        k < child_sizes.len(),
    ensures
        column_children(padding, spacing, alignment, child_sizes, available_width, 0)[k as int]
            == crate::node::Node::leaf(
                padding.left.add(align_offset(alignment, available_width, child_sizes[k as int].width)),
                child_y_position(padding.top, child_sizes, spacing, k),
                child_sizes[k as int],
            ),
{
    lemma_column_children_element_shifted(padding, spacing, alignment, child_sizes, available_width, 0, k);
}

/// Helper: column_children(pad, sp, al, sizes, aw, start)[k - start] for start <= k < sizes.len()
proof fn lemma_column_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < child_sizes.len(),
    ensures
        column_children(padding, spacing, alignment, child_sizes, available_width, start)[(k - start) as int]
            == crate::node::Node::leaf(
                padding.left.add(align_offset(alignment, available_width, child_sizes[k as int].width)),
                child_y_position(padding.top, child_sizes, spacing, k),
                child_sizes[k as int],
            ),
    decreases k - start,
{
    if start == k {
        // Base case: one-step unfolding gives column_children(.., k)[0] = node_k
    } else {
        // Establish tail length so axiom_seq_add_index2 precondition is satisfied
        lemma_column_children_len(padding, spacing, alignment, child_sizes, available_width, start + 1);
        lemma_column_children_len(padding, spacing, alignment, child_sizes, available_width, start);

        // Apply induction first
        lemma_column_children_element_shifted(padding, spacing, alignment, child_sizes, available_width, start + 1, k);

        // column_children(.., start) = head.add(tail) where head has length 1
        // For index (k-start) >= 1: element is tail[(k-start) - 1] = tail[(k-(start+1))]
        let tail = column_children(padding, spacing, alignment, child_sizes, available_width, start + 1);
        let cc = column_children(padding, spacing, alignment, child_sizes, available_width, start);
        // cc[k-start] == tail[(k-start) - 1] by axiom_seq_add_index2 (since head.len() == 1)
        assert(cc[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

/// Length of row_children sequence.
pub proof fn lemma_row_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_height: T,
    index: nat,
)
    requires
        index <= child_sizes.len(),
    ensures
        row_children(padding, spacing, alignment, child_sizes, available_height, index).len()
            == child_sizes.len() - index,
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
    } else {
        lemma_row_children_len(padding, spacing, alignment, child_sizes, available_height, index + 1);
    }
}

/// Element access into row_children: the k-th child (from start) has the expected fields.
pub proof fn lemma_row_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_height: T,
    k: nat,
)
    requires
        k < child_sizes.len(),
    ensures
        row_children(padding, spacing, alignment, child_sizes, available_height, 0)[k as int]
            == crate::node::Node::leaf(
                child_x_position(padding.left, child_sizes, spacing, k),
                padding.top.add(align_offset(alignment, available_height, child_sizes[k as int].height)),
                child_sizes[k as int],
            ),
{
    lemma_row_children_element_shifted(padding, spacing, alignment, child_sizes, available_height, 0, k);
}

/// Helper: row_children(pad, sp, al, sizes, ah, start)[k - start] for start <= k < sizes.len()
proof fn lemma_row_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_height: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < child_sizes.len(),
    ensures
        row_children(padding, spacing, alignment, child_sizes, available_height, start)[(k - start) as int]
            == crate::node::Node::leaf(
                child_x_position(padding.left, child_sizes, spacing, k),
                padding.top.add(align_offset(alignment, available_height, child_sizes[k as int].height)),
                child_sizes[k as int],
            ),
    decreases k - start,
{
    if start == k {
        // Base case: one-step unfolding gives row_children(.., k)[0] = node_k
    } else {
        // Establish tail length so axiom_seq_add_index2 precondition is satisfied
        lemma_row_children_len(padding, spacing, alignment, child_sizes, available_height, start + 1);
        lemma_row_children_len(padding, spacing, alignment, child_sizes, available_height, start);

        // Apply induction first
        lemma_row_children_element_shifted(padding, spacing, alignment, child_sizes, available_height, start + 1, k);

        // row_children(.., start) = head.add(tail) where head has length 1
        let tail = row_children(padding, spacing, alignment, child_sizes, available_height, start + 1);
        let rc = row_children(padding, spacing, alignment, child_sizes, available_height, start);
        assert(rc[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

// ── Phase 4: Additional Properties ────────────────────────────────

/// Helper: x/two() + x/two() ≡ x.
/// Proof: (x/2)*2 ≡ x by div_mul_cancel, and (x/2)*2 = (x/2)*(1+1)
/// = (x/2)*1 + (x/2)*1 = x/2 + x/2 by distributivity and mul_one.
proof fn lemma_half_plus_half<T: OrderedField>(x: T)
    ensures
        x.div(two::<T>()).add(x.div(two::<T>())).eqv(x),
{
    let h = x.div(two::<T>());

    // (x/two()) * two() ≡ x
    lemma_two_nonzero::<T>();
    verus_algebra::lemmas::field_lemmas::lemma_div_mul_cancel::<T>(x, two::<T>());
    // h.mul(two()) ≡ x

    // two() = one() + one()
    // h * (one() + one()) ≡ h*one() + h*one() by distributivity
    T::axiom_mul_distributes_left(h, T::one(), T::one());
    // h.mul(T::one().add(T::one())) ≡ h.mul(T::one()).add(h.mul(T::one()))

    // h * one() ≡ h
    T::axiom_mul_one_right(h);
    // So h*one() + h*one() ≡ h + h via congruence
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
        h.mul(T::one()), h, h.mul(T::one()), h,
    );

    // h * two() ≡ h * (one() + one()) by definition (they're equal)
    // and h * (one() + one()) ≡ h*one() + h*one() ≡ h + h
    T::axiom_eqv_transitive(
        h.mul(T::one().add(T::one())),
        h.mul(T::one()).add(h.mul(T::one())),
        h.add(h),
    );
    // h.mul(two()) ≡ h + h (since two() == one() + one())

    // h.mul(two()) ≡ h + h, so h + h ≡ h.mul(two()) by symmetry
    T::axiom_eqv_symmetric(h.mul(two::<T>()), h.add(h));
    // h.mul(two()) ≡ x by div_mul_cancel, flip to get x side
    // h + h ≡ h.mul(two()) ≡ x
    T::axiom_eqv_transitive(h.add(h), h.mul(two::<T>()), x);
}

/// Center alignment is symmetric: the gap on the left equals the gap on the right.
///
/// For Center alignment: align_offset = (available - used) / 2.
/// This lemma proves: align_offset ≡ (available - used) - align_offset,
/// i.e. the child is equidistant from both edges.
pub proof fn lemma_center_alignment_symmetric<T: OrderedField>(
    available: T,
    used: T,
)
    requires
        used.le(available),
    ensures
        align_offset(Alignment::Center, available, used).eqv(
            available.sub(used).sub(align_offset(Alignment::Center, available, used))
        ),
{
    let x = available.sub(used);
    let h = x.div(two::<T>());
    // align_offset(Center, available, used) == h == x / two()

    // h + h ≡ x
    lemma_half_plus_half::<T>(x);

    // (h + h) - h ≡ h  by add_then_sub_cancel
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<T>(h, h);

    // h + h ≡ x, so (h + h) - h ≡ x - h by sub_congruence
    T::axiom_eqv_reflexive(h);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_congruence::<T>(
        h.add(h), x, h, h,
    );

    // (h + h) - h ≡ h, and (h + h) - h ≡ x - h
    // => h ≡ x - h
    T::axiom_eqv_symmetric(h.add(h).sub(h), h);
    T::axiom_eqv_transitive(h, h.add(h).sub(h), x.sub(h));
}

/// Column children are contained within the padded region: both
/// cross-axis and layout-axis bounds hold simultaneously.
///
/// Each child i satisfies:
///   - padding_left <= child_x  (cross-axis lower)
///   - child_x + child_width <= padding_left + available_width  (cross-axis upper)
///   - padding_top <= child_y  (layout-axis lower)
pub proof fn lemma_column_child_contained<T: OrderedField>(
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    i: nat,
)
    requires
        i < child_sizes.len(),
        T::zero().le(spacing),
        forall|j: int| 0 <= j < child_sizes.len() ==> T::zero().le(child_sizes[j].height),
        forall|j: int| 0 <= j < child_sizes.len() ==> child_sizes[j].width.le(available_width),
    ensures
        // Cross-axis lower bound
        padding.left.le(
            padding.left.add(align_offset(alignment, available_width, child_sizes[i as int].width))
        ),
        // Cross-axis upper bound
        padding.left.add(align_offset(alignment, available_width, child_sizes[i as int].width))
            .add(child_sizes[i as int].width)
            .le(padding.left.add(available_width)),
        // Layout-axis lower bound
        padding.top.le(
            child_y_position(padding.top, child_sizes, spacing, i)
        ),
{
    lemma_column_child_x_lower_bound(
        padding.left, alignment, available_width, child_sizes[i as int].width,
    );
    lemma_column_child_x_upper_bound(
        padding.left, alignment, available_width, child_sizes[i as int].width,
    );
    lemma_column_child_y_lower_bound(padding.top, child_sizes, spacing, i);
}

/// Adding a child increases column content height.
///
/// content_height(sizes.push(new_size)) >= content_height(sizes)
/// for non-negative child heights and spacing.
pub proof fn lemma_column_content_height_monotone<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    new_size: Size<T>,
    spacing: T,
)
    requires
        T::zero().le(spacing),
        T::zero().le(new_size.height),
        forall|j: int| 0 <= j < child_sizes.len() ==> T::zero().le(child_sizes[j].height),
    ensures
        column_content_height(child_sizes, spacing).le(
            column_content_height(child_sizes.push(new_size), spacing)
        ),
{
    let n = child_sizes.len();
    let ext = child_sizes.push(new_size);
    assert(ext.len() == n + 1);

    if n == 0 {
        // content_height(empty) = 0, content_height([new]) = new.height + 0
        // Need: 0 <= content_height([new])
        lemma_column_content_height_nonneg(ext, spacing);
    } else {
        // LHS = sum_heights(sizes, n) + repeated_add(spacing, n-1)
        // RHS = sum_heights(ext, n+1) + repeated_add(spacing, n)
        //     = (sum_heights(ext, n) + new.height) + (repeated_add(spacing, n-1) + spacing)
        // Since ext[j] == sizes[j] for j < n:
        //     = (sum_heights(sizes, n) + new.height) + (repeated_add(spacing, n-1) + spacing)
        lemma_sum_heights_ext_equal::<T>(child_sizes, ext, n as nat);

        let sh_n = sum_heights(child_sizes, n as nat);
        let ra_nm1 = repeated_add(spacing, (n - 1) as nat);

        // sh_n <= sh_n + new.height  (new.height >= 0)
        lemma_le_add_nonneg::<T>(sh_n, new_size.height);
        // ra_nm1 <= ra_nm1 + spacing  (spacing >= 0)
        lemma_le_add_nonneg::<T>(ra_nm1, spacing);

        // sh_n + ra_nm1 <= (sh_n + new.height) + (ra_nm1 + spacing)
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            sh_n, sh_n.add(new_size.height),
            ra_nm1, ra_nm1.add(spacing),
        );

        // Assert definitional equalities to help Z3 connect to column_content_height
        assert(column_content_height(child_sizes, spacing) == sh_n.add(ra_nm1));
        assert(sum_heights(ext, (n + 1) as nat) ==
            sum_heights(ext, n as nat).add(ext[n as int].height));
        assert(ext[n as int] == new_size);
        assert(column_content_height(ext, spacing) ==
            sum_heights(ext, (n + 1) as nat).add(repeated_add(spacing, n as nat)));
    }
}

/// Helper: sum_heights gives the same result when the first `count` elements are identical.
proof fn lemma_sum_heights_ext_equal<T: OrderedRing>(
    a: Seq<Size<T>>,
    b: Seq<Size<T>>,
    count: nat,
)
    requires
        count <= a.len(),
        count <= b.len(),
        forall|j: int| 0 <= j < count ==> a[j] == b[j],
    ensures
        sum_heights(a, count) == sum_heights(b, count),
    decreases count,
{
    if count == 0 {
    } else {
        lemma_sum_heights_ext_equal(a, b, (count - 1) as nat);
    }
}

/// Grid 2D non-overlap: consecutive cells don't overlap in both directions.
///
/// Combines column and row non-overlap into a single lemma.
pub proof fn lemma_grid_2d_nonoverlapping<T: OrderedRing>(
    padding_left: T,
    padding_top: T,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    col: nat,
    row: nat,
)
    requires
        (col + 1) < col_widths.len(),
        (row + 1) < row_heights.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
    ensures
        // Columns: right edge of col <= left edge of col+1
        crate::layout::grid::grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width)
            .le(crate::layout::grid::grid_cell_x(padding_left, col_widths, h_spacing, col + 1)),
        // Rows: bottom edge of row <= top edge of row+1
        crate::layout::grid::grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height)
            .le(crate::layout::grid::grid_cell_y(padding_top, row_heights, v_spacing, row + 1)),
{
    crate::layout::grid_proofs::lemma_grid_columns_nonoverlapping(
        padding_left, col_widths, h_spacing, col,
    );
    crate::layout::grid_proofs::lemma_grid_rows_nonoverlapping(
        padding_top, row_heights, v_spacing, row,
    );
}

// ── Stack children helper lemmas ──────────────────────────────────

/// Length of stack_children sequence.
pub proof fn lemma_stack_children_len<T: OrderedField>(
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    available_height: T,
    index: nat,
)
    requires
        index <= child_sizes.len(),
    ensures
        crate::layout::stack::stack_children(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, index,
        ).len() == child_sizes.len() - index,
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
    } else {
        lemma_stack_children_len(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, index + 1,
        );
    }
}

/// Element access into stack_children.
pub proof fn lemma_stack_children_element<T: OrderedField>(
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    available_height: T,
    k: nat,
)
    requires
        k < child_sizes.len(),
    ensures
        crate::layout::stack::stack_children(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, 0,
        )[k as int]
            == crate::node::Node::leaf(
                padding.left.add(align_offset(h_align, available_width, child_sizes[k as int].width)),
                padding.top.add(align_offset(v_align, available_height, child_sizes[k as int].height)),
                child_sizes[k as int],
            ),
{
    lemma_stack_children_element_shifted(
        padding, h_align, v_align, child_sizes,
        available_width, available_height, 0, k,
    );
}

proof fn lemma_stack_children_element_shifted<T: OrderedField>(
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    available_height: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < child_sizes.len(),
    ensures
        crate::layout::stack::stack_children(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start,
        )[(k - start) as int]
            == crate::node::Node::leaf(
                padding.left.add(align_offset(h_align, available_width, child_sizes[k as int].width)),
                padding.top.add(align_offset(v_align, available_height, child_sizes[k as int].height)),
                child_sizes[k as int],
            ),
    decreases k - start,
{
    if start == k {
    } else {
        lemma_stack_children_len(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start + 1,
        );
        lemma_stack_children_len(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start,
        );
        lemma_stack_children_element_shifted(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start + 1, k,
        );
        let tail = crate::layout::stack::stack_children(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start + 1,
        );
        let sc = crate::layout::stack::stack_children(
            padding, h_align, v_align, child_sizes,
            available_width, available_height, start,
        );
        assert(sc[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

// ── Row content width monotone lemma (symmetric to column) ────────

/// Helper: sum_widths gives the same result when the first `count` elements are identical.
proof fn lemma_sum_widths_ext_equal<T: OrderedRing>(
    a: Seq<Size<T>>,
    b: Seq<Size<T>>,
    count: nat,
)
    requires
        count <= a.len(),
        count <= b.len(),
        forall|j: int| 0 <= j < count ==> a[j] == b[j],
    ensures
        sum_widths(a, count) == sum_widths(b, count),
    decreases count,
{
    if count == 0 {
    } else {
        lemma_sum_widths_ext_equal(a, b, (count - 1) as nat);
    }
}

/// The row content width is non-negative when spacing and all child widths are non-negative.
pub proof fn lemma_row_content_width_nonneg<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
)
    requires
        T::zero().le(spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> T::zero().le(child_sizes[i].width),
    ensures
        T::zero().le(row_content_width(child_sizes, spacing)),
{
    if child_sizes.len() == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        crate::layout::grid_proofs::lemma_sum_widths_nonneg(
            child_sizes, child_sizes.len() as nat,
        );
        lemma_repeated_add_nonneg(spacing, (child_sizes.len() - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_widths(child_sizes, child_sizes.len() as nat),
            T::zero(), repeated_add(spacing, (child_sizes.len() - 1) as nat),
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        let total = sum_widths(child_sizes, child_sizes.len() as nat)
            .add(repeated_add(spacing, (child_sizes.len() - 1) as nat));
        T::axiom_eqv_reflexive(total);
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            total, total,
        );
    }
}

/// Adding a child increases row content width.
///
/// content_width(sizes.push(new_size)) >= content_width(sizes)
/// for non-negative child widths and spacing.
pub proof fn lemma_row_content_width_monotone<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    new_size: Size<T>,
    spacing: T,
)
    requires
        T::zero().le(spacing),
        T::zero().le(new_size.width),
        forall|j: int| 0 <= j < child_sizes.len() ==> T::zero().le(child_sizes[j].width),
    ensures
        row_content_width(child_sizes, spacing).le(
            row_content_width(child_sizes.push(new_size), spacing)
        ),
{
    let n = child_sizes.len();
    let ext = child_sizes.push(new_size);
    assert(ext.len() == n + 1);

    if n == 0 {
        lemma_row_content_width_nonneg(ext, spacing);
    } else {
        lemma_sum_widths_ext_equal::<T>(child_sizes, ext, n as nat);

        let sw_n = sum_widths(child_sizes, n as nat);
        let ra_nm1 = repeated_add(spacing, (n - 1) as nat);

        // sw_n <= sw_n + new.width  (new.width >= 0)
        lemma_le_add_nonneg::<T>(sw_n, new_size.width);
        // ra_nm1 <= ra_nm1 + spacing  (spacing >= 0)
        lemma_le_add_nonneg::<T>(ra_nm1, spacing);

        // sw_n + ra_nm1 <= (sw_n + new.width) + (ra_nm1 + spacing)
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            sw_n, sw_n.add(new_size.width),
            ra_nm1, ra_nm1.add(spacing),
        );

        // Assert definitional equalities to help Z3
        assert(row_content_width(child_sizes, spacing) == sw_n.add(ra_nm1));
        assert(sum_widths(ext, (n + 1) as nat) ==
            sum_widths(ext, n as nat).add(ext[n as int].width));
        assert(ext[n as int] == new_size);
        assert(row_content_width(ext, spacing) ==
            sum_widths(ext, (n + 1) as nat).add(repeated_add(spacing, n as nat)));
    }
}

// ── Layout respects limits ──────────────────────────────────────────

/// Master theorem: layout_widget always produces a size within [limits.min, limits.max].
///
/// Every variant ends with limits.resolve(something), and resolve clamps to bounds.
/// Conditional(visible) is the only variant that doesn't resolve — it passes through
/// the child result, but uses the same limits, so induction applies.
pub proof fn lemma_layout_respects_limits<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 0,
    ensures
        limits.min.le(layout_widget(limits, widget, fuel).size),
        layout_widget(limits, widget, fuel).size.le(limits.max),
    decreases fuel, 0nat,
{
    match widget {
        Widget::Leaf { size } => {
            lemma_resolve_bounds(limits, size);
        },
        Widget::Column { padding, spacing, alignment, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let layout = column_layout(limits, padding, spacing, alignment, child_sizes);
            // merge preserves size
            assert(merge_layout(layout, cn).size == layout.size);
            // column_layout.size = limits.resolve(...)
            let content_height = column_content_height(child_sizes, spacing);
            let total_height = padding.vertical().add(content_height);
            lemma_resolve_bounds(limits, Size::new(limits.max.width, total_height));
        },
        Widget::Row { padding, spacing, alignment, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let layout = row_layout(limits, padding, spacing, alignment, child_sizes);
            assert(merge_layout(layout, cn).size == layout.size);
            let content_width = row_content_width(child_sizes, spacing);
            let total_width = padding.horizontal().add(content_width);
            lemma_resolve_bounds(limits, Size::new(total_width, limits.max.height));
        },
        Widget::Stack { padding, h_align, v_align, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let layout = stack_layout(limits, padding, h_align, v_align, child_sizes);
            assert(merge_layout(layout, cn).size == layout.size);
            let content = stack_content_size(child_sizes);
            let tw = padding.horizontal().add(content.width);
            let th = padding.vertical().add(content.height);
            lemma_resolve_bounds(limits, Size::new(tw, th));
        },
        Widget::Wrap { padding, h_spacing, v_spacing, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let layout = wrap_layout(limits, padding, h_spacing, v_spacing, child_sizes);
            assert(merge_layout(layout, cn).size == layout.size);
            let available_width = limits.max.width.sub(padding.horizontal());
            let content = wrap_content_size(child_sizes, h_spacing, v_spacing, available_width);
            let tw = padding.horizontal().add(content.width);
            let th = padding.vertical().add(content.height);
            lemma_resolve_bounds(limits, Size::new(tw, th));
        },
        Widget::Flex { padding, spacing, alignment, direction, children } => {
            lemma_resolve_bounds(limits, limits.max);
        },
        Widget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                       col_widths, row_heights, children } => {
            let content_w = grid_content_width(col_widths, h_spacing);
            let content_h = grid_content_height(row_heights, v_spacing);
            let tw = padding.horizontal().add(content_w);
            let th = padding.vertical().add(content_h);
            lemma_resolve_bounds(limits, Size::new(tw, th));
        },
        Widget::Absolute { padding, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
            let offsets = Seq::new(children.len(), |i: int|
                (children[i].x, children[i].y));
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let child_data = Seq::new(cn.len(), |i: int|
                (offsets[i].0, offsets[i].1, cn[i].size));
            let content = absolute_content_size(child_data);
            let tw = padding.horizontal().add(content.width);
            let th = padding.vertical().add(content.height);
            lemma_resolve_bounds(limits, Size::new(tw, th));
        },
        Widget::Margin { margin, child } => {
            let inner = limits.shrink(margin.horizontal(), margin.vertical());
            let child_node = layout_widget(inner, *child, (fuel - 1) as nat);
            let tw = margin.horizontal().add(child_node.size.width);
            let th = margin.vertical().add(child_node.size.height);
            lemma_resolve_bounds(limits, Size::new(tw, th));
        },
        Widget::Conditional { visible, child } => {
            if visible {
                let child_node = layout_widget(limits, *child, (fuel - 1) as nat);
                lemma_resolve_bounds(limits, child_node.size);
            } else {
                lemma_resolve_bounds(limits, Size::zero_size());
            }
        },
        Widget::SizedBox { inner_limits, child } => {
            let effective = limits.intersect(inner_limits);
            let child_node = layout_widget(effective, *child, (fuel - 1) as nat);
            lemma_resolve_bounds(limits, child_node.size);
        },
        Widget::AspectRatio { ratio, child } => {
            let w1 = limits.max.width;
            let h1 = w1.div(ratio);
            let child_node = if h1.le(limits.max.height) {
                let eff = Limits {
                    min: limits.min,
                    max: Size::new(w1, h1),
                };
                layout_widget(eff, *child, (fuel - 1) as nat)
            } else {
                let h2 = limits.max.height;
                let w2 = h2.mul(ratio);
                let eff = Limits {
                    min: limits.min,
                    max: Size::new(w2, h2),
                };
                layout_widget(eff, *child, (fuel - 1) as nat)
            };
            lemma_resolve_bounds(limits, child_node.size);
        },
    }
}

// ── Clamp / Resolve foundation lemmas ────────────────────────────

/// val <= clamp(val, lo, hi) when val <= hi and lo <= hi.
/// Since val <= hi, min(val, hi) = val, so clamp = max(lo, val) >= val.
pub proof fn lemma_val_le_clamp<T: OrderedRing>(val: T, lo: T, hi: T)
    requires
        lo.le(hi),
        val.le(hi),
    ensures
        val.le(Limits::clamp(val, lo, hi)),
{
    // min(val, hi) = val since val.le(hi), so clamp = max(lo, val)
    lemma_max_ge_right::<T>(lo, min::<T>(val, hi));
}

/// max(c, a) <= max(c, b) when a <= b.
proof fn lemma_max_monotone_right<T: OrderedRing>(a: T, b: T, c: T)
    requires
        a.le(b),
    ensures
        max::<T>(c, a).le(max::<T>(c, b)),
{
    T::axiom_le_total(c, a);
    if c.le(a) {
        // max(c,a) = a. c <= a <= b so c <= b, hence max(c,b) = b.
        T::axiom_le_transitive(c, a, b);
        // Now max(c,a) = a, max(c,b) = b, need a.le(b) ✓
    } else {
        // a < c, so max(c,a) = c. Need c <= max(c,b).
        lemma_max_ge_left::<T>(c, b);
    }
}

/// Clamp is monotone in the upper bound:
/// clamp(v, lo, hi1) <= clamp(v, lo, hi2) when lo <= hi1 <= hi2.
pub proof fn lemma_clamp_monotone_hi<T: OrderedRing>(v: T, lo: T, hi1: T, hi2: T)
    requires
        lo.le(hi1),
        hi1.le(hi2),
    ensures
        Limits::clamp(v, lo, hi1).le(Limits::clamp(v, lo, hi2)),
{
    // clamp(v, lo, hi_k) = max(lo, min(v, hi_k))
    // Show min(v, hi1) <= min(v, hi2), then use max_monotone_right.
    T::axiom_le_total(v, hi1);
    if v.le(hi1) {
        // min(v, hi1) = v. Also v <= hi1 <= hi2 so v <= hi2, min(v, hi2) = v.
        T::axiom_le_transitive(v, hi1, hi2);
        // Both clamps = max(lo, v).
        T::axiom_le_reflexive(max::<T>(lo, v));
    } else {
        // hi1 < v, so min(v, hi1) = hi1.
        T::axiom_le_total(v, hi2);
        if v.le(hi2) {
            // min(v, hi2) = v. Need max(lo, hi1) <= max(lo, v).
            // hi1 <= v (from hi1 < v via total order: NOT v.le(hi1) means hi1.le(v) by totality...
            // actually axiom_le_total gives v.le(hi1) || hi1.le(v), and we're in the !v.le(hi1) branch)
            lemma_max_monotone_right::<T>(hi1, v, lo);
        } else {
            // hi2 < v, so min(v, hi2) = hi2. Need max(lo, hi1) <= max(lo, hi2).
            lemma_max_monotone_right::<T>(hi1, hi2, lo);
        }
    }
}

/// resolve(size) >= size component-wise when size <= limits.max.
pub proof fn lemma_resolve_ge_input<T: OrderedRing>(limits: Limits<T>, size: Size<T>)
    requires
        limits.wf(),
        size.le(limits.max),
    ensures
        size.le(limits.resolve(size)),
{
    lemma_val_le_clamp::<T>(size.width, limits.min.width, limits.max.width);
    lemma_val_le_clamp::<T>(size.height, limits.min.height, limits.max.height);
}

// ── Resolve monotonicity ─────────────────────────────────────────

/// max(a1, b).eqv(max(a2, b)) when a1.eqv(a2).
proof fn lemma_max_congruence_left<T: OrderedRing>(a1: T, a2: T, b: T)
    requires
        a1.eqv(a2),
    ensures
        max::<T>(a1, b).eqv(max::<T>(a2, b)),
{
    // Case split on a1.le(b)
    T::axiom_le_total(a1, b);
    if a1.le(b) {
        // max(a1, b) = b.
        // a1.eqv(a2) and a1.le(b) => a2.le(b) by le_congruence
        T::axiom_eqv_reflexive(b);
        T::axiom_le_congruence(a1, a2, b, b);
        // max(a2, b) = b. So both are b.
        T::axiom_eqv_reflexive(b);
    } else {
        // max(a1, b) = a1. And b < a1, so NOT b.le(a1)... wait, le_total says a1.le(b) || b.le(a1).
        // We're in NOT a1.le(b), so b.le(a1) by totality... but wait, that's already from le_total above.
        // Actually le_total gives a1.le(b) || b.le(a1), and we're in the else, so b.le(a1).
        // But NOT a1.le(b) doesn't mean NOT a2.le(b) directly. Let me use le_congruence differently.
        // We have: NOT a1.le(b). max(a1, b) = a1.
        // Need to show NOT a2.le(b), i.e., max(a2, b) = a2.
        // From NOT a1.le(b) and a1.eqv(a2): if a2.le(b), then by le_congruence(a2, a1, b, b),
        // a1.le(b) — contradiction. So NOT a2.le(b).
        T::axiom_eqv_symmetric(a1, a2);
        T::axiom_eqv_reflexive(b);
        T::axiom_le_total(a2, b);
        if a2.le(b) {
            T::axiom_le_congruence(a2, a1, b, b);
            // contradiction: a1.le(b) in else branch
        }
        // max(a2, b) = a2. Need a1.eqv(a2).
    }
}

/// Resolve is monotone in limits.max: widening max widens the result.
pub proof fn lemma_resolve_monotone_max<T: OrderedRing>(
    limits1: Limits<T>,
    limits2: Limits<T>,
    size: Size<T>,
)
    requires
        limits1.wf(),
        limits2.wf(),
        limits1.min.width.eqv(limits2.min.width),
        limits1.min.height.eqv(limits2.min.height),
        limits1.max.le(limits2.max),
    ensures
        limits1.resolve(size).le(limits2.resolve(size)),
{
    // Width: clamp(v, min1.w, max1.w) <= clamp(v, min2.w, max2.w)
    // Since min1.w.eqv(min2.w) and max1.w.le(max2.w):
    // Step 1: clamp(v, min1.w, max1.w) <= clamp(v, min1.w, max2.w)  [clamp_monotone_hi]
    lemma_clamp_monotone_hi::<T>(
        size.width, limits1.min.width, limits1.max.width, limits2.max.width,
    );
    // Step 2: clamp(v, min1.w, max2.w) eqv clamp(v, min2.w, max2.w)  [min eqv => max eqv]
    // clamp(v, lo, hi) = max(lo, min(v, hi))
    lemma_max_congruence_left::<T>(
        limits1.min.width, limits2.min.width,
        min::<T>(size.width, limits2.max.width),
    );
    // Step 3: le + eqv => le
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        limits1.resolve(size).width,
        Limits::clamp(size.width, limits1.min.width, limits2.max.width),
        limits2.resolve(size).width,
    );

    // Height: symmetric
    lemma_clamp_monotone_hi::<T>(
        size.height, limits1.min.height, limits1.max.height, limits2.max.height,
    );
    lemma_max_congruence_left::<T>(
        limits1.min.height, limits2.min.height,
        min::<T>(size.height, limits2.max.height),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        limits1.resolve(size).height,
        Limits::clamp(size.height, limits1.min.height, limits2.max.height),
        limits2.resolve(size).height,
    );
}

/// Leaf layout is monotone in limits.max: widening max widens the leaf size.
pub proof fn lemma_layout_leaf_monotone<T: OrderedField>(
    limits1: Limits<T>,
    limits2: Limits<T>,
    size: Size<T>,
    fuel: nat,
)
    requires
        limits1.wf(),
        limits2.wf(),
        limits1.min.width.eqv(limits2.min.width),
        limits1.min.height.eqv(limits2.min.height),
        limits1.max.le(limits2.max),
        fuel > 0,
    ensures
        layout_widget(limits1, Widget::Leaf { size }, fuel).size.le(
            layout_widget(limits2, Widget::Leaf { size }, fuel).size),
{
    // layout_widget for Leaf = limits.resolve(size)
    lemma_resolve_monotone_max(limits1, limits2, size);
}

// ── Children-within-parent bounds ─────────────────────────────────

/// Layout of a Leaf widget has no children, so children_within_bounds is trivially true.
pub proof fn lemma_leaf_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    size: Size<T>,
)
    requires limits.wf(),
    ensures
        layout_widget(limits, Widget::Leaf { size }, 1).children_within_bounds(),
{
}

/// Layout of a Conditional(!visible) widget has no children.
pub proof fn lemma_conditional_hidden_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    child: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 0,
    ensures
        layout_widget(limits, Widget::Conditional { visible: false, child: Box::new(child) }, fuel)
            .children_within_bounds(),
{
}

/// At fuel=0, layout produces a zero-size leaf, so children_within_bounds holds.
pub proof fn lemma_zero_fuel_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
)
    ensures
        layout_widget(limits, widget, 0).children_within_bounds(),
{
}

/// limits.intersect(other).wf() whenever limits.wf().
/// The intersect construction guarantees min <= max and non-negativity.
proof fn lemma_intersect_wf<T: OrderedRing>(limits: Limits<T>, other: Limits<T>)
    requires
        limits.wf(),
    ensures
        limits.intersect(other).wf(),
{
    let eff = limits.intersect(other);
    // min is non-negative: new_min = max(limits.min, other.min) >= limits.min >= 0
    lemma_max_ge_left::<T>(limits.min.width, other.min.width);
    T::axiom_le_transitive(T::zero(), limits.min.width, eff.min.width);
    lemma_max_ge_left::<T>(limits.min.height, other.min.height);
    T::axiom_le_transitive(T::zero(), limits.min.height, eff.min.height);
    // max >= min by construction: max = max(new_min, min(...)) >= new_min
    lemma_max_ge_left::<T>(eff.min.width, min::<T>(limits.max.width, other.max.width));
    lemma_max_ge_left::<T>(eff.min.height, min::<T>(limits.max.height, other.max.height));
    // max is non-negative: max >= min >= 0
    T::axiom_le_transitive(T::zero(), eff.min.width, eff.max.width);
    T::axiom_le_transitive(T::zero(), eff.min.height, eff.max.height);
}

/// limits.intersect(other).max <= limits.max when inner_limits.min <= limits.max.
proof fn lemma_intersect_max_le<T: OrderedRing>(limits: Limits<T>, other: Limits<T>)
    requires
        limits.wf(),
        other.min.width.le(limits.max.width),
        other.min.height.le(limits.max.height),
    ensures
        limits.intersect(other).max.le(limits.max),
{
    let eff = limits.intersect(other);
    // Width: eff.max.width = max(new_min_w, min(limits.max.width, other.max.width))
    // min(...) <= limits.max.width by lemma_min_le_left
    lemma_min_le_left::<T>(limits.max.width, other.max.width);
    // new_min_w = max(limits.min.width, other.min.width)
    // Both <= limits.max.width, so max <= limits.max.width (case split)
    let new_min_w = max::<T>(limits.min.width, other.min.width);
    T::axiom_le_total(limits.min.width, other.min.width);
    if limits.min.width.le(other.min.width) {
        // new_min_w = other.min.width <= limits.max.width
    } else {
        // new_min_w = limits.min.width <= limits.max.width (by wf)
    }
    // Now both sides of outer max <= limits.max.width
    let inner_w = min::<T>(limits.max.width, other.max.width);
    T::axiom_le_total(new_min_w, inner_w);
    // max(new_min_w, inner_w) is whichever is larger, both <= limits.max.width

    // Height: symmetric
    lemma_min_le_left::<T>(limits.max.height, other.max.height);
    let new_min_h = max::<T>(limits.min.height, other.min.height);
    T::axiom_le_total(limits.min.height, other.min.height);
    let inner_h = min::<T>(limits.max.height, other.max.height);
    T::axiom_le_total(new_min_h, inner_h);
}

/// SizedBox layout places its single child within the parent bounds.
pub proof fn lemma_sized_box_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    inner_limits: Limits<T>,
    child: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        inner_limits.min.width.le(limits.max.width),
        inner_limits.min.height.le(limits.max.height),
    ensures
        layout_widget(limits, Widget::SizedBox {
            inner_limits, child: Box::new(child),
        }, fuel).children_within_bounds(),
{
    let effective = limits.intersect(inner_limits);
    let child_node = layout_widget(effective, child, (fuel - 1) as nat);
    let parent = layout_widget(limits, Widget::SizedBox {
        inner_limits, child: Box::new(child),
    }, fuel);

    // Step 1: effective.wf()
    lemma_intersect_wf(limits, inner_limits);

    // Step 2: child_node.size <= effective.max
    lemma_layout_respects_limits(effective, child, (fuel - 1) as nat);

    // Step 3: effective.max <= limits.max
    lemma_intersect_max_le(limits, inner_limits);

    // Step 4: child_node.size <= limits.max (by transitivity)
    T::axiom_le_transitive(child_node.size.width, effective.max.width, limits.max.width);
    T::axiom_le_transitive(child_node.size.height, effective.max.height, limits.max.height);

    // Step 5: child_node.size <= limits.resolve(child_node.size)
    lemma_resolve_ge_input(limits, child_node.size);

    // cwb for the single child at (0, 0):
    lemma_single_child_at_origin_cwb(child_node.size, limits.resolve(child_node.size));
}

/// AspectRatio layout places its single child within the parent bounds.
///
/// Requires the effective limits (whichever branch is chosen) to be wf.
/// - Width-first branch (w1/ratio <= max.h): needs min.h <= w1/ratio
/// - Height-first branch: needs min.w <= h2*ratio
pub proof fn lemma_aspect_ratio_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    ratio: T,
    child: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        T::zero().lt(ratio),
        ({
            let w1 = limits.max.width;
            let h1 = w1.div(ratio);
            if h1.le(limits.max.height) {
                // Width-first: eff.max = (w1, h1), need min <= max for wf
                limits.min.height.le(h1) && T::zero().le(h1)
            } else {
                // Height-first: eff.max = (w2, h2), need min <= max for wf
                let w2 = limits.max.height.mul(ratio);
                limits.min.width.le(w2) && T::zero().le(w2)
            }
        }),
    ensures
        layout_widget(limits, Widget::AspectRatio {
            ratio, child: Box::new(child),
        }, fuel).children_within_bounds(),
{
    let w1 = limits.max.width;
    let h1 = w1.div(ratio);
    if h1.le(limits.max.height) {
        // Width-first branch
        let eff = Limits {
            min: limits.min,
            max: Size::new(w1, h1),
        };
        // eff.wf(): min.w <= max.w = w1 from limits.wf, min.h <= h1 from precondition
        // 0 <= w1 from limits.wf, 0 <= h1 from precondition
        let child_node = layout_widget(eff, child, (fuel - 1) as nat);

        // child_node.size <= eff.max
        lemma_layout_respects_limits(eff, child, (fuel - 1) as nat);

        // eff.max <= limits.max: w1 <= w1 (refl), h1 <= max.h (branch cond)
        T::axiom_le_reflexive(w1);

        // child_node.size <= limits.max
        T::axiom_le_transitive(child_node.size.width, eff.max.width, limits.max.width);
        T::axiom_le_transitive(child_node.size.height, eff.max.height, limits.max.height);
    } else {
        // Height-first branch
        let h2 = limits.max.height;
        let w2 = h2.mul(ratio);
        let eff = Limits {
            min: limits.min,
            max: Size::new(w2, h2),
        };
        // eff.wf(): min.w <= w2 from precondition, min.h <= max.h from limits.wf
        // 0 <= w2 from precondition, 0 <= h2 from limits.wf
        let child_node = layout_widget(eff, child, (fuel - 1) as nat);

        // child_node.size <= eff.max
        lemma_layout_respects_limits(eff, child, (fuel - 1) as nat);

        // eff.max <= limits.max: w2 <= max.w (we need this but don't have it directly)
        // Actually h2 = max.h, so eff.max.h = max.h <= max.h (refl)
        T::axiom_le_reflexive(h2);

        // w2 = max.h * ratio. Need w2 <= max.w.
        // !h1.le(max.h) → max.h.le(h1) by totality
        T::axiom_le_total(h1, limits.max.height);
        // max.h.le(h1), so max.h * ratio <= h1 * ratio (since 0 <= ratio)
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), ratio);
        T::axiom_le_mul_nonneg_monotone(limits.max.height, h1, ratio);
        // h1 * ratio = (w1/ratio) * ratio ≡ w1
        // Need !ratio.eqv(zero) from !zero.eqv(ratio) via contrapositive of symmetric
        assert(!ratio.eqv(T::zero())) by {
            if ratio.eqv(T::zero()) {
                T::axiom_eqv_symmetric(ratio, T::zero());
            }
        };
        verus_algebra::lemmas::field_lemmas::lemma_div_mul_cancel::<T>(w1, ratio);
        // w2 <= h1*ratio, h1*ratio ≡ w1 = max.w → w2 <= max.w
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            w2, h1.mul(ratio), w1,
        );

        // child_node.size <= limits.max
        T::axiom_le_transitive(child_node.size.width, eff.max.width, limits.max.width);
        T::axiom_le_transitive(child_node.size.height, eff.max.height, limits.max.height);
    }

    // Common: child_node.size <= limits.max
    // → resolve(child_node.size) >= child_node.size
    let child_node = if h1.le(limits.max.height) {
        let eff = Limits { min: limits.min, max: Size::new(w1, h1) };
        layout_widget(eff, child, (fuel - 1) as nat)
    } else {
        let h2 = limits.max.height;
        let w2 = h2.mul(ratio);
        let eff = Limits { min: limits.min, max: Size::new(w2, h2) };
        layout_widget(eff, child, (fuel - 1) as nat)
    };
    lemma_resolve_ge_input(limits, child_node.size);
    lemma_single_child_at_origin_cwb(child_node.size, limits.resolve(child_node.size));
}

// ── Reusable arithmetic helpers ───────────────────────────────────

/// a + b >= 0 when a >= 0 and b >= 0.
pub proof fn lemma_nonneg_sum<T: OrderedRing>(a: T, b: T)
    requires T::zero().le(a), T::zero().le(b),
    ensures T::zero().le(a.add(b)),
{
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        T::zero(), a, T::zero(), b,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero().add(T::zero()), T::zero(), a.add(b),
    );
}

/// If a + b <= c, then b + a <= c (commutativity preserves le).
pub proof fn lemma_add_comm_le<T: OrderedRing>(a: T, b: T, c: T)
    requires a.add(b).le(c),
    ensures b.add(a).le(c),
{
    T::axiom_add_commutative(a, b);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        a.add(b), b.add(a), c,
    );
}

// ── Single-child-at-origin cwb helper ─────────────────────────────

/// Helper: 0 + v <= bound when v <= bound.
/// Bridges right()/bottom() = zero.add(size) to the le bound.
proof fn lemma_zero_add_le<T: OrderedRing>(v: T, bound: T)
    requires v.le(bound),
    ensures T::zero().add(v).le(bound),
{
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(v);
    T::axiom_eqv_symmetric(T::zero().add(v), v);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        v, T::zero().add(v), bound,
    );
}

/// Additive cancellation for le: a + c <= b + c implies a <= b.
pub proof fn lemma_le_add_cancel_right<T: OrderedRing>(a: T, b: T, c: T)
    requires
        a.add(c).le(b.add(c)),
    ensures
        a.le(b),
{
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone::<T>(
        a.add(c), b.add(c), c,
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<T>(a, c);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel::<T>(b, c);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        a.add(c).sub(c), a, b.add(c).sub(c),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        a, b.add(c).sub(c), b,
    );
}

/// Establish cwb proof facts for a single child positioned at origin (0,0).
/// After calling, Z3 has: 0 <= 0, 0 + child_w <= parent_w, 0 + child_h <= parent_h.
/// These are exactly the facts needed for children_within_bounds of a node
/// with one child at (0,0) whose size fits within the parent.
pub proof fn lemma_single_child_at_origin_cwb<T: OrderedRing>(
    child_size: Size<T>,
    parent_size: Size<T>,
)
    requires
        child_size.width.le(parent_size.width),
        child_size.height.le(parent_size.height),
    ensures
        T::zero().le(T::zero()),
        T::zero().add(child_size.width).le(parent_size.width),
        T::zero().add(child_size.height).le(parent_size.height),
{
    T::axiom_le_reflexive(T::zero());
    lemma_zero_add_le(child_size.width, parent_size.width);
    lemma_zero_add_le(child_size.height, parent_size.height);
}

/// Conditional(visible=true) layout has cwb when the child layout has cwb.
/// The Conditional passes through child_node.children with a (possibly larger)
/// resolved parent size, so inner cwb implies outer cwb by transitivity.
pub proof fn lemma_conditional_visible_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    child: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        layout_widget(limits, child, (fuel - 1) as nat).children_within_bounds(),
    ensures
        layout_widget(limits, Widget::Conditional {
            visible: true, child: Box::new(child),
        }, fuel).children_within_bounds(),
{
    let child_node = layout_widget(limits, child, (fuel - 1) as nat);
    // child_node.size <= limits.max
    lemma_layout_respects_limits(limits, child, (fuel - 1) as nat);
    // child_node.size <= limits.resolve(child_node.size) (resolve only grows)
    lemma_resolve_ge_input(limits, child_node.size);
    // Each child c: c.right() <= child_node.size.width <= resolve.width (transitivity)
    assert forall|i: int| 0 <= i < child_node.children.len() implies {
        &&& T::zero().le(child_node.children[i].x)
        &&& T::zero().le(child_node.children[i].y)
        &&& child_node.children[i].right().le(limits.resolve(child_node.size).width)
        &&& child_node.children[i].bottom().le(limits.resolve(child_node.size).height)
    } by {
        T::axiom_le_transitive(
            child_node.children[i].right(),
            child_node.size.width,
            limits.resolve(child_node.size).width,
        );
        T::axiom_le_transitive(
            child_node.children[i].bottom(),
            child_node.size.height,
            limits.resolve(child_node.size).height,
        );
    };
}

// ── Shrink helpers ────────────────────────────────────────────────

/// shrink(h, v) preserves wf: the shrunken limits still satisfy min <= max
/// and both are non-negative.
pub proof fn lemma_shrink_wf<T: OrderedRing>(limits: Limits<T>, h: T, v: T)
    requires
        limits.wf(),
        T::zero().le(h),
        T::zero().le(v),
    ensures
        limits.shrink(h, v).wf(),
{
    let s = limits.shrink(h, v);
    // min.w <= max(min.w, ...) by max_ge_left
    lemma_max_ge_left::<T>(limits.min.width, limits.max.width.sub(h));
    lemma_max_ge_left::<T>(limits.min.height, limits.max.height.sub(v));
    // max nonneg: max >= min >= 0
    T::axiom_le_transitive(T::zero(), limits.min.width, s.max.width);
    T::axiom_le_transitive(T::zero(), limits.min.height, s.max.height);
}

/// After shrinking, shrink.max + margin fits within limits.max:
/// shrink(h, v).max.width + h <= limits.max.width (and symmetrically for height).
pub proof fn lemma_shrink_max_bound<T: OrderedRing>(limits: Limits<T>, h: T, v: T)
    requires
        limits.wf(),
        T::zero().le(h),
        T::zero().le(v),
        limits.min.width.add(h).le(limits.max.width),
        limits.min.height.add(v).le(limits.max.height),
    ensures
        limits.shrink(h, v).max.width.add(h).le(limits.max.width),
        limits.shrink(h, v).max.height.add(v).le(limits.max.height),
{
    // Width: shrink.max.w = max(min.w, max.w - h)
    T::axiom_le_total(limits.min.width, limits.max.width.sub(h));
    if limits.min.width.le(limits.max.width.sub(h)) {
        // max(min.w, max.w-h) = max.w-h
        // (max.w-h)+h ≡ max.w → le from eqv
        verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
            limits.max.width, h,
        );
        T::axiom_eqv_symmetric(limits.max.width.sub(h).add(h), limits.max.width);
        T::axiom_le_reflexive(limits.max.width);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            limits.max.width,
            limits.max.width.sub(h).add(h),
            limits.max.width,
        );
    }
    // else: max(min.w, max.w-h) = min.w, min.w+h <= max.w from precondition

    // Height: symmetric
    T::axiom_le_total(limits.min.height, limits.max.height.sub(v));
    if limits.min.height.le(limits.max.height.sub(v)) {
        verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
            limits.max.height, v,
        );
        T::axiom_eqv_symmetric(limits.max.height.sub(v).add(v), limits.max.height);
        T::axiom_le_reflexive(limits.max.height);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            limits.max.height,
            limits.max.height.sub(v).add(v),
            limits.max.height,
        );
    }
}

// ── Margin cwb ───────────────────────────────────────────────────

/// Margin layout places its single child at (margin.left, margin.top)
/// within the parent bounds, when the margin fits within limits.
pub proof fn lemma_margin_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    margin: Padding<T>,
    child: Widget<T>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        margin.is_nonneg(),
        margin.horizontal().add(limits.min.width).le(limits.max.width),
        margin.vertical().add(limits.min.height).le(limits.max.height),
    ensures
        layout_widget(limits, Widget::Margin {
            margin, child: Box::new(child),
        }, fuel).children_within_bounds(),
{
    let h = margin.horizontal();
    let v = margin.vertical();
    let inner = limits.shrink(h, v);
    let child_node = layout_widget(inner, child, (fuel - 1) as nat);
    let total_w = h.add(child_node.size.width);
    let total_h = v.add(child_node.size.height);

    // 0. h >= 0, v >= 0 from component non-negativity
    lemma_nonneg_sum(margin.left, margin.right);
    lemma_nonneg_sum(margin.top, margin.bottom);

    // 1. inner.wf()
    lemma_shrink_wf(limits, h, v);

    // 2. child.size <= inner.max
    lemma_layout_respects_limits(inner, child, (fuel - 1) as nat);

    // 3. Convert precondition: h+min.w <= max.w → min.w+h <= max.w
    lemma_add_comm_le(h, limits.min.width, limits.max.width);
    lemma_add_comm_le(v, limits.min.height, limits.max.height);

    // 4. shrink.max + h <= limits.max
    lemma_shrink_max_bound(limits, h, v);

    // 5. total_w = h + child.w <= h + inner.max.w = inner.max.w + h <= max.w
    T::axiom_le_add_monotone(child_node.size.width, inner.max.width, h);
    T::axiom_add_commutative(child_node.size.width, h);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        child_node.size.width.add(h), h.add(child_node.size.width), inner.max.width.add(h),
    );
    T::axiom_le_transitive(total_w, inner.max.width.add(h), limits.max.width);

    // Similarly for height
    T::axiom_le_add_monotone(child_node.size.height, inner.max.height, v);
    T::axiom_add_commutative(child_node.size.height, v);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        child_node.size.height.add(v), v.add(child_node.size.height), inner.max.height.add(v),
    );
    T::axiom_le_transitive(total_h, inner.max.height.add(v), limits.max.height);

    // 6. resolve(total) >= total → parent_size >= total
    lemma_resolve_ge_input(limits, Size::new(total_w, total_h));
    let parent_size = limits.resolve(Size::new(total_w, total_h));

    // 7. margin.left + child.w <= total_w <= parent.w
    lemma_le_add_nonneg(margin.left, margin.right);
    T::axiom_le_add_monotone(margin.left, h, child_node.size.width);
    T::axiom_le_transitive(margin.left.add(child_node.size.width), total_w, parent_size.width);

    // 8. margin.top + child.h <= total_h <= parent.h
    lemma_le_add_nonneg(margin.top, margin.bottom);
    T::axiom_le_add_monotone(margin.top, v, child_node.size.height);
    T::axiom_le_transitive(margin.top.add(child_node.size.height), total_h, parent_size.height);
}

/// If layout positions and child sizes satisfy bounds, merge_layout preserves cwb.
/// Reusable for any widget that goes through merge_layout (stack, column, row, etc.).
pub proof fn lemma_merge_layout_cwb<T: OrderedRing>(
    layout: Node<T>,
    child_nodes: Seq<Node<T>>,
)
    requires
        layout.children.len() == child_nodes.len(),
        forall|i: int| 0 <= i < child_nodes.len() ==> {
            &&& T::zero().le(layout.children[i].x)
            &&& T::zero().le(layout.children[i].y)
            &&& layout.children[i].x.add(child_nodes[i].size.width).le(layout.size.width)
            &&& layout.children[i].y.add(child_nodes[i].size.height).le(layout.size.height)
        },
    ensures
        merge_layout(layout, child_nodes).children_within_bounds(),
{
    let result = merge_layout(layout, child_nodes);
    assert forall|i: int| 0 <= i < result.children.len() implies
        T::zero().le(result.children[i].x)
        && T::zero().le(result.children[i].y)
        && result.children[i].right().le(result.size.width)
        && result.children[i].bottom().le(result.size.height)
    by {};
}

/// Clamp is monotone in the lower bound: raising lo raises the result.
pub proof fn lemma_clamp_monotone_lo<T: OrderedRing>(
    v: T,
    lo1: T,
    lo2: T,
    hi: T,
)
    requires
        lo1.le(lo2),
        lo2.le(hi),
    ensures
        Limits::clamp(v, lo1, hi).le(Limits::clamp(v, lo2, hi)),
{
    // clamp(v, lo, hi) = max(lo, min(v, hi))
    let m = min::<T>(v, hi);
    T::axiom_le_total(lo2, m);
    if lo2.le(m) {
        // max(lo2, m) = m, lo1 <= lo2 <= m ⇒ lo1.le(m) ⇒ max(lo1, m) = m
        T::axiom_le_transitive(lo1, lo2, m);
        // result: m.le(m)
        T::axiom_le_reflexive(m);
    } else {
        // !lo2.le(m), totality ⇒ m.le(lo2)
        // max(lo2, m) = lo2
        // max(lo1, m) ∈ {lo1, m}, both <= lo2
    }
}

/// Resolve is monotone in both min and max: widening both widens the result.
pub proof fn lemma_resolve_monotone_both<T: OrderedRing>(
    limits1: Limits<T>,
    limits2: Limits<T>,
    size: Size<T>,
)
    requires
        limits1.wf(),
        limits2.wf(),
        limits1.min.le(limits2.min),
        limits1.max.le(limits2.max),
    ensures
        limits1.resolve(size).le(limits2.resolve(size)),
{
    // resolve(size).width = clamp(size.width, min.width, max.width)
    // Need: clamp(size.w, min1.w, max1.w) <= clamp(size.w, min2.w, max2.w)
    // Step 1: clamp(v, lo1, hi1) <= clamp(v, lo1, hi2) when hi1 <= hi2
    //   (from lemma_clamp_monotone_hi, which is the core of resolve_monotone_max)
    // Step 2: clamp(v, lo1, hi2) <= clamp(v, lo2, hi2) when lo1 <= lo2
    //   (from lemma_clamp_monotone_lo)

    // Width: use intermediate clamp(size.w, min1.w, max2.w)
    // First raise max: clamp(v, min1.w, max1.w) <= clamp(v, min1.w, max2.w)
    let lim_mid = Limits {
        min: limits1.min,
        max: limits2.max,
    };
    // lim_mid.wf(): min1 <= max1 <= max2, so min1 <= max2
    T::axiom_le_transitive(limits1.min.width, limits1.max.width, limits2.max.width);
    T::axiom_le_transitive(limits1.min.height, limits1.max.height, limits2.max.height);
    // max nonneg for wf
    T::axiom_le_transitive(T::zero(), limits2.min.width, limits2.max.width);
    T::axiom_le_transitive(T::zero(), limits2.min.height, limits2.max.height);

    // resolve_monotone_max needs min1.eqv(lim_mid.min) = min1.eqv(min1) (reflexive)
    T::axiom_eqv_reflexive(limits1.min.width);
    T::axiom_eqv_reflexive(limits1.min.height);
    lemma_resolve_monotone_max(limits1, lim_mid, size);

    // Then raise min: clamp(v, min1.w, max2.w) <= clamp(v, min2.w, max2.w)
    lemma_clamp_monotone_lo(
        size.width, limits1.min.width, limits2.min.width, limits2.max.width,
    );
    lemma_clamp_monotone_lo(
        size.height, limits1.min.height, limits2.min.height, limits2.max.height,
    );

    // Combine: width
    T::axiom_le_transitive(
        limits1.resolve(size).width,
        lim_mid.resolve(size).width,
        limits2.resolve(size).width,
    );
    // Combine: height
    T::axiom_le_transitive(
        limits1.resolve(size).height,
        lim_mid.resolve(size).height,
        limits2.resolve(size).height,
    );
}

/// Column layout has children_within_bounds when padding fits and content doesn't overflow.
pub proof fn lemma_column_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            padding.vertical().add(column_content_height(child_sizes, spacing))
                .le(limits.max.height)
        }),
    ensures
        layout_widget(limits, Widget::Column {
            padding, spacing, alignment, children,
        }, fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    let avail_w = limits.max.width.sub(h);
    let content_h = column_content_height(child_sizes, spacing);
    let total_h = v.add(content_h);
    let input_size = Size::new(limits.max.width, total_h);

    // h >= 0, v >= 0
    lemma_nonneg_sum(padding.left, padding.right);
    lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf() + shrink bounds
    lemma_shrink_wf(limits, h, v);
    lemma_add_comm_le(h, limits.min.width, limits.max.width);
    lemma_add_comm_le(v, limits.min.height, limits.max.height);
    lemma_shrink_max_bound(limits, h, v);

    // inner.max.w <= avail_w: from shrink_max_bound + add_cancel
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.width, h,
    );
    T::axiom_eqv_symmetric(avail_w.add(h), limits.max.width);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        inner.max.width.add(h), limits.max.width, avail_w.add(h),
    );
    lemma_le_add_cancel_right(inner.max.width, avail_w, h);

    // Each child: size <= inner.max → size <= (avail_w for width, inner.max for height)
    // Also: child nonneg from inner min <= size
    assert forall|k: int| 0 <= k < cn.len() implies
        child_sizes[k].width.le(avail_w)
        && T::zero().le(child_sizes[k].width)
        && T::zero().le(child_sizes[k].height)
    by {
        lemma_layout_respects_limits(inner, children[k], (fuel - 1) as nat);
        T::axiom_le_transitive(child_sizes[k].width, inner.max.width, avail_w);
        T::axiom_le_transitive(T::zero(), inner.min.width, child_sizes[k].width);
        T::axiom_le_transitive(T::zero(), inner.min.height, child_sizes[k].height);
    };

    // total_h <= max.h (from no-overflow precondition: v + content_h <= max.h)
    // resolve(max.w, total_h) >= (max.w, total_h) since both <= max
    T::axiom_le_reflexive(limits.max.width);
    lemma_resolve_ge_input(limits, input_size);

    // Also: resolve.w <= max.w and resolve.h <= max.h
    lemma_resolve_le_max_width(limits, input_size);

    // parent.w = resolve.w. Show resolve.w ≡ max.w (input was max.w, clamped to [min,max])
    T::axiom_le_antisymmetric(
        limits.resolve(input_size).width, limits.max.width,
    );
    // parent.w ≡ max.w now established

    // left + avail_w <= max.w: left <= h (from nonneg right), h + avail_w ≡ max.w
    lemma_le_add_nonneg(padding.left, padding.right);
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

    // top + content_h <= total_h: top <= v, so top + content_h <= v + content_h = total_h
    lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, v, content_h);

    // Column children structure
    lemma_column_children_len(padding, spacing, alignment, child_sizes, avail_w, 0);

    let layout = column_layout(limits, padding, spacing, alignment, child_sizes);

    // Per-child bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        lemma_column_children_element(
            padding, spacing, alignment, child_sizes, avail_w, i as nat,
        );

        // X lower: 0 <= left, left <= left + align_offset, so 0 <= x
        lemma_column_child_x_lower_bound(
            padding.left, alignment, avail_w, child_sizes[i].width,
        );
        T::axiom_le_transitive(T::zero(), padding.left, layout.children[i].x);

        // X upper: x + w <= left + avail_w <= max.w ≡ parent.w
        lemma_column_child_x_upper_bound(
            padding.left, alignment, avail_w, child_sizes[i].width,
        );
        T::axiom_le_transitive(
            layout.children[i].x.add(child_sizes[i].width),
            padding.left.add(avail_w),
            limits.max.width,
        );
        // max.w ≡ parent.w (from antisymmetric above)
        T::axiom_eqv_symmetric(
            limits.resolve(input_size).width, limits.max.width,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            layout.children[i].x.add(child_sizes[i].width),
            limits.max.width,
            limits.resolve(input_size).width,
        );

        // Y lower: 0 <= top <= child_y
        lemma_column_child_y_lower_bound(padding.top, child_sizes, spacing, i as nat);
        T::axiom_le_transitive(T::zero(), padding.top, layout.children[i].y);

        // Y upper: y + h <= top + content_h <= total_h <= resolve.h = parent.h
        if cn.len() > 0 {
            lemma_column_child_y_upper_bound(padding.top, child_sizes, spacing, i as nat);
            T::axiom_le_transitive(
                layout.children[i].y.add(child_sizes[i].height),
                padding.top.add(content_h),
                total_h,
            );
            T::axiom_le_transitive(
                layout.children[i].y.add(child_sizes[i].height),
                total_h,
                limits.resolve(input_size).height,
            );
        }

        // cn[i].size == child_sizes[i]
        assert(child_sizes[i] === cn[i].size);
    };

    lemma_merge_layout_cwb(layout, cn);
}

/// Row layout has children_within_bounds when padding fits and content doesn't overflow.
pub proof fn lemma_row_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            padding.horizontal().add(row_content_width(child_sizes, spacing))
                .le(limits.max.width)
        }),
    ensures
        layout_widget(limits, Widget::Row {
            padding, spacing, alignment, children,
        }, fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    let avail_h = limits.max.height.sub(v);
    let content_w = row_content_width(child_sizes, spacing);
    let total_w = h.add(content_w);
    let input_size = Size::new(total_w, limits.max.height);

    // h >= 0, v >= 0
    lemma_nonneg_sum(padding.left, padding.right);
    lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf() + shrink bounds
    lemma_shrink_wf(limits, h, v);
    lemma_add_comm_le(h, limits.min.width, limits.max.width);
    lemma_add_comm_le(v, limits.min.height, limits.max.height);
    lemma_shrink_max_bound(limits, h, v);

    // inner.max.h <= avail_h: from shrink_max_bound + add_cancel
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.height, v,
    );
    T::axiom_eqv_symmetric(avail_h.add(v), limits.max.height);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        inner.max.height.add(v), limits.max.height, avail_h.add(v),
    );
    lemma_le_add_cancel_right(inner.max.height, avail_h, v);

    // Each child: height <= avail_h and nonneg
    assert forall|k: int| 0 <= k < cn.len() implies
        child_sizes[k].height.le(avail_h)
        && T::zero().le(child_sizes[k].width)
        && T::zero().le(child_sizes[k].height)
    by {
        lemma_layout_respects_limits(inner, children[k], (fuel - 1) as nat);
        T::axiom_le_transitive(child_sizes[k].height, inner.max.height, avail_h);
        T::axiom_le_transitive(T::zero(), inner.min.width, child_sizes[k].width);
        T::axiom_le_transitive(T::zero(), inner.min.height, child_sizes[k].height);
    };

    // total_w <= max.w (from no-overflow), max.h <= max.h (reflexive)
    T::axiom_le_reflexive(limits.max.height);
    lemma_resolve_ge_input(limits, input_size);
    lemma_resolve_le_max_height(limits, input_size);

    // parent.h = resolve.h ≡ max.h
    T::axiom_le_antisymmetric(
        limits.resolve(input_size).height, limits.max.height,
    );

    // top + avail_h <= max.h: top <= v, v + avail_h ≡ max.h
    lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, v, avail_h);
    T::axiom_add_commutative(v, avail_h);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        limits.max.height, v,
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding.top.add(avail_h), v.add(avail_h), avail_h.add(v),
    );
    T::axiom_le_transitive(
        padding.top.add(avail_h), avail_h.add(v), limits.max.height,
    );

    // left + content_w <= total_w: left <= h, so left + content_w <= h + content_w = total_w
    lemma_le_add_nonneg(padding.left, padding.right);
    T::axiom_le_add_monotone(padding.left, h, content_w);

    // Row children structure
    lemma_row_children_len(padding, spacing, alignment, child_sizes, avail_h, 0);

    let layout = row_layout(limits, padding, spacing, alignment, child_sizes);

    // Per-child bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        lemma_row_children_element(
            padding, spacing, alignment, child_sizes, avail_h, i as nat,
        );

        // X lower: 0 <= left <= child_x
        lemma_row_child_x_lower_bound(padding.left, child_sizes, spacing, i as nat);
        T::axiom_le_transitive(T::zero(), padding.left, layout.children[i].x);

        // X upper: x + w <= left + content_w <= total_w <= resolve.w = parent.w
        if cn.len() > 0 {
            lemma_row_child_x_upper_bound(padding.left, child_sizes, spacing, i as nat);
            T::axiom_le_transitive(
                layout.children[i].x.add(child_sizes[i].width),
                padding.left.add(content_w),
                total_w,
            );
            T::axiom_le_transitive(
                layout.children[i].x.add(child_sizes[i].width),
                total_w,
                limits.resolve(input_size).width,
            );
        }

        // Y lower: 0 <= top <= top + align_offset
        lemma_row_child_y_lower_bound(
            padding.top, alignment, avail_h, child_sizes[i].height,
        );
        T::axiom_le_transitive(T::zero(), padding.top, layout.children[i].y);

        // Y upper: y + h <= top + avail_h <= max.h ≡ parent.h
        lemma_row_child_y_upper_bound(
            padding.top, alignment, avail_h, child_sizes[i].height,
        );
        T::axiom_le_transitive(
            layout.children[i].y.add(child_sizes[i].height),
            padding.top.add(avail_h),
            limits.max.height,
        );
        T::axiom_eqv_symmetric(
            limits.resolve(input_size).height, limits.max.height,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
            layout.children[i].y.add(child_sizes[i].height),
            limits.max.height,
            limits.resolve(input_size).height,
        );

        // cn[i].size == child_sizes[i]
        assert(child_sizes[i] === cn[i].size);
    };

    lemma_merge_layout_cwb(layout, cn);
}

} // verus!
