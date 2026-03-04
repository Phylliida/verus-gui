use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::min_max::*;
use crate::size::Size;
use crate::limits::Limits;
use crate::layout::*;
use crate::alignment::{Alignment, align_offset};

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

/// align_offset produces a non-negative offset when the child fits.
pub proof fn lemma_align_offset_nonneg<T: OrderedRing>(
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
            T::axiom_le_reflexive(T::zero());
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
pub proof fn lemma_align_offset_bounded<T: OrderedRing>(
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
            verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(used);
            T::axiom_eqv_symmetric(T::zero().add(used), used);
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                used, T::zero().add(used), available,
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
pub proof fn lemma_column_child_x_lower_bound<T: OrderedRing>(
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
pub proof fn lemma_column_child_x_upper_bound<T: OrderedRing>(
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
pub proof fn lemma_row_child_y_lower_bound<T: OrderedRing>(
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
pub proof fn lemma_row_child_y_upper_bound<T: OrderedRing>(
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
proof fn lemma_add_swap_last<T: OrderedRing>(a: T, b: T, c: T)
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

} // verus!
