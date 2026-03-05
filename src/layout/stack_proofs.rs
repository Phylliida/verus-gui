use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::*;
use crate::size::Size;
use crate::layout::stack::*;
use crate::layout::proofs::{lemma_align_offset_nonneg, lemma_align_offset_bounded, lemma_le_add_nonneg};
use crate::alignment::{Alignment, align_offset};

verus! {

// ── max_width / max_height non-negativity ───────────────────────────

/// max_width is non-negative when all child widths are non-negative.
pub proof fn lemma_max_width_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].width),
    ensures
        T::zero().le(max_width(sizes, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_max_width_nonneg(sizes, (n - 1) as nat);
        // max(prev, sizes[n-1].width) >= prev >= 0
        lemma_max_ge_left::<T>(
            max_width(sizes, (n - 1) as nat),
            sizes[(n - 1) as int].width,
        );
        T::axiom_le_transitive(
            T::zero(),
            max_width(sizes, (n - 1) as nat),
            max::<T>(max_width(sizes, (n - 1) as nat), sizes[(n - 1) as int].width),
        );
    }
}

/// max_height is non-negative when all child heights are non-negative.
pub proof fn lemma_max_height_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].height),
    ensures
        T::zero().le(max_height(sizes, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_max_height_nonneg(sizes, (n - 1) as nat);
        lemma_max_ge_left::<T>(
            max_height(sizes, (n - 1) as nat),
            sizes[(n - 1) as int].height,
        );
        T::axiom_le_transitive(
            T::zero(),
            max_height(sizes, (n - 1) as nat),
            max::<T>(max_height(sizes, (n - 1) as nat), sizes[(n - 1) as int].height),
        );
    }
}

/// The stack content size is non-negative when all children have non-negative sizes.
pub proof fn lemma_stack_content_size_nonneg<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
)
    requires
        forall|i: int| 0 <= i < child_sizes.len() ==> child_sizes[i].is_nonneg(),
    ensures
        stack_content_size(child_sizes).is_nonneg(),
{
    lemma_max_width_nonneg(child_sizes, child_sizes.len() as nat);
    lemma_max_height_nonneg(child_sizes, child_sizes.len() as nat);
}

// ── max_width / max_height bound each child ─────────────────────────

/// Each child's width is <= max_width.
pub proof fn lemma_max_width_bounds_child<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].width),
    ensures
        sizes[i as int].width.le(max_width(sizes, sizes.len() as nat)),
    decreases sizes.len() - i,
{
    let n = sizes.len() as nat;
    // sizes[i].width <= max_width(sizes, i+1) <= max_width(sizes, n)
    lemma_max_width_contains(sizes, i);
    lemma_max_width_monotone(sizes, (i + 1) as nat, n);
    T::axiom_le_transitive(
        sizes[i as int].width,
        max_width(sizes, (i + 1) as nat),
        max_width(sizes, n),
    );
}

/// max_width(sizes, i+1) >= sizes[i].width (the latest element is in the max).
proof fn lemma_max_width_contains<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
    ensures
        sizes[i as int].width.le(max_width(sizes, (i + 1) as nat)),
{
    // max_width(sizes, i+1) = max(max_width(sizes, i), sizes[i].width) >= sizes[i].width
    lemma_max_ge_right::<T>(max_width(sizes, i), sizes[i as int].width);
}

/// max_width is monotone: i <= j implies max_width(sizes, i) <= max_width(sizes, j).
proof fn lemma_max_width_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        max_width(sizes, i).le(max_width(sizes, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(max_width(sizes, i));
    } else {
        lemma_max_width_monotone(sizes, i, (j - 1) as nat);
        // max_width(j) = max(max_width(j-1), sizes[j-1].width) >= max_width(j-1)
        lemma_max_ge_left::<T>(max_width(sizes, (j - 1) as nat), sizes[(j - 1) as int].width);
        T::axiom_le_transitive(
            max_width(sizes, i),
            max_width(sizes, (j - 1) as nat),
            max_width(sizes, j),
        );
    }
}

/// Each child's height is <= max_height.
pub proof fn lemma_max_height_bounds_child<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].height),
    ensures
        sizes[i as int].height.le(max_height(sizes, sizes.len() as nat)),
    decreases sizes.len() - i,
{
    let n = sizes.len() as nat;
    lemma_max_height_contains(sizes, i);
    lemma_max_height_monotone(sizes, (i + 1) as nat, n);
    T::axiom_le_transitive(
        sizes[i as int].height,
        max_height(sizes, (i + 1) as nat),
        max_height(sizes, n),
    );
}

/// max_height(sizes, i+1) >= sizes[i].height.
proof fn lemma_max_height_contains<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
    ensures
        sizes[i as int].height.le(max_height(sizes, (i + 1) as nat)),
{
    lemma_max_ge_right::<T>(max_height(sizes, i), sizes[i as int].height);
}

/// max_height is monotone.
proof fn lemma_max_height_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        max_height(sizes, i).le(max_height(sizes, j)),
    decreases j - i,
{
    if i == j {
        T::axiom_le_reflexive(max_height(sizes, i));
    } else {
        lemma_max_height_monotone(sizes, i, (j - 1) as nat);
        lemma_max_ge_left::<T>(max_height(sizes, (j - 1) as nat), sizes[(j - 1) as int].height);
        T::axiom_le_transitive(
            max_height(sizes, i),
            max_height(sizes, (j - 1) as nat),
            max_height(sizes, j),
        );
    }
}

// ── Stack child within bounds ───────────────────────────────────────

/// Each child in a stack fits within the available space.
/// Child x-position >= padding_left and child right edge <= padding_left + available_width.
/// Child y-position >= padding_top and child bottom edge <= padding_top + available_height.
pub proof fn lemma_stack_child_within_bounds<T: OrderedField>(
    padding_left: T,
    padding_top: T,
    h_align: Alignment,
    v_align: Alignment,
    available_width: T,
    available_height: T,
    child_width: T,
    child_height: T,
)
    requires
        child_width.le(available_width),
        child_height.le(available_height),
    ensures
        // x lower bound
        padding_left.le(
            padding_left.add(align_offset(h_align, available_width, child_width))
        ),
        // x upper bound
        padding_left.add(align_offset(h_align, available_width, child_width))
            .add(child_width)
            .le(padding_left.add(available_width)),
        // y lower bound
        padding_top.le(
            padding_top.add(align_offset(v_align, available_height, child_height))
        ),
        // y upper bound
        padding_top.add(align_offset(v_align, available_height, child_height))
            .add(child_height)
            .le(padding_top.add(available_height)),
{
    // x bounds: direct from alignment lemmas
    lemma_align_offset_nonneg(h_align, available_width, child_width);
    lemma_le_add_nonneg(padding_left, align_offset(h_align, available_width, child_width));

    crate::layout::proofs::lemma_column_child_x_upper_bound(
        padding_left, h_align, available_width, child_width,
    );

    // y bounds: direct from alignment lemmas
    lemma_align_offset_nonneg(v_align, available_height, child_height);
    lemma_le_add_nonneg(padding_top, align_offset(v_align, available_height, child_height));

    crate::layout::proofs::lemma_row_child_y_upper_bound(
        padding_top, v_align, available_height, child_height,
    );
}

} // verus!
