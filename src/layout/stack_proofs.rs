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

// ── Stack size commutativity ─────────────────────────────────────

/// Swap two elements in a sequence.
pub open spec fn swap_seq<A>(s: Seq<A>, i: nat, j: nat) -> Seq<A> {
    s.update(i as int, s[j as int]).update(j as int, s[i as int])
}

/// max_width(sizes, n) <= bound when every element width <= bound.
proof fn lemma_max_width_upper_bound<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
    bound: T,
)
    requires
        n <= sizes.len(),
        T::zero().le(bound),
        forall|k: int| 0 <= k < n ==> sizes[k].width.le(bound),
    ensures
        max_width(sizes, n).le(bound),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_max_width_upper_bound(sizes, (n - 1) as nat, bound);
        // max_width(n) = max(max_width(n-1), sizes[n-1].width)
        // max_width(n-1) <= bound, sizes[n-1].width <= bound
        // max(a, b) <= c when a <= c and b <= c
        T::axiom_le_total(max_width(sizes, (n - 1) as nat), sizes[(n - 1) as int].width);
        if max_width(sizes, (n - 1) as nat).le(sizes[(n - 1) as int].width) {
            // max = sizes[n-1].width <= bound
        } else {
            // max = max_width(n-1) <= bound
        }
    }
}

/// Every element of swap_seq is bounded by max_width of the original.
proof fn lemma_swap_elements_bounded_by_max_width<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        forall|k: int| 0 <= k < sizes.len() as int ==>
            swap_seq(sizes, i, j)[k].width.le(
                max_width(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);
    assert forall|k: int| 0 <= k < sizes.len() as int implies
        t[k].width.le(max_width(sizes, n))
    by {
        if k == j as int {
            // t[j] = sizes[i]
            lemma_max_width_bounds_child(sizes, i);
        } else if k == i as int {
            // t[i] = sizes[j]
            lemma_max_width_bounds_child(sizes, j);
        } else {
            // t[k] = sizes[k]
            lemma_max_width_bounds_child(sizes, k as nat);
        }
    }
}

/// Swapping two children doesn't change max_width.
pub proof fn lemma_max_width_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        max_width(swap_seq(sizes, i, j), sizes.len() as nat).eqv(
            max_width(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);

    // Nonneg bounds for upper_bound preconditions
    lemma_max_width_nonneg(sizes, n);
    // t has same elements, so nonneg widths carry over
    assert forall|k: int| 0 <= k < t.len() implies T::zero().le(t[k].width) by {
        if k == i as int { } else if k == j as int { } else { }
    }
    lemma_max_width_nonneg(t, n);

    // Direction 1: max_width(t, n) <= max_width(s, n)
    lemma_swap_elements_bounded_by_max_width(sizes, i, j);
    lemma_max_width_upper_bound(t, n, max_width(sizes, n));

    // Direction 2: max_width(s, n) <= max_width(t, n)
    assert forall|k: int| 0 <= k < n as int implies
        sizes[k].width.le(max_width(t, n))
    by {
        if k == i as int {
            lemma_max_width_bounds_child(t, j);
        } else if k == j as int {
            lemma_max_width_bounds_child(t, i);
        } else {
            lemma_max_width_bounds_child(t, k as nat);
        }
    }
    lemma_max_width_upper_bound(sizes, n, max_width(t, n));

    T::axiom_le_antisymmetric(
        max_width(t, n),
        max_width(sizes, n),
    );
}

/// Every element of swap_seq is bounded by max_height of the original.
proof fn lemma_swap_elements_bounded_by_max_height<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        forall|k: int| 0 <= k < sizes.len() as int ==>
            swap_seq(sizes, i, j)[k].height.le(
                max_height(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);
    assert forall|k: int| 0 <= k < sizes.len() as int implies
        t[k].height.le(max_height(sizes, n))
    by {
        if k == j as int {
            lemma_max_height_bounds_child(sizes, i);
        } else if k == i as int {
            lemma_max_height_bounds_child(sizes, j);
        } else {
            lemma_max_height_bounds_child(sizes, k as nat);
        }
    }
}

/// max_height(sizes, n) <= bound when every element height <= bound.
proof fn lemma_max_height_upper_bound<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
    bound: T,
)
    requires
        n <= sizes.len(),
        T::zero().le(bound),
        forall|k: int| 0 <= k < n ==> sizes[k].height.le(bound),
    ensures
        max_height(sizes, n).le(bound),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_max_height_upper_bound(sizes, (n - 1) as nat, bound);
        T::axiom_le_total(max_height(sizes, (n - 1) as nat), sizes[(n - 1) as int].height);
    }
}

/// Swapping two children doesn't change max_height.
pub proof fn lemma_max_height_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        max_height(swap_seq(sizes, i, j), sizes.len() as nat).eqv(
            max_height(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);

    // Nonneg bounds for upper_bound preconditions
    lemma_max_height_nonneg(sizes, n);
    assert forall|k: int| 0 <= k < t.len() implies T::zero().le(t[k].height) by {
        if k == i as int { } else if k == j as int { } else { }
    }
    lemma_max_height_nonneg(t, n);

    // Direction 1: max_height(t, n) <= max_height(s, n)
    lemma_swap_elements_bounded_by_max_height(sizes, i, j);
    lemma_max_height_upper_bound(t, n, max_height(sizes, n));

    // Direction 2: max_height(s, n) <= max_height(t, n)
    assert forall|k: int| 0 <= k < n as int implies
        sizes[k].height.le(max_height(t, n))
    by {
        if k == i as int {
            lemma_max_height_bounds_child(t, j);
        } else if k == j as int {
            lemma_max_height_bounds_child(t, i);
        } else {
            lemma_max_height_bounds_child(t, k as nat);
        }
    }
    lemma_max_height_upper_bound(sizes, n, max_height(t, n));

    T::axiom_le_antisymmetric(
        max_height(t, n),
        max_height(sizes, n),
    );
}

/// Stack parent size is invariant under swapping two children.
pub proof fn lemma_stack_content_size_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> sizes[k].is_nonneg(),
    ensures
        stack_content_size(swap_seq(sizes, i, j)).width.eqv(
            stack_content_size(sizes).width),
        stack_content_size(swap_seq(sizes, i, j)).height.eqv(
            stack_content_size(sizes).height),
{
    lemma_max_width_swap(sizes, i, j);
    lemma_max_height_swap(sizes, i, j);
}

} // verus!
