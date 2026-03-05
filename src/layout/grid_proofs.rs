use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::layout::*;
use crate::layout::grid::*;
use crate::layout::proofs::*;

verus! {

// ── Grid content size non-negativity ────────────────────────────────

/// Grid content width is non-negative.
pub proof fn lemma_grid_content_width_nonneg<T: OrderedRing>(
    col_widths: Seq<Size<T>>,
    h_spacing: T,
)
    requires
        T::zero().le(h_spacing),
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
    ensures
        T::zero().le(grid_content_width(col_widths, h_spacing)),
{
    if col_widths.len() == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_widths_nonneg(col_widths, col_widths.len() as nat);
        lemma_repeated_add_nonneg(h_spacing, (col_widths.len() - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_widths(col_widths, col_widths.len() as nat),
            T::zero(), repeated_add(h_spacing, (col_widths.len() - 1) as nat),
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        let total = sum_widths(col_widths, col_widths.len() as nat)
            .add(repeated_add(h_spacing, (col_widths.len() - 1) as nat));
        T::axiom_eqv_reflexive(total);
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            total, total,
        );
    }
}

/// Grid content height is non-negative.
pub proof fn lemma_grid_content_height_nonneg<T: OrderedRing>(
    row_heights: Seq<Size<T>>,
    v_spacing: T,
)
    requires
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
    ensures
        T::zero().le(grid_content_height(row_heights, v_spacing)),
{
    if row_heights.len() == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_heights_nonneg(row_heights, row_heights.len() as nat);
        lemma_repeated_add_nonneg(v_spacing, (row_heights.len() - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_heights(row_heights, row_heights.len() as nat),
            T::zero(), repeated_add(v_spacing, (row_heights.len() - 1) as nat),
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        let total = sum_heights(row_heights, row_heights.len() as nat)
            .add(repeated_add(v_spacing, (row_heights.len() - 1) as nat));
        T::axiom_eqv_reflexive(total);
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            total, total,
        );
    }
}

// ── Grid cells don't overlap ────────────────────────────────────────

/// grid_cell_x(pl, cw, sp, col) ≡ child_x_position(pl, cw, sp, col).
///
/// The closed-form grid position matches the recursive column position.
proof fn lemma_grid_cell_x_eq_child_x<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col: nat,
)
    requires
        col <= col_widths.len(),
    ensures
        child_x_position(padding_left, col_widths, h_spacing, col).eqv(
            grid_cell_x(padding_left, col_widths, h_spacing, col)
        ),
{
    // child_x_position ≡ pl + sum_widths + repeated_add by identity lemma
    // grid_cell_x is DEFINED as pl + sum_widths + repeated_add
    lemma_child_x_position_identity(padding_left, col_widths, h_spacing, col);
}

/// grid_cell_y(pt, rh, sp, row) ≡ child_y_position(pt, rh, sp, row).
proof fn lemma_grid_cell_y_eq_child_y<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row: nat,
)
    requires
        row <= row_heights.len(),
    ensures
        child_y_position(padding_top, row_heights, v_spacing, row).eqv(
            grid_cell_y(padding_top, row_heights, v_spacing, row)
        ),
{
    lemma_child_y_position_identity(padding_top, row_heights, v_spacing, row);
}

/// Cells in the same row at consecutive columns don't overlap horizontally:
/// grid_cell_x(col) + col_widths[col].width <= grid_cell_x(col + 1).
pub proof fn lemma_grid_columns_nonoverlapping<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col: nat,
)
    requires
        (col + 1) < col_widths.len(),
        T::zero().le(h_spacing),
    ensures
        grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width)
            .le(grid_cell_x(padding_left, col_widths, h_spacing, col + 1)),
{
    // child_x_position(col) + cw[col].width <= child_x_position(col+1)
    // (from row non-overlapping lemma, which uses child_x_position)
    lemma_row_children_nonoverlapping(padding_left, col_widths, h_spacing, col);

    // child_x_position(col) ≡ grid_cell_x(col)
    lemma_grid_cell_x_eq_child_x(padding_left, col_widths, h_spacing, col);
    // child_x_position(col+1) ≡ grid_cell_x(col+1)
    lemma_grid_cell_x_eq_child_x(padding_left, col_widths, h_spacing, col + 1);

    // Chain congruence:
    // child_x_position(col) + cw ≡ grid_cell_x(col) + cw
    T::axiom_add_congruence_left(
        child_x_position(padding_left, col_widths, h_spacing, col),
        grid_cell_x(padding_left, col_widths, h_spacing, col),
        col_widths[col as int].width,
    );

    // left side: child_x(col)+cw ≡ grid_cell_x(col)+cw, and child_x(col)+cw <= child_x(col+1)
    // so grid_cell_x(col)+cw <= child_x(col+1)
    T::axiom_eqv_symmetric(
        child_x_position(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width),
        grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        child_x_position(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width),
        grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width),
        child_x_position(padding_left, col_widths, h_spacing, col + 1),
    );

    // right side: child_x(col+1) ≡ grid_cell_x(col+1)
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width),
        child_x_position(padding_left, col_widths, h_spacing, col + 1),
        grid_cell_x(padding_left, col_widths, h_spacing, col + 1),
    );
}

/// Cells in the same column at consecutive rows don't overlap vertically.
pub proof fn lemma_grid_rows_nonoverlapping<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row: nat,
)
    requires
        (row + 1) < row_heights.len(),
        T::zero().le(v_spacing),
    ensures
        grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height)
            .le(grid_cell_y(padding_top, row_heights, v_spacing, row + 1)),
{
    // child_y_position(row) + rh[row].height <= child_y_position(row+1)
    lemma_column_children_nonoverlapping(padding_top, row_heights, v_spacing, row);

    // Bridge via identity: child_y_position ≡ grid_cell_y
    lemma_grid_cell_y_eq_child_y(padding_top, row_heights, v_spacing, row);
    lemma_grid_cell_y_eq_child_y(padding_top, row_heights, v_spacing, row + 1);

    T::axiom_add_congruence_left(
        child_y_position(padding_top, row_heights, v_spacing, row),
        grid_cell_y(padding_top, row_heights, v_spacing, row),
        row_heights[row as int].height,
    );

    T::axiom_eqv_symmetric(
        child_y_position(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height),
        grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        child_y_position(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height),
        grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height),
        child_y_position(padding_top, row_heights, v_spacing, row + 1),
    );

    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height),
        child_y_position(padding_top, row_heights, v_spacing, row + 1),
        grid_cell_y(padding_top, row_heights, v_spacing, row + 1),
    );
}

// ── sum_widths non-negativity ───────────────────────────────────────

/// If all child widths are non-negative, then sum_widths(sizes, n) is non-negative.
pub proof fn lemma_sum_widths_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].width),
    ensures
        T::zero().le(sum_widths(sizes, n)),
    decreases n,
{
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_sum_widths_nonneg(sizes, (n - 1) as nat);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), sum_widths(sizes, (n - 1) as nat),
            T::zero(), sizes[(n - 1) as int].width,
        );
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
        T::axiom_eqv_reflexive(
            sum_widths(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].width)
        );
        T::axiom_le_congruence(
            T::zero().add(T::zero()), T::zero(),
            sum_widths(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].width),
            sum_widths(sizes, (n - 1) as nat).add(sizes[(n - 1) as int].width),
        );
    }
}

// ── Grid children length/element lemmas ───────────────────────────

/// Length of grid_row_children.
pub proof fn lemma_grid_row_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    row: nat,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    col: nat,
)
    requires
        row < child_sizes.len(),
        col <= col_widths.len(),
        child_sizes[row as int].len() >= col_widths.len(),
    ensures
        grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, col,
        ).len() == (col_widths.len() - col) as nat,
    decreases col_widths.len() - col,
{
    if col >= col_widths.len() {
    } else {
        lemma_grid_row_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, col + 1,
        );
    }
}

/// Element access into grid_row_children.
pub proof fn lemma_grid_row_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    row: nat,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    k: nat,
)
    requires
        row < child_sizes.len(),
        k < col_widths.len(),
        child_sizes[row as int].len() >= col_widths.len(),
    ensures
        grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, 0,
        )[k as int]
            == grid_child(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, row, k, child_sizes[row as int][k as int],
            ),
{
    lemma_grid_row_children_element_shifted(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, row, child_sizes, 0, k,
    );
}

proof fn lemma_grid_row_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    row: nat,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    start: nat,
    k: nat,
)
    requires
        row < child_sizes.len(),
        start <= k,
        k < col_widths.len(),
        child_sizes[row as int].len() >= col_widths.len(),
    ensures
        grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start,
        )[(k - start) as int]
            == grid_child(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, row, k, child_sizes[row as int][k as int],
            ),
    decreases k - start,
{
    if start == k {
    } else {
        lemma_grid_row_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start + 1,
        );
        lemma_grid_row_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start,
        );
        lemma_grid_row_children_element_shifted(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start + 1, k,
        );
        let tail = grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start + 1,
        );
        let gr = grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, start,
        );
        assert(gr[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

/// Length of grid_all_children = (remaining rows) * num_cols.
pub proof fn lemma_grid_all_children_len<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    row: nat,
    num_cols: nat,
)
    requires
        row <= row_heights.len(),
        child_sizes.len() >= row_heights.len(),
        num_cols == col_widths.len(),
        forall|r: int| 0 <= r < child_sizes.len() ==> child_sizes[r].len() >= num_cols,
    ensures
        grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row,
        ).len() == (row_heights.len() - row) * num_cols,
    decreases row_heights.len() - row,
{
    if row >= row_heights.len() {
        assert(grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row,
        ).len() == 0nat);
        assert((row_heights.len() - row) * num_cols == 0nat);
    } else {
        lemma_grid_row_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, 0,
        );
        lemma_grid_all_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row + 1, num_cols,
        );
        let rc = grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, 0,
        );
        let rest = grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row + 1,
        );
        assert(rc.len() == num_cols);
        assert(rest.len() == (row_heights.len() - row - 1) * num_cols);
        assert(grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row,
        ).len() == rc.len() + rest.len());
        // Bridge: rc.len() + rest.len() == target
        assert(rc.len() + rest.len() == (row_heights.len() - row) * num_cols)
            by (nonlinear_arith)
            requires
                rc.len() == num_cols,
                rest.len() == (row_heights.len() - row - 1) * num_cols,
                row < row_heights.len(),
        ;
        // Final chain
        assert(grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, row,
        ).len() == (row_heights.len() - row) * num_cols);
    }
}

/// Flat element access: grid_all_children(0)[row * ncols + col] == grid_child(row, col, ...).
pub proof fn lemma_grid_all_children_element<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    row: nat,
    col: nat,
)
    requires
        row < row_heights.len(),
        col < col_widths.len(),
        child_sizes.len() >= row_heights.len(),
        forall|r: int| 0 <= r < child_sizes.len() ==>
            (#[trigger] child_sizes[r]).len() >= col_widths.len(),
    ensures
        grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, 0,
        )[(row * col_widths.len() + col) as int]
            == grid_child(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, row, col, child_sizes[row as int][col as int],
            ),
{
    lemma_grid_all_children_element_shifted(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes, 0, row, col,
    );
}

proof fn lemma_grid_all_children_element_shifted<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<crate::size::Size<T>>,
    row_heights: Seq<crate::size::Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    child_sizes: Seq<Seq<crate::size::Size<T>>>,
    start_row: nat,
    row: nat,
    col: nat,
)
    requires
        start_row <= row,
        row < row_heights.len(),
        col < col_widths.len(),
        child_sizes.len() >= row_heights.len(),
        forall|r: int| 0 <= r < child_sizes.len() ==>
            (#[trigger] child_sizes[r]).len() >= col_widths.len(),
    ensures
        grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, start_row,
        )[((row - start_row) * col_widths.len() + col) as int]
            == grid_child(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, row, col, child_sizes[row as int][col as int],
            ),
    decreases row - start_row,
{
    let ncols = col_widths.len();
    lemma_grid_row_children_len(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, start_row, child_sizes, 0,
    );
    // rc.len() == ncols

    let rc = grid_row_children(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, start_row, child_sizes, 0,
    );
    let rest = grid_all_children(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes, start_row + 1,
    );
    let all = grid_all_children(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes, start_row,
    );
    assert(rc.len() == ncols);

    if row == start_row {
        lemma_grid_row_children_element(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, col,
        );
        assert((row - start_row) * ncols + col == col)
            by (nonlinear_arith) requires row == start_row;
        assert(all[col as int] == rc[col as int]);
    } else {
        lemma_grid_all_children_len(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, start_row + 1, ncols,
        );
        // rest.len() == (row_heights.len() - start_row - 1) * ncols

        lemma_grid_all_children_element_shifted(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes, start_row + 1, row, col,
        );

        let flat_idx: int = (row - start_row) as int * ncols as int + col as int;
        let rest_idx: int = (row - start_row - 1) as int * ncols as int + col as int;

        let rest_len: int = rest.len() as int;
        let rh_len: int = row_heights.len() as int;
        let row_i: int = row as int;
        let sr_i: int = start_row as int;
        let nc_i: int = ncols as int;
        let col_i: int = col as int;

        assert(rest_idx >= 0) by (nonlinear_arith)
            requires
                rest_idx == (row_i - sr_i - 1) * nc_i + col_i,
                row_i > sr_i, nc_i >= 0, col_i >= 0;
        assert(rest_idx < rest_len) by (nonlinear_arith)
            requires
                rest_idx == (row_i - sr_i - 1) * nc_i + col_i,
                rest_len == (rh_len - sr_i - 1) * nc_i,
                row_i < rh_len, sr_i < row_i, col_i < nc_i,
                nc_i > 0, row_i - sr_i <= rh_len - sr_i - 1;
        assert(flat_idx >= nc_i) by (nonlinear_arith)
            requires
                flat_idx == (row_i - sr_i) * nc_i + col_i,
                row_i > sr_i, nc_i > 0, col_i >= 0;
        assert(flat_idx - nc_i == rest_idx) by (nonlinear_arith)
            requires
                flat_idx == (row_i - sr_i) * nc_i + col_i,
                rest_idx == (row_i - sr_i - 1) * nc_i + col_i,
                row_i > sr_i, nc_i > 0;

        assert(all[flat_idx] == rest[rest_idx]);
    }
}

} // verus!
