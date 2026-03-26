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

// ── Grid cell position lower bounds ─────────────────────────────────

/// grid_cell_x(col) >= padding_left when widths and spacing are nonneg.
proof fn lemma_grid_cell_x_lower_bound<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col: nat,
)
    requires
        col <= col_widths.len(),
        T::zero().le(h_spacing),
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
    ensures
        padding_left.le(grid_cell_x(padding_left, col_widths, h_spacing, col)),
{
    // grid_cell_x = padding_left + sum_widths(col) + repeated_add(h_sp, col)
    // sum_widths(col) >= 0 and repeated_add(h_sp, col) >= 0
    lemma_sum_widths_nonneg(col_widths, col);
    lemma_repeated_add_nonneg(h_spacing, col);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        T::zero(), sum_widths(col_widths, col),
        T::zero(), repeated_add(h_spacing, col),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
    let offset = sum_widths(col_widths, col).add(repeated_add(h_spacing, col));
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero().add(T::zero()), T::zero(), offset,
    );
    // 0 <= offset, so padding_left <= padding_left + offset
    lemma_le_add_nonneg(padding_left, offset);
    // padding_left + offset ≡ grid_cell_x via associativity
    // assoc: (pl + sw) + ra ≡ pl + (sw + ra) = pl + offset
    // So grid_cell_x ≡ pl + offset. Need symmetric for le_congruence_right.
    T::axiom_add_associative(padding_left, sum_widths(col_widths, col),
        repeated_add(h_spacing, col));
    T::axiom_eqv_symmetric(
        padding_left.add(sum_widths(col_widths, col)).add(repeated_add(h_spacing, col)),
        padding_left.add(offset),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding_left, padding_left.add(offset),
        padding_left.add(sum_widths(col_widths, col)).add(repeated_add(h_spacing, col)),
    );
}

/// grid_cell_y(row) >= padding_top when heights and spacing are nonneg.
proof fn lemma_grid_cell_y_lower_bound<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row: nat,
)
    requires
        row <= row_heights.len(),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
    ensures
        padding_top.le(grid_cell_y(padding_top, row_heights, v_spacing, row)),
{
    lemma_sum_heights_nonneg(row_heights, row);
    lemma_repeated_add_nonneg(v_spacing, row);
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
        T::zero(), sum_heights(row_heights, row),
        T::zero(), repeated_add(v_spacing, row),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_symmetric(T::zero().add(T::zero()), T::zero());
    let offset = sum_heights(row_heights, row).add(repeated_add(v_spacing, row));
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero().add(T::zero()), T::zero(), offset,
    );
    lemma_le_add_nonneg(padding_top, offset);
    T::axiom_add_associative(padding_top, sum_heights(row_heights, row),
        repeated_add(v_spacing, row));
    T::axiom_eqv_symmetric(
        padding_top.add(sum_heights(row_heights, row)).add(repeated_add(v_spacing, row)),
        padding_top.add(offset),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        padding_top, padding_top.add(offset),
        padding_top.add(sum_heights(row_heights, row)).add(repeated_add(v_spacing, row)),
    );
}

// ── Grid cell position upper bounds ─────────────────────────────────

/// grid_cell_x(col) + col_widths[col].width <= padding_left + content_width.
/// Uses lemma_row_child_x_upper_bound + bridge via grid_cell_x ≡ child_x_position.
proof fn lemma_grid_cell_x_plus_width_bounded<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col: nat,
)
    requires
        col < col_widths.len(),
        T::zero().le(h_spacing),
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
    ensures
        grid_cell_x(padding_left, col_widths, h_spacing, col)
            .add(col_widths[col as int].width)
            .le(padding_left.add(grid_content_width(col_widths, h_spacing))),
{
    // child_x_position(pl, cw, sp, col) + cw[col].w <= pl + row_content_width(cw, sp)
    lemma_row_child_x_upper_bound(padding_left, col_widths, h_spacing, col);
    // row_content_width == grid_content_width (definitionally equal)

    // child_x_position ≡ grid_cell_x
    lemma_grid_cell_x_eq_child_x(padding_left, col_widths, h_spacing, col);
    // Bridge: child_x_position(col) + cw ≡ grid_cell_x(col) + cw
    T::axiom_add_congruence_left(
        child_x_position(padding_left, col_widths, h_spacing, col),
        grid_cell_x(padding_left, col_widths, h_spacing, col),
        col_widths[col as int].width,
    );
    // Symmetric direction for le_congruence_left
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
        padding_left.add(row_content_width(col_widths, h_spacing)),
    );
}

/// grid_cell_y(row) + row_heights[row].height <= padding_top + content_height.
proof fn lemma_grid_cell_y_plus_height_bounded<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row: nat,
)
    requires
        row < row_heights.len(),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
    ensures
        grid_cell_y(padding_top, row_heights, v_spacing, row)
            .add(row_heights[row as int].height)
            .le(padding_top.add(grid_content_height(row_heights, v_spacing))),
{
    lemma_column_child_y_upper_bound(padding_top, row_heights, v_spacing, row);
    // column_content_height == grid_content_height (definitionally equal)

    lemma_grid_cell_y_eq_child_y(padding_top, row_heights, v_spacing, row);
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
        padding_top.add(column_content_height(row_heights, v_spacing)),
    );
}

// ── Grid children within bounds ─────────────────────────────────────

/// Helper: per-child grid CWB for a single cell at (row, col).
proof fn lemma_grid_child_cwb<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    child_size: Size<T>,
    parent_w: T,
    parent_h: T,
    row: nat,
    col: nat,
)
    requires
        row < row_heights.len(),
        col < col_widths.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        padding.is_nonneg(),
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
        child_size.width.le(grid_col_width(col_widths, col)),
        child_size.height.le(grid_row_height(row_heights, row)),
        padding.horizontal().add(grid_content_width(col_widths, h_spacing)).le(parent_w),
        padding.vertical().add(grid_content_height(row_heights, v_spacing)).le(parent_h),
    ensures ({
        let child = grid_child(padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, col, child_size);
        &&& T::zero().le(child.x)
        &&& T::zero().le(child.y)
        &&& child.x.add(child_size.width).le(parent_w)
        &&& child.y.add(child_size.height).le(parent_h)
    }),
{
    let cell_x = grid_cell_x(padding.left, col_widths, h_spacing, col);
    let cell_y = grid_cell_y(padding.top, row_heights, v_spacing, row);
    let cell_w = grid_col_width(col_widths, col);
    let cell_h = grid_row_height(row_heights, row);
    let child = grid_child(padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, row, col, child_size);

    // --- Lower bounds ---
    // cell_x >= padding.left >= 0
    lemma_grid_cell_x_lower_bound(padding.left, col_widths, h_spacing, col);
    T::axiom_le_transitive(T::zero(), padding.left, cell_x);
    // align_offset >= 0
    lemma_align_offset_nonneg(h_align, cell_w, child_size.width);
    // child.x = cell_x + align_offset >= cell_x >= 0
    lemma_le_add_nonneg(cell_x, align_offset(h_align, cell_w, child_size.width));
    T::axiom_le_transitive(T::zero(), cell_x, child.x);

    // cell_y >= padding.top >= 0
    lemma_grid_cell_y_lower_bound(padding.top, row_heights, v_spacing, row);
    T::axiom_le_transitive(T::zero(), padding.top, cell_y);
    lemma_align_offset_nonneg(v_align, cell_h, child_size.height);
    lemma_le_add_nonneg(cell_y, align_offset(v_align, cell_h, child_size.height));
    T::axiom_le_transitive(T::zero(), cell_y, child.y);

    // --- X upper bound ---
    // child.x + child_w = (cell_x + align_off) + child_w ≡ cell_x + (align_off + child_w)
    let ao_x = align_offset(h_align, cell_w, child_size.width);
    T::axiom_add_associative(cell_x, ao_x, child_size.width);
    // align_off + child_w <= cell_w (from align_offset_bounded)
    lemma_align_offset_bounded(h_align, cell_w, child_size.width);
    // cell_x + (ao + child_w) <= cell_x + cell_w
    T::axiom_le_add_monotone(ao_x.add(child_size.width), cell_w, cell_x);
    T::axiom_add_commutative(ao_x.add(child_size.width), cell_x);
    T::axiom_add_commutative(cell_w, cell_x);
    T::axiom_le_congruence(
        ao_x.add(child_size.width).add(cell_x), cell_x.add(ao_x.add(child_size.width)),
        cell_w.add(cell_x), cell_x.add(cell_w),
    );
    // assoc gives: child.x + child_w = (cell_x + ao) + cw ≡ cell_x + (ao + cw)
    // Need symmetric for le_congruence_left
    T::axiom_eqv_symmetric(
        cell_x.add(ao_x).add(child_size.width),
        cell_x.add(ao_x.add(child_size.width)),
    );
    // child.x.add(child_w) ≡ cell_x.add(ao.add(cw))  [a1.eqv(a2)]
    // cell_x.add(ao.add(cw)).le(cell_x.add(cell_w))   [a1.le(b)]
    // => child.x.add(child_w).le(cell_x.add(cell_w))  [a2.le(b)]
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        cell_x.add(ao_x.add(child_size.width)),
        cell_x.add(ao_x).add(child_size.width),
        cell_x.add(cell_w),
    );

    // cell_x + cell_w <= padding.left + content_width
    lemma_grid_cell_x_plus_width_bounded(padding.left, col_widths, h_spacing, col);

    // padding.left + content_width <= h + content_width
    let gcw = grid_content_width(col_widths, h_spacing);
    lemma_le_add_nonneg(padding.left, padding.right);
    T::axiom_le_add_monotone(padding.left, padding.horizontal(), gcw);
    T::axiom_add_commutative(padding.left, gcw);
    T::axiom_add_commutative(padding.horizontal(), gcw);
    T::axiom_le_congruence(
        padding.left.add(gcw), gcw.add(padding.left),
        padding.horizontal().add(gcw), gcw.add(padding.horizontal()),
    );

    // Chain: child.x + child_w <= cell_x + cell_w <= left + gcw <= h + gcw <= parent_w
    T::axiom_le_transitive(
        child.x.add(child_size.width), cell_x.add(cell_w),
        padding.left.add(gcw));
    T::axiom_le_transitive(
        child.x.add(child_size.width), padding.left.add(gcw),
        padding.horizontal().add(gcw));
    T::axiom_le_transitive(
        child.x.add(child_size.width), padding.horizontal().add(gcw), parent_w);

    // --- Y upper bound ---
    let ao_y = align_offset(v_align, cell_h, child_size.height);
    T::axiom_add_associative(cell_y, ao_y, child_size.height);
    lemma_align_offset_bounded(v_align, cell_h, child_size.height);
    T::axiom_le_add_monotone(ao_y.add(child_size.height), cell_h, cell_y);
    T::axiom_add_commutative(ao_y.add(child_size.height), cell_y);
    T::axiom_add_commutative(cell_h, cell_y);
    T::axiom_le_congruence(
        ao_y.add(child_size.height).add(cell_y), cell_y.add(ao_y.add(child_size.height)),
        cell_h.add(cell_y), cell_y.add(cell_h),
    );
    T::axiom_eqv_symmetric(
        cell_y.add(ao_y).add(child_size.height),
        cell_y.add(ao_y.add(child_size.height)),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        cell_y.add(ao_y.add(child_size.height)),
        cell_y.add(ao_y).add(child_size.height),
        cell_y.add(cell_h),
    );

    lemma_grid_cell_y_plus_height_bounded(padding.top, row_heights, v_spacing, row);

    let gch = grid_content_height(row_heights, v_spacing);
    lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, padding.vertical(), gch);
    T::axiom_add_commutative(padding.top, gch);
    T::axiom_add_commutative(padding.vertical(), gch);
    T::axiom_le_congruence(
        padding.top.add(gch), gch.add(padding.top),
        padding.vertical().add(gch), gch.add(padding.vertical()),
    );

    T::axiom_le_transitive(
        child.y.add(child_size.height), cell_y.add(cell_h),
        padding.top.add(gch));
    T::axiom_le_transitive(
        child.y.add(child_size.height), padding.top.add(gch),
        padding.vertical().add(gch));
    T::axiom_le_transitive(
        child.y.add(child_size.height), padding.vertical().add(gch), parent_h);
}

/// Per-child grid CWB: given (row, col) and child_size, prove bounds on the positioned child.
proof fn lemma_grid_per_child_cwb<T: OrderedField>(
    padding: crate::padding::Padding<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    child_sizes_2d: Seq<Seq<Size<T>>>,
    child_size: Size<T>,
    parent_w: T,
    parent_h: T,
    row: nat,
    col: nat,
)
    requires
        row < row_heights.len(),
        col < col_widths.len(),
        // child_sizes_2d structure
        child_sizes_2d.len() >= row_heights.len(),
        forall|r: int| 0 <= r < child_sizes_2d.len() ==>
            (#[trigger] child_sizes_2d[r]).len() >= col_widths.len(),
        child_sizes_2d[row as int][col as int] === child_size,
        // child fits in cell
        child_size.width.le(col_widths[col as int].width),
        child_size.height.le(row_heights[row as int].height),
        // Grid params
        padding.is_nonneg(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
        // Content fits in parent
        padding.horizontal().add(grid_content_width(col_widths, h_spacing)).le(parent_w),
        padding.vertical().add(grid_content_height(row_heights, v_spacing)).le(parent_h),
    ensures ({
        let child_node = grid_all_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes_2d, 0,
        )[(row * col_widths.len() + col) as int];
        &&& T::zero().le(child_node.x)
        &&& T::zero().le(child_node.y)
        &&& child_node.x.add(child_size.width).le(parent_w)
        &&& child_node.y.add(child_size.height).le(parent_h)
    }),
{
    lemma_grid_all_children_element(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes_2d, row, col,
    );

    lemma_grid_child_cwb(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_size, parent_w, parent_h,
        row, col,
    );
}

/// Grid layout has children_within_bounds.
pub proof fn lemma_grid_children_within_bounds<T: OrderedField>(
    limits: crate::limits::Limits<T>,
    padding: crate::padding::Padding<T>,
    h_spacing: T,
    v_spacing: T,
    h_align: crate::alignment::Alignment,
    v_align: crate::alignment::Alignment,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    children: Seq<crate::widget::Widget<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        col_widths.len() > 0,
        row_heights.len() > 0,
        children.len() == col_widths.len() * row_heights.len(),
        // Content fits
        padding.horizontal().add(grid_content_width(col_widths, h_spacing)).le(limits.max.width),
        padding.vertical().add(grid_content_height(row_heights, v_spacing)).le(limits.max.height),
        // Column widths and row heights are nonneg
        forall|i: int| 0 <= i < col_widths.len() ==> T::zero().le(col_widths[i].width),
        forall|i: int| 0 <= i < row_heights.len() ==> T::zero().le(row_heights[i].height),
        // Each child fits in its cell
        crate::layout::proofs::widget_wf_grid_cells_fit(
            limits, padding, col_widths, row_heights,
            children, (fuel - 1) as nat,
        ),
    ensures
        crate::widget::layout_widget(limits, crate::widget::Widget::Container(crate::widget::ContainerWidget::Grid {
            padding, h_spacing, v_spacing, h_align, v_align,
            col_widths, row_heights, children,
        }), fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let ncols = col_widths.len();
    let nrows = row_heights.len();
    let cn = crate::widget::grid_widget_child_nodes(
        inner, col_widths, row_heights, children,
        ncols, (fuel - 1) as nat,
    );

    // h, v >= 0
    lemma_nonneg_sum(padding.left, padding.right);
    lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf
    lemma_shrink_wf(limits, h, v);
    lemma_add_comm_le(h, limits.min.width, limits.max.width);
    lemma_add_comm_le(v, limits.min.height, limits.max.height);

    // child_sizes_2d for grid_layout
    let child_sizes_2d = Seq::new(nrows, |r: int|
        Seq::new(ncols, |c: int| cn[(r * ncols as int + c)].size)
    );
    // Help Z3 with nested Seq::new (can't beta-reduce nested Seq::new)
    assert(child_sizes_2d.len() == nrows);
    assert forall|r: int| 0 <= r < nrows as int implies
        (#[trigger] child_sizes_2d[r]).len() == ncols
    by {};
    assert forall|r: int, c: int|
        0 <= r < nrows as int && 0 <= c < ncols as int implies
        child_sizes_2d[r][c] === (#[trigger] cn[(r * ncols as int + c)]).size
    by {};

    // total size <= max
    let content_w = grid_content_width(col_widths, h_spacing);
    let content_h = grid_content_height(row_heights, v_spacing);
    let total_w = h.add(content_w);
    let total_h = v.add(content_h);
    crate::layout::proofs::lemma_resolve_ge_input(
        limits, Size::new(total_w, total_h),
    );
    let parent_size = limits.resolve(Size::new(total_w, total_h));

    reveal(grid_layout);
    let layout = grid_layout(limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, child_sizes_2d);

    // layout.children.len() == cn.len()
    lemma_grid_all_children_len(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes_2d, 0, ncols,
    );
    assert(layout.children.len() == nrows * ncols);
    assert(cn.len() == children.len());
    assert(cn.len() == ncols * nrows);
    assert(ncols * nrows == nrows * ncols) by (nonlinear_arith)
        requires ncols >= 0, nrows >= 0;
    assert(cn.len() == layout.children.len());

    // Per-child bounds via extracted helper
    assert forall|idx: int| 0 <= idx < cn.len() implies
        T::zero().le(layout.children[idx].x)
        && T::zero().le(layout.children[idx].y)
        && layout.children[idx].x.add(cn[idx].size.width).le(layout.size.width)
        && layout.children[idx].y.add(cn[idx].size.height).le(layout.size.height)
    by {
        // Compute (row, col) from flat index
        let row: nat = (idx / ncols as int) as nat;
        let col: nat = (idx % ncols as int) as nat;

        // Division/modulus bounds
        assert(col < ncols) by (nonlinear_arith)
            requires col == (idx % ncols as int) as nat, 0 <= idx, ncols > 0nat;
        assert(row < nrows) by (nonlinear_arith)
            requires row == (idx / ncols as int) as nat,
                0 <= idx, idx < (ncols * nrows) as int,
                ncols > 0nat, nrows > 0nat;
        assert(idx == row as int * ncols as int + col as int) by (nonlinear_arith)
            requires row == (idx / ncols as int) as nat,
                col == (idx % ncols as int) as nat,
                0 <= idx, idx < (ncols * nrows) as int,
                ncols > 0nat;

        // Connect child_sizes_2d to cn
        assert(child_sizes_2d[row as int][col as int] === cn[idx].size);

        lemma_grid_per_child_cwb(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, child_sizes_2d, cn[idx].size,
            parent_size.width, parent_size.height,
            row, col,
        );
    };

    crate::layout::proofs::lemma_merge_layout_cwb(layout, cn);
}

// ── Grid cell non-overlapping (arbitrary pairs) ─────────────────

/// Columns non-overlapping for arbitrary col1 < col2 (not just consecutive).
pub proof fn lemma_grid_columns_nonoverlapping_any<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col1: nat, col2: nat,
)
    requires
        col1 < col2,
        col2 < col_widths.len(),
        T::zero().le(h_spacing),
        forall|j: int| 0 <= j < col_widths.len() ==> T::zero().le(col_widths[j].width),
    ensures
        grid_cell_x(padding_left, col_widths, h_spacing, col1)
            .add(col_widths[col1 as int].width)
            .le(grid_cell_x(padding_left, col_widths, h_spacing, col2)),
    decreases col2 - col1,
{
    if col1 + 1 == col2 {
        lemma_grid_columns_nonoverlapping(padding_left, col_widths, h_spacing, col1);
    } else {
        // IH: col1's right edge ≤ cell_x(col1+1)
        lemma_grid_columns_nonoverlapping(padding_left, col_widths, h_spacing, col1);
        // IH: cell_x(col1+1) + width[col1+1] ≤ cell_x(col2)
        lemma_grid_columns_nonoverlapping_any(
            padding_left, col_widths, h_spacing, col1 + 1, col2);
        // cell_x(col1+1) ≤ cell_x(col1+1) + width[col1+1] (nonneg width)
        let cx = grid_cell_x(padding_left, col_widths, h_spacing, (col1 + 1) as nat);
        crate::layout::proofs::lemma_le_add_nonneg::<T>(
            cx, col_widths[(col1 + 1) as int].width);
        // Chain: col1_right ≤ cell_x(col1+1) ≤ cell_x(col1+1)+w ≤ cell_x(col2)
        T::axiom_le_transitive(
            grid_cell_x(padding_left, col_widths, h_spacing, col1)
                .add(col_widths[col1 as int].width),
            cx,
            cx.add(col_widths[(col1 + 1) as int].width));
        T::axiom_le_transitive(
            grid_cell_x(padding_left, col_widths, h_spacing, col1)
                .add(col_widths[col1 as int].width),
            cx.add(col_widths[(col1 + 1) as int].width),
            grid_cell_x(padding_left, col_widths, h_spacing, col2));
    }
}

/// Rows non-overlapping for arbitrary row1 < row2.
pub proof fn lemma_grid_rows_nonoverlapping_any<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row1: nat, row2: nat,
)
    requires
        row1 < row2,
        row2 < row_heights.len(),
        T::zero().le(v_spacing),
        forall|j: int| 0 <= j < row_heights.len() ==> T::zero().le(row_heights[j].height),
    ensures
        grid_cell_y(padding_top, row_heights, v_spacing, row1)
            .add(row_heights[row1 as int].height)
            .le(grid_cell_y(padding_top, row_heights, v_spacing, row2)),
    decreases row2 - row1,
{
    if row1 + 1 == row2 {
        lemma_grid_rows_nonoverlapping(padding_top, row_heights, v_spacing, row1);
    } else {
        lemma_grid_rows_nonoverlapping(padding_top, row_heights, v_spacing, row1);
        lemma_grid_rows_nonoverlapping_any(
            padding_top, row_heights, v_spacing, row1 + 1, row2);
        let cy = grid_cell_y(padding_top, row_heights, v_spacing, (row1 + 1) as nat);
        crate::layout::proofs::lemma_le_add_nonneg::<T>(
            cy, row_heights[(row1 + 1) as int].height);
        T::axiom_le_transitive(
            grid_cell_y(padding_top, row_heights, v_spacing, row1)
                .add(row_heights[row1 as int].height),
            cy,
            cy.add(row_heights[(row1 + 1) as int].height));
        T::axiom_le_transitive(
            grid_cell_y(padding_top, row_heights, v_spacing, row1)
                .add(row_heights[row1 as int].height),
            cy.add(row_heights[(row1 + 1) as int].height),
            grid_cell_y(padding_top, row_heights, v_spacing, row2));
    }
}

/// Any two distinct grid cells don't overlap in 2D.
/// Either their column ranges or row ranges are disjoint.
pub proof fn lemma_grid_cells_nonoverlapping<T: OrderedRing>(
    padding_left: T, padding_top: T,
    col_widths: Seq<Size<T>>, row_heights: Seq<Size<T>>,
    h_spacing: T, v_spacing: T,
    r1: nat, c1: nat, r2: nat, c2: nat,
)
    requires
        r1 < row_heights.len(), c1 < col_widths.len(),
        r2 < row_heights.len(), c2 < col_widths.len(),
        (r1 != r2 || c1 != c2),
        T::zero().le(h_spacing), T::zero().le(v_spacing),
        forall|j: int| 0 <= j < col_widths.len() ==> T::zero().le(col_widths[j].width),
        forall|j: int| 0 <= j < row_heights.len() ==> T::zero().le(row_heights[j].height),
    ensures
        // Either x-ranges disjoint or y-ranges disjoint
        grid_cell_x(padding_left, col_widths, h_spacing, c1)
            .add(col_widths[c1 as int].width)
            .le(grid_cell_x(padding_left, col_widths, h_spacing, c2))
        || grid_cell_x(padding_left, col_widths, h_spacing, c2)
            .add(col_widths[c2 as int].width)
            .le(grid_cell_x(padding_left, col_widths, h_spacing, c1))
        || grid_cell_y(padding_top, row_heights, v_spacing, r1)
            .add(row_heights[r1 as int].height)
            .le(grid_cell_y(padding_top, row_heights, v_spacing, r2))
        || grid_cell_y(padding_top, row_heights, v_spacing, r2)
            .add(row_heights[r2 as int].height)
            .le(grid_cell_y(padding_top, row_heights, v_spacing, r1)),
{
    if c1 != c2 {
        if c1 < c2 {
            lemma_grid_columns_nonoverlapping_any(
                padding_left, col_widths, h_spacing, c1, c2);
        } else {
            lemma_grid_columns_nonoverlapping_any(
                padding_left, col_widths, h_spacing, c2, c1);
        }
    } else {
        // c1 == c2, so r1 != r2
        if r1 < r2 {
            lemma_grid_rows_nonoverlapping_any(
                padding_top, row_heights, v_spacing, r1, r2);
        } else {
            lemma_grid_rows_nonoverlapping_any(
                padding_top, row_heights, v_spacing, r2, r1);
        }
    }
}

} // verus!
