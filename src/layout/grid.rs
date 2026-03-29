use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};
use crate::layout::{sum_widths, sum_heights, repeated_add};

verus! {

//  ── Grid cell position helpers ──────────────────────────────────────

///  X-position of a grid cell at column `col`:
///  padding_left + sum_widths(col_widths, col) + col * h_spacing.
pub open spec fn grid_cell_x<T: OrderedRing>(
    padding_left: T,
    col_widths: Seq<Size<T>>,
    h_spacing: T,
    col: nat,
) -> T {
    padding_left
        .add(sum_widths(col_widths, col))
        .add(repeated_add(h_spacing, col))
}

///  Y-position of a grid cell at row `row`:
///  padding_top + sum_heights(row_heights, row) + row * v_spacing.
pub open spec fn grid_cell_y<T: OrderedRing>(
    padding_top: T,
    row_heights: Seq<Size<T>>,
    v_spacing: T,
    row: nat,
) -> T {
    padding_top
        .add(sum_heights(row_heights, row))
        .add(repeated_add(v_spacing, row))
}

///  Width of column `col`: col_widths[col].width.
pub open spec fn grid_col_width<T: OrderedRing>(
    col_widths: Seq<Size<T>>,
    col: nat,
) -> T {
    col_widths[col as int].width
}

///  Height of row `row`: row_heights[row].height.
pub open spec fn grid_row_height<T: OrderedRing>(
    row_heights: Seq<Size<T>>,
    row: nat,
) -> T {
    row_heights[row as int].height
}

//  ── Grid child placement ────────────────────────────────────────────

///  Place a single child in a grid cell, applying alignment within the cell.
pub open spec fn grid_child<T: OrderedField>(
    padding: Padding<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    row: nat,
    col: nat,
    child_size: Size<T>,
) -> Node<T> {
    let cell_x = grid_cell_x(padding.left, col_widths, h_spacing, col);
    let cell_y = grid_cell_y(padding.top, row_heights, v_spacing, row);
    let cell_w = grid_col_width(col_widths, col);
    let cell_h = grid_row_height(row_heights, row);
    let child_x = cell_x.add(align_offset(h_align, cell_w, child_size.width));
    let child_y = cell_y.add(align_offset(v_align, cell_h, child_size.height));
    Node::leaf(child_x, child_y, child_size)
}

///  Build children for a single row of the grid (columns col..num_cols).
pub open spec fn grid_row_children<T: OrderedField>(
    padding: Padding<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    row: nat,
    child_sizes: Seq<Seq<Size<T>>>,
    col: nat,
) -> Seq<Node<T>>
    decreases col_widths.len() - col,
{
    if col >= col_widths.len() || col >= child_sizes[row as int].len() {
        Seq::empty()
    } else {
        let child = grid_child(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, col, child_sizes[row as int][col as int],
        );
        Seq::empty().push(child).add(
            grid_row_children(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, row, child_sizes, col + 1,
            )
        )
    }
}

///  Build all children for the grid (rows row..num_rows, each containing all columns).
pub open spec fn grid_all_children<T: OrderedField>(
    padding: Padding<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    child_sizes: Seq<Seq<Size<T>>>,
    row: nat,
) -> Seq<Node<T>>
    decreases row_heights.len() - row,
{
    if row >= row_heights.len() || row >= child_sizes.len() {
        Seq::empty()
    } else {
        grid_row_children(
            padding, col_widths, row_heights, h_spacing, v_spacing,
            h_align, v_align, row, child_sizes, 0,
        ).add(
            grid_all_children(
                padding, col_widths, row_heights, h_spacing, v_spacing,
                h_align, v_align, child_sizes, row + 1,
            )
        )
    }
}

///  Total grid content width: sum of column widths + (num_cols - 1) * h_spacing.
pub open spec fn grid_content_width<T: OrderedRing>(
    col_widths: Seq<Size<T>>,
    h_spacing: T,
) -> T {
    if col_widths.len() == 0 {
        T::zero()
    } else {
        sum_widths(col_widths, col_widths.len() as nat)
            .add(repeated_add(h_spacing, (col_widths.len() - 1) as nat))
    }
}

///  Total grid content height: sum of row heights + (num_rows - 1) * v_spacing.
pub open spec fn grid_content_height<T: OrderedRing>(
    row_heights: Seq<Size<T>>,
    v_spacing: T,
) -> T {
    if row_heights.len() == 0 {
        T::zero()
    } else {
        sum_heights(row_heights, row_heights.len() as nat)
            .add(repeated_add(v_spacing, (row_heights.len() - 1) as nat))
    }
}

///  Lay out children in a grid with fixed column widths and row heights.
#[verifier::opaque]
pub open spec fn grid_layout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    child_sizes: Seq<Seq<Size<T>>>,
) -> Node<T> {
    let content_w = grid_content_width(col_widths, h_spacing);
    let content_h = grid_content_height(row_heights, v_spacing);
    let total_w = padding.horizontal().add(content_w);
    let total_h = padding.vertical().add(content_h);
    let parent_size = limits.resolve(Size::new(total_w, total_h));
    let children = grid_all_children(
        padding, col_widths, row_heights, h_spacing, v_spacing,
        h_align, v_align, child_sizes, 0,
    );
    Node { x: T::zero(), y: T::zero(), size: parent_size, children }
}

} //  verus!
