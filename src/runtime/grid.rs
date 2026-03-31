use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::linear::align_offset_exec;
use crate::size::Size;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::alignment::align_offset;
use crate::layout::*;
use crate::layout::grid::*;
use crate::layout::grid_proofs::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Compute grid content width at runtime: sum_widths + (ncols-1) * h_spacing.
pub fn grid_content_width_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    col_widths: &Vec<RuntimeSize<R, V>>,
    h_spacing: &R,
) -> (out: R)
    requires
        h_spacing.wf_spec(),
        forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == grid_content_width::<V>(
            Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@),
            h_spacing@,
        ),
{
    let ghost spec_cw: Seq<Size<V>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let n = col_widths.len();

    if n == 0 {
        h_spacing.zero_like()
    } else {
        let mut sum_w = h_spacing.zero_like();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n, n == col_widths@.len(),
                sum_w.wf_spec(),
                sum_w@ == sum_widths::<V>(spec_cw, i as nat),
                forall|j: int| 0 <= j < col_widths@.len() ==> col_widths@[j].wf_spec(),
                forall|j: int| 0 <= j < col_widths@.len() ==> spec_cw[j] == col_widths@[j]@,
            decreases n - i,
        {
            sum_w = sum_w.add(&col_widths[i].width);
            i = i + 1;
        }

        let mut sp = h_spacing.zero_like();
        let mut j: usize = 0;
        let sp_count = n - 1;
        while j < sp_count
            invariant
                0 <= j <= sp_count, sp_count == n - 1, n > 0,
                sp.wf_spec(), h_spacing.wf_spec(),
                sp@ == repeated_add::<V>(h_spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(h_spacing);
            j = j + 1;
        }

        sum_w.add(&sp)
    }
}

///  Compute grid content height at runtime: sum_heights + (nrows-1) * v_spacing.
pub fn grid_content_height_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    row_heights: &Vec<RuntimeSize<R, V>>,
    v_spacing: &R,
) -> (out: R)
    requires
        v_spacing.wf_spec(),
        forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == grid_content_height::<V>(
            Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@),
            v_spacing@,
        ),
{
    let ghost spec_rh: Seq<Size<V>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let n = row_heights.len();

    if n == 0 {
        v_spacing.zero_like()
    } else {
        let mut sum_h = v_spacing.zero_like();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n, n == row_heights@.len(),
                sum_h.wf_spec(),
                sum_h@ == sum_heights::<V>(spec_rh, i as nat),
                forall|j: int| 0 <= j < row_heights@.len() ==> row_heights@[j].wf_spec(),
                forall|j: int| 0 <= j < row_heights@.len() ==> spec_rh[j] == row_heights@[j]@,
            decreases n - i,
        {
            sum_h = sum_h.add(&row_heights[i].height);
            i = i + 1;
        }

        let mut sp = v_spacing.zero_like();
        let mut j: usize = 0;
        let sp_count = n - 1;
        while j < sp_count
            invariant
                0 <= j <= sp_count, sp_count == n - 1, n > 0,
                sp.wf_spec(), v_spacing.wf_spec(),
                sp@ == repeated_add::<V>(v_spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(v_spacing);
            j = j + 1;
        }

        sum_h.add(&sp)
    }
}

///  Execute grid layout: place children in a fixed-width/height grid.
pub fn grid_layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    h_spacing: &R,
    v_spacing: &R,
    h_align: &Alignment,
    v_align: &Alignment,
    col_widths: &Vec<RuntimeSize<R, V>>,
    row_heights: &Vec<RuntimeSize<R, V>>,
    child_sizes: &Vec<Vec<RuntimeSize<R, V>>>,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
        forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
        child_sizes@.len() >= row_heights@.len(),
        forall|r: int| 0 <= r < child_sizes@.len() ==> {
            &&& child_sizes@[r]@.len() >= col_widths@.len()
            &&& forall|c: int| 0 <= c < child_sizes@[r]@.len()
                ==> (#[trigger] child_sizes@[r]@[c]).wf_spec()
        },
    ensures
        out.wf_spec(),
        out@ == grid_layout::<V>(
            limits@, padding@, h_spacing@, v_spacing@, *h_align, *v_align,
            Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@),
            Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@),
            Seq::new(child_sizes@.len() as nat, |i: int|
                Seq::new(child_sizes@[i]@.len() as nat, |j: int| child_sizes@[i]@[j]@)
            ),
        ),
        out.children@.len() == row_heights@.len() * col_widths@.len(),
{
    proof { reveal(grid_layout); }
    let ghost spec_cw: Seq<Size<V>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let ghost spec_rh: Seq<Size<V>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let ghost spec_cs: Seq<Seq<Size<V>>> =
        Seq::new(child_sizes@.len() as nat, |i: int|
            Seq::new(child_sizes@[i]@.len() as nat, |j: int| child_sizes@[i]@[j]@)
        );

    let num_cols = col_widths.len();
    let num_rows = row_heights.len();

    //  ── Content size + parent size ──
    let content_width = grid_content_width_exec(col_widths, h_spacing);
    let content_height = grid_content_height_exec(row_heights, v_spacing);

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&content_width);
    let total_height = pad_v.add(&content_height);
    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    //  ── Establish children length ──
    let ghost spec_children = grid_all_children(
        padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
        *h_align, *v_align, spec_cs, 0,
    );
    proof {
        lemma_grid_all_children_len::<V>(
            padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
            *h_align, *v_align, spec_cs, 0, num_cols as nat,
        );
    }

    //  ── Build children via nested loops ──
    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut sh = h_spacing.zero_like();
    let mut ra_v = h_spacing.zero_like();
    let mut r: usize = 0;

    while r < num_rows
        invariant
            0 <= r <= num_rows,
            num_rows == row_heights@.len(),
            num_cols == col_widths@.len(),
            spec_cw.len() == num_cols as nat,
            spec_rh.len() == num_rows as nat,
            spec_cs.len() == child_sizes@.len() as nat,
            spec_cs.len() >= spec_rh.len(),
            sh.wf_spec(), ra_v.wf_spec(),
            h_spacing.wf_spec(), v_spacing.wf_spec(), padding.wf_spec(),
            sh@ == sum_heights::<V>(spec_rh, r as nat),
            ra_v@ == repeated_add::<V>(v_spacing@, r as nat),
            children@.len() == (r as nat) * spec_cw.len(),
            spec_children.len() == spec_rh.len() * spec_cw.len(),
            spec_children =~= grid_all_children(
                padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                *h_align, *v_align, spec_cs, 0nat,
            ),
            forall|j: int| 0 <= j < col_widths@.len() ==> col_widths@[j].wf_spec(),
            forall|j: int| 0 <= j < row_heights@.len() ==> row_heights@[j].wf_spec(),
            forall|j: int| 0 <= j < col_widths@.len() ==> spec_cw[j] == col_widths@[j]@,
            forall|j: int| 0 <= j < row_heights@.len() ==> spec_rh[j] == row_heights@[j]@,
            child_sizes@.len() >= row_heights@.len(),
            forall|ri: int| 0 <= ri < child_sizes@.len() ==> {
                &&& child_sizes@[ri]@.len() >= col_widths@.len()
                &&& forall|ci: int| 0 <= ci < child_sizes@[ri]@.len()
                    ==> (#[trigger] child_sizes@[ri]@[ci]).wf_spec()
            },
            forall|ri: int| 0 <= ri < spec_cs.len() ==>
                (#[trigger] spec_cs[ri]).len() >= spec_cw.len(),
            forall|ri: int, ci: int|
                0 <= ri < spec_cs.len() && 0 <= ci < spec_cs[ri].len()
                ==> spec_cs[ri][ci] == (#[trigger] child_sizes@[ri]@[ci])@,
            forall|j: int| 0 <= j < children@.len() ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == spec_children[j]
            },
        decreases num_rows - r,
    {
        let mut sw = h_spacing.zero_like();
        let mut ra_h = h_spacing.zero_like();
        let mut c: usize = 0;

        while c < num_cols
            invariant
                0 <= c <= num_cols,
                num_cols == col_widths@.len(),
                num_rows == row_heights@.len(),
                r < num_rows,
                spec_cw.len() == num_cols as nat,
                spec_rh.len() == num_rows as nat,
                spec_cs.len() == child_sizes@.len() as nat,
                spec_cs.len() >= spec_rh.len(),
                sw.wf_spec(), ra_h.wf_spec(), sh.wf_spec(), ra_v.wf_spec(),
                h_spacing.wf_spec(), v_spacing.wf_spec(), padding.wf_spec(),
                sw@ == sum_widths::<V>(spec_cw, c as nat),
                ra_h@ == repeated_add::<V>(h_spacing@, c as nat),
                sh@ == sum_heights::<V>(spec_rh, r as nat),
                ra_v@ == repeated_add::<V>(v_spacing@, r as nat),
                children@.len() == (r as nat) * spec_cw.len() + (c as nat),
                spec_children.len() == spec_rh.len() * spec_cw.len(),
                spec_children =~= grid_all_children(
                    padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                    *h_align, *v_align, spec_cs, 0nat,
                ),
                forall|j: int| 0 <= j < col_widths@.len() ==> col_widths@[j].wf_spec(),
                forall|j: int| 0 <= j < row_heights@.len() ==> row_heights@[j].wf_spec(),
                forall|j: int| 0 <= j < col_widths@.len() ==> spec_cw[j] == col_widths@[j]@,
                forall|j: int| 0 <= j < row_heights@.len() ==> spec_rh[j] == row_heights@[j]@,
                child_sizes@.len() >= row_heights@.len(),
                forall|ri: int| 0 <= ri < child_sizes@.len() ==> {
                    &&& child_sizes@[ri]@.len() >= col_widths@.len()
                    &&& forall|ci: int| 0 <= ci < child_sizes@[ri]@.len()
                        ==> (#[trigger] child_sizes@[ri]@[ci]).wf_spec()
                },
                forall|ri: int| 0 <= ri < spec_cs.len() ==>
                    (#[trigger] spec_cs[ri]).len() >= spec_cw.len(),
                forall|ri: int, ci: int|
                    0 <= ri < spec_cs.len() && 0 <= ci < spec_cs[ri].len()
                    ==> spec_cs[ri][ci] == (#[trigger] child_sizes@[ri]@[ci])@,
                forall|j: int| 0 <= j < children@.len() ==> {
                    &&& (#[trigger] children@[j]).wf_spec()
                    &&& children@[j]@ == spec_children[j]
                },
            decreases num_cols - c,
        {
            let cell_x = padding.left.add(&sw).add(&ra_h);
            let cell_y = padding.top.add(&sh).add(&ra_v);
            let cell_w = col_widths[c].width.copy();
            let cell_h = row_heights[r].height.copy();
            let cs_w = child_sizes[r][c].width.copy();
            let cs_h = child_sizes[r][c].height.copy();
            let x_off = align_offset_exec(h_align, &cell_w, &cs_w);
            let y_off = align_offset_exec(v_align, &cell_h, &cs_h);
            let child_x = cell_x.add(&x_off);
            let child_y = cell_y.add(&y_off);
            let cs = child_sizes[r][c].copy_size();
            let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);

            proof {
                //  Call the element lemma
                lemma_grid_all_children_element::<V>(
                    padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                    *h_align, *v_align, spec_cs, r as nat, c as nat,
                );

                let flat_idx: nat = (r as nat) * spec_cw.len() + (c as nat);
                assert(children@.len() == flat_idx);
                let flat_idx_int: int = flat_idx as int;

                //  Lemma postcondition → spec_children connection
                let expected = grid_child::<V>(
                    padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                    *h_align, *v_align, r as nat, c as nat,
                    spec_cs[(r as nat) as int][(c as nat) as int],
                );
                //  From =~= invariant, spec_children[i] == grid_all_children(...)[i]
                assert(spec_children[flat_idx_int] == expected);

                //  Trigger the forall for this specific (r, c)
                let cs_rt = child_sizes@[r as int]@[c as int];
                assert(cs_rt.wf_spec());
                assert(cs@ == cs_rt@);
                assert(cs@ == spec_cs[r as int][c as int]);

                //  wf_spec: field views match model fields
                assert(cs_w@ == cs_rt@.width);
                assert(cs_h@ == cs_rt@.height);

                //  Cell dimensions and positions
                assert(cell_w@ == grid_col_width::<V>(spec_cw, c as nat));
                assert(cell_h@ == grid_row_height::<V>(spec_rh, r as nat));
                assert(cell_x@ == grid_cell_x::<V>(
                    padding@.left, spec_cw, h_spacing@, c as nat));
                assert(cell_y@ == grid_cell_y::<V>(
                    padding@.top, spec_rh, v_spacing@, r as nat));

                //  Connect child_node to expected
                assert(child_node@ == expected);
            }

            children.push(child_node);

            sw = sw.add(&col_widths[c].width);
            ra_h = ra_h.add(h_spacing);
            c = c + 1;
        }

        proof {
            let r_n: nat = r as nat;
            let nc: nat = spec_cw.len();
            assert((r_n + 1) * nc == r_n * nc + nc) by (nonlinear_arith)
                requires r_n >= 0, nc >= 0;
        }

        sh = sh.add(&row_heights[r].height);
        ra_v = ra_v.add(v_spacing);
        r = r + 1;
    }

    //  ── Construct output ──
    let x = h_spacing.zero_like();
    let y = h_spacing.zero_like();

    let ghost parent_model = grid_layout::<V>(
        limits@, padding@, h_spacing@, v_spacing@, *h_align, *v_align,
        spec_cw, spec_rh, spec_cs,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        assert(out@.children == spec_children);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} //  verus!
