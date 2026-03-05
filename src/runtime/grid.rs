use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::column::align_offset_exec;
use crate::size::Size;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::alignment::align_offset;
use crate::layout::*;
use crate::layout::grid::*;
use crate::layout::grid_proofs::*;

verus! {

/// Compute grid content width at runtime: sum_widths + (ncols-1) * h_spacing.
fn grid_content_width_exec(
    col_widths: &Vec<RuntimeSize>,
    h_spacing: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        h_spacing.wf_spec(),
        forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == grid_content_width::<RationalModel>(
            Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@),
            h_spacing@,
        ),
{
    let ghost spec_cw: Seq<Size<RationalModel>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let n = col_widths.len();

    if n == 0 {
        RuntimeRational::from_int(0)
    } else {
        let mut sum_w = RuntimeRational::from_int(0);
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n, n == col_widths@.len(),
                sum_w.wf_spec(),
                sum_w@ == sum_widths::<RationalModel>(spec_cw, i as nat),
                forall|j: int| 0 <= j < col_widths@.len() ==> col_widths@[j].wf_spec(),
                forall|j: int| 0 <= j < col_widths@.len() ==> spec_cw[j] == col_widths@[j]@,
            decreases n - i,
        {
            sum_w = sum_w.add(&col_widths[i].width);
            i = i + 1;
        }

        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        let sp_count = n - 1;
        while j < sp_count
            invariant
                0 <= j <= sp_count, sp_count == n - 1, n > 0,
                sp.wf_spec(), h_spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(h_spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(h_spacing);
            j = j + 1;
        }

        sum_w.add(&sp)
    }
}

/// Compute grid content height at runtime: sum_heights + (nrows-1) * v_spacing.
fn grid_content_height_exec(
    row_heights: &Vec<RuntimeSize>,
    v_spacing: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        v_spacing.wf_spec(),
        forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == grid_content_height::<RationalModel>(
            Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@),
            v_spacing@,
        ),
{
    let ghost spec_rh: Seq<Size<RationalModel>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let n = row_heights.len();

    if n == 0 {
        RuntimeRational::from_int(0)
    } else {
        let mut sum_h = RuntimeRational::from_int(0);
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n, n == row_heights@.len(),
                sum_h.wf_spec(),
                sum_h@ == sum_heights::<RationalModel>(spec_rh, i as nat),
                forall|j: int| 0 <= j < row_heights@.len() ==> row_heights@[j].wf_spec(),
                forall|j: int| 0 <= j < row_heights@.len() ==> spec_rh[j] == row_heights@[j]@,
            decreases n - i,
        {
            sum_h = sum_h.add(&row_heights[i].height);
            i = i + 1;
        }

        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        let sp_count = n - 1;
        while j < sp_count
            invariant
                0 <= j <= sp_count, sp_count == n - 1, n > 0,
                sp.wf_spec(), v_spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(v_spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(v_spacing);
            j = j + 1;
        }

        sum_h.add(&sp)
    }
}

/// Execute grid layout: place children in a fixed-width/height grid.
pub fn grid_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_spacing: &RuntimeRational,
    v_spacing: &RuntimeRational,
    h_align: &Alignment,
    v_align: &Alignment,
    col_widths: &Vec<RuntimeSize>,
    row_heights: &Vec<RuntimeSize>,
    child_sizes: &Vec<Vec<RuntimeSize>>,
) -> (out: RuntimeNode)
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
        out@ == grid_layout::<RationalModel>(
            limits@, padding@, h_spacing@, v_spacing@, *h_align, *v_align,
            Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@),
            Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@),
            Seq::new(child_sizes@.len() as nat, |i: int|
                Seq::new(child_sizes@[i]@.len() as nat, |j: int| child_sizes@[i]@[j]@)
            ),
        ),
{
    let ghost spec_cw: Seq<Size<RationalModel>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let ghost spec_rh: Seq<Size<RationalModel>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let ghost spec_cs: Seq<Seq<Size<RationalModel>>> =
        Seq::new(child_sizes@.len() as nat, |i: int|
            Seq::new(child_sizes@[i]@.len() as nat, |j: int| child_sizes@[i]@[j]@)
        );

    let num_cols = col_widths.len();
    let num_rows = row_heights.len();

    // ── Content size + parent size ──
    let content_width = grid_content_width_exec(col_widths, h_spacing);
    let content_height = grid_content_height_exec(row_heights, v_spacing);

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&content_width);
    let total_height = pad_v.add(&content_height);
    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    // ── Establish children length ──
    let ghost spec_children = grid_all_children(
        padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
        *h_align, *v_align, spec_cs, 0,
    );
    proof {
        lemma_grid_all_children_len::<RationalModel>(
            padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
            *h_align, *v_align, spec_cs, 0, num_cols as nat,
        );
    }

    // ── Build children via nested loops ──
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut sh = RuntimeRational::from_int(0);
    let mut ra_v = RuntimeRational::from_int(0);
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
            sh@ == sum_heights::<RationalModel>(spec_rh, r as nat),
            ra_v@ == repeated_add::<RationalModel>(v_spacing@, r as nat),
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
        let mut sw = RuntimeRational::from_int(0);
        let mut ra_h = RuntimeRational::from_int(0);
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
                sw@ == sum_widths::<RationalModel>(spec_cw, c as nat),
                ra_h@ == repeated_add::<RationalModel>(h_spacing@, c as nat),
                sh@ == sum_heights::<RationalModel>(spec_rh, r as nat),
                ra_v@ == repeated_add::<RationalModel>(v_spacing@, r as nat),
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
            let cell_w = copy_rational(&col_widths[c].width);
            let cell_h = copy_rational(&row_heights[r].height);
            let cs_w = copy_rational(&child_sizes[r][c].width);
            let cs_h = copy_rational(&child_sizes[r][c].height);
            let x_off = align_offset_exec(h_align, &cell_w, &cs_w);
            let y_off = align_offset_exec(v_align, &cell_h, &cs_h);
            let child_x = cell_x.add(&x_off);
            let child_y = cell_y.add(&y_off);
            let cs = child_sizes[r][c].copy_size();
            let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);

            proof {
                // Call the element lemma
                lemma_grid_all_children_element::<RationalModel>(
                    padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                    *h_align, *v_align, spec_cs, r as nat, c as nat,
                );

                let flat_idx: nat = (r as nat) * spec_cw.len() + (c as nat);
                assert(children@.len() == flat_idx);
                let flat_idx_int: int = flat_idx as int;

                // Lemma postcondition → spec_children connection
                let expected = grid_child::<RationalModel>(
                    padding@, spec_cw, spec_rh, h_spacing@, v_spacing@,
                    *h_align, *v_align, r as nat, c as nat,
                    spec_cs[(r as nat) as int][(c as nat) as int],
                );
                // From =~= invariant, spec_children[i] == grid_all_children(...)[i]
                assert(spec_children[flat_idx_int] == expected);

                // Trigger the forall for this specific (r, c)
                let cs_rt = child_sizes@[r as int]@[c as int];
                assert(cs_rt.wf_spec());
                assert(cs@ == cs_rt@);
                assert(cs@ == spec_cs[r as int][c as int]);

                // wf_spec: field views match model fields
                assert(cs_w@ == cs_rt@.width);
                assert(cs_h@ == cs_rt@.height);

                // Cell dimensions and positions
                assert(cell_w@ == grid_col_width::<RationalModel>(spec_cw, c as nat));
                assert(cell_h@ == grid_row_height::<RationalModel>(spec_rh, r as nat));
                assert(cell_x@ == grid_cell_x::<RationalModel>(
                    padding@.left, spec_cw, h_spacing@, c as nat));
                assert(cell_y@ == grid_cell_y::<RationalModel>(
                    padding@.top, spec_rh, v_spacing@, r as nat));

                // Connect child_node to expected
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

    // ── Construct output ──
    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = grid_layout::<RationalModel>(
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

} // verus!
