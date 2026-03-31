use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::RuntimeSize;
use crate::runtime::RuntimeLimits;
use crate::runtime::RuntimePadding;
use crate::runtime::RuntimeNode;
use crate::runtime::grid::*;
use crate::runtime::widget::{RuntimeWidget, layout_widget_exec, merge_layout_exec};
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::alignment::Alignment;
use crate::widget::*;
use crate::layout::*;
use crate::layout::grid::*;
use crate::layout::grid_proofs::*;

verus! {

///  Layout a grid widget: each child gets cell-sized limits.
pub fn layout_grid_widget_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_spacing: &RuntimeRational,
    v_spacing: &RuntimeRational,
    h_align: &Alignment,
    v_align: &Alignment,
    col_widths: &Vec<RuntimeSize>,
    row_heights: &Vec<RuntimeSize>,
    children: &Vec<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
        forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
        children@.len() == col_widths@.len() * row_heights@.len(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_cw = Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
            let spec_rh = Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
            let spec_wc = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::Container(ContainerWidget::Grid {
                padding: padding@, h_spacing: h_spacing@, v_spacing: v_spacing@,
                h_align: *h_align, v_align: *v_align,
                col_widths: spec_cw, row_heights: spec_rh, children: spec_wc,
            });
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_cw: Seq<Size<RationalModel>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let ghost spec_rh: Seq<Size<RationalModel>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let num_cols = col_widths.len();
    let num_rows = row_heights.len();
    let n = children.len();

    let ghost inner_spec = limits@.shrink(pad_h@, pad_v@);

    //  Recursively layout each child with cell-sized limits (flat iteration)
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes_2d: Vec<Vec<RuntimeSize>> = Vec::new();
    let mut flat_idx: usize = 0;
    let mut r: usize = 0;

    while r < num_rows
        invariant
            0 <= r <= num_rows,
            num_cols == col_widths@.len(),
            num_rows == row_heights@.len(),
            n == children@.len(),
            n == num_cols * num_rows,
            flat_idx == r * num_cols,
            inner.wf_spec(),
            inner@ == inner_spec,
            fuel > 0,
            forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
            forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
            forall|i: int| 0 <= i < children@.len() ==>
                (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
            child_nodes@.len() == flat_idx as int,
            child_sizes_2d@.len() == r as int,
            //  Each child node is wf
            forall|j: int| 0 <= j < flat_idx as int ==>
                (#[trigger] child_nodes@[j]).wf_spec(),
            //  Each child node was laid out with cell-sized limits (using row/col indices)
            forall|ri: int, ci: int| 0 <= ri < r as int && 0 <= ci < num_cols as int ==> {
                child_nodes@[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                    Limits { min: inner_spec.min, max: Size::new(
                        col_widths@[ci]@.width, row_heights@[ri]@.height) },
                    children@[ri * num_cols as int + ci].model(),
                    (fuel - 1) as nat)
            },
            //  child_sizes_2d rows have right length and wf, and match child node sizes
            forall|ri: int| 0 <= ri < r as int ==> {
                &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                &&& forall|ci: int| 0 <= ci < num_cols ==> {
                    &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                    &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                }
            },
        decreases num_rows - r,
    {
        let mut row_sizes: Vec<RuntimeSize> = Vec::new();
        let mut c: usize = 0;
        let ghost row_base: int = flat_idx as int;
        let ghost pre_inner_cn: Seq<RuntimeNode> = child_nodes@;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                num_cols == col_widths@.len(),
                num_rows == row_heights@.len(),
                n == children@.len(),
                n == num_cols * num_rows,
                r < num_rows,
                flat_idx == r * num_cols + c,
                row_base == (r * num_cols) as int,
                inner.wf_spec(),
                inner@ == inner_spec,
                fuel > 0,
                forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
                forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
                forall|i: int| 0 <= i < children@.len() ==>
                    (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
                child_nodes@.len() == flat_idx as int,
                child_sizes_2d@.len() == r as int,
                row_sizes@.len() == c as int,
                //  Ghost snapshot: old elements unchanged
                pre_inner_cn.len() == row_base,
                forall|j: int| 0 <= j < row_base ==>
                    child_nodes@[j] == (#[trigger] pre_inner_cn[j]),
                //  Preserve existing wf facts
                forall|j: int| 0 <= j < row_base ==>
                    (#[trigger] child_nodes@[j]).wf_spec(),
                //  Completed rows' layout facts (via snapshot, invariant through inner loop)
                forall|ri: int, ci: int| 0 <= ri < r as int && 0 <= ci < num_cols as int ==> {
                    pre_inner_cn[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                        Limits { min: inner_spec.min, max: Size::new(
                            col_widths@[ci]@.width, row_heights@[ri]@.height) },
                        children@[ri * num_cols as int + ci].model(),
                        (fuel - 1) as nat)
                },
                //  Completed rows' child_sizes_2d facts (via snapshot)
                forall|ri: int| 0 <= ri < r as int ==> {
                    &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                    &&& forall|ci: int| 0 <= ci < num_cols ==> {
                        &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                        &&& child_sizes_2d@[ri]@[ci]@ == pre_inner_cn[ri * num_cols as int + ci]@.size
                    }
                },
                //  New child nodes in this row
                forall|ci: int| 0 <= ci < c ==> {
                    &&& (#[trigger] child_nodes@[row_base + ci]).wf_spec()
                    &&& child_nodes@[row_base + ci]@ == layout_widget::<RationalModel>(
                        Limits { min: inner_spec.min, max: Size::new(
                            col_widths@[ci]@.width, row_heights@[r as int]@.height) },
                        children@[row_base + ci].model(),
                        (fuel - 1) as nat)
                },
                //  Row sizes match child node sizes
                forall|ci: int| 0 <= ci < c ==> {
                    &&& (#[trigger] row_sizes@[ci]).wf_spec()
                    &&& row_sizes@[ci]@ == child_nodes@[row_base + ci]@.size
                },
            decreases num_cols - c,
        {
            proof {
                assert(flat_idx < n) by(nonlinear_arith)
                    requires flat_idx == r * num_cols + c,
                        c < num_cols, r < num_rows,
                        n == num_cols * num_rows;
                //  Help Z3 instantiate quantifiers for preconditions
                assert(col_widths@[c as int].wf_spec());
                assert(row_heights@[r as int].wf_spec());
                assert(children@[flat_idx as int].wf_spec((fuel - 1) as nat));
            }
            let child_lim = RuntimeLimits::new(
                inner.min.copy_size(),
                RuntimeSize::new(
                    copy_rational(&col_widths[c].width),
                    copy_rational(&row_heights[r].height)),
            );
            let cn = layout_widget_exec(&child_lim, &children[flat_idx], fuel - 1);
            row_sizes.push(cn.size.copy_size());
            child_nodes.push(cn);
            c = c + 1;
            flat_idx = flat_idx + 1;
        }
        //  Capture row_sizes facts before push moves it
        let ghost row_sizes_len = row_sizes@.len();
        let ghost row_sizes_view: Seq<RuntimeSize> = row_sizes@;

        child_sizes_2d.push(row_sizes);

        proof {
            //  row_sizes had num_cols elements, all wf, matching child node sizes
            assert(row_sizes_len == num_cols as int);

            //  child_sizes_2d@[r] is the just-pushed row_sizes
            assert(child_sizes_2d@[r as int]@ =~= row_sizes_view);

            //  Combine child_nodes wf facts from both ranges
            assert forall|j: int| 0 <= j < flat_idx as int implies
                (#[trigger] child_nodes@[j]).wf_spec()
            by {
                if j < row_base {
                } else {
                    let ci = j - row_base;
                    assert(child_nodes@[row_base + ci].wf_spec());
                }
            }

            //  Establish snapshot preservation for old rows
            assert forall|ri: int, ci: int|
                0 <= ri < r as int && 0 <= ci < num_cols as int implies
                #[trigger] child_nodes@[ri * (num_cols as int) + ci]
                    == pre_inner_cn[ri * (num_cols as int) + ci]
            by {
                let idx = ri * (num_cols as int) + ci;
                assert((ri + 1) * (num_cols as int) <= row_base) by(nonlinear_arith)
                    requires ri + 1 <= (r as int), (num_cols as int) >= 0,
                        row_base == (r as int) * (num_cols as int);
                assert(idx < (ri + 1) * (num_cols as int)) by(nonlinear_arith)
                    requires idx == ri * (num_cols as int) + ci,
                        ci < (num_cols as int);
            }

            //  Reconstruct completed rows' layout_widget facts from snapshot
            assert forall|ri: int, ci: int|
                0 <= ri < (r + 1) as int && 0 <= ci < num_cols as int implies
                child_nodes@[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                    Limits { min: inner_spec.min, max: Size::new(
                        col_widths@[ci]@.width, row_heights@[ri]@.height) },
                    children@[ri * num_cols as int + ci].model(),
                    (fuel - 1) as nat)
            by {
                if ri < r as int {
                    assert(child_nodes@[ri * (num_cols as int) + ci]
                        == pre_inner_cn[ri * (num_cols as int) + ci]);
                } else {
                    assert(ri == r as int);
                    assert(ri * (num_cols as int) + ci == row_base + ci);
                }
            }

            //  child_sizes_2d invariant for all rows including the new one
            assert forall|ri: int| 0 <= ri < (r + 1) as int implies {
                &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                &&& forall|ci: int| 0 <= ci < num_cols ==> {
                    &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                    &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                }
            } by {
                if ri < r as int {
                    assert forall|ci: int| 0 <= ci < num_cols as int implies {
                        &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                        &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                    } by {
                        assert(child_nodes@[ri * (num_cols as int) + ci]
                            == pre_inner_cn[ri * (num_cols as int) + ci]);
                    }
                } else {
                    assert(ri == r as int);
                    assert(child_sizes_2d@[ri]@ =~= row_sizes_view);
                    assert(row_sizes_view.len() == num_cols as int);
                    assert(ri * (num_cols as int) == row_base);
                }
            }

            //  flat_idx arithmetic
            assert(flat_idx == r * num_cols + num_cols);
            assert((r + 1) * num_cols == r * num_cols + num_cols) by(nonlinear_arith)
                requires r >= 0nat, num_cols >= 0nat;
        }

        r = r + 1;
    }

    //  Call grid_layout_exec
    let layout_result = grid_layout_exec(
        limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, &child_sizes_2d);

    //  Merge
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);
    proof {
        //  After outer loop: r == num_rows, flat_idx == num_rows * num_cols
        //  n == num_cols * num_rows (commutativity: flat_idx == n)
        assert(flat_idx == n) by(nonlinear_arith)
            requires flat_idx == (num_rows as int) * (num_cols as int),
                n == (num_cols as int) * (num_rows as int);
        assert(child_nodes@.len() == n as int);
        assert(cn_models.len() == n as nat);

        //  Bridge child_sizes_2d to cn_models BEFORE child_nodes is consumed by merge
        assert forall|ri: int, ci: int|
            0 <= ri < num_rows as int && 0 <= ci < num_cols as int implies
            child_sizes_2d@[ri]@[ci]@ == cn_models[ri * (num_cols as int) + ci].size
        by {
            let nc = num_cols as int;
            let j = ri * nc + ci;
            //  j is in range [0, n)
            assert(j < (n as int)) by(nonlinear_arith)
                requires 0 <= ri, ri < (num_rows as int), 0 <= ci, ci < nc,
                    (n as int) == nc * (num_rows as int), j == ri * nc + ci;
            assert(child_sizes_2d@[ri]@[ci]@ == child_nodes@[j]@.size);
            //  Seq::new trigger: cn_models[j] == child_nodes@[j]@
        }
    }
    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    //  Connect to spec layout_widget
    proof {
        let spec_cn: Seq<Node<RationalModel>> = grid_widget_child_nodes(
            inner_spec, spec_cw, spec_rh, spec_wc,
            num_cols as nat, (fuel - 1) as nat);

        //  cn_models matches spec_cn: each element is the same layout_widget call
        assert(cn_models.len() == spec_cn.len());

        //  When n > 0, we have num_cols > 0 (needed for div/mod)
        if n > 0 {
            assert(num_cols > 0 && num_rows > 0) by(nonlinear_arith)
                requires n as int == (num_cols as int) * (num_rows as int),
                    n > 0;

            assert forall|j: int| 0 <= j < cn_models.len() as int implies
                cn_models[j] == spec_cn[j]
            by {
                let nc = num_cols as int;
                let nr = num_rows as int;
                let ri = j / nc;
                let ci = j % nc;
                //  vstd div/mod lemma: j == nc * (j / nc) + (j % nc)
                lemma_fundamental_div_mod(j, nc);
                assert(nc * ri + ci == j);
                assert(0 <= ci && ci < nc);
                assert(ri >= 0);
                //  Now use nonlinear_arith with these Z3-derived facts:
                assert(ri < nr) by(nonlinear_arith)
                    requires ri >= 0, nc * ri + ci == j, 0 <= ci, ci < nc,
                        j < nc * nr, nc > 0;
                //  Trigger Seq::new unfoldings for spec sequences
                let cw_ci = spec_cw[ci];
                assert(cw_ci == col_widths@[ci]@);
                let rh_ri = spec_rh[ri];
                assert(rh_ri == row_heights@[ri]@);
                let wc_j = spec_wc[j];
                assert(wc_j == children@[j].model());
            }
        }
        assert(cn_models =~= spec_cn);

        //  child_sizes_2d view matches layout_grid_body's computed child_sizes
        let spec_cs_view: Seq<Seq<Size<RationalModel>>> =
            Seq::new(child_sizes_2d@.len() as nat, |i: int|
                Seq::new(child_sizes_2d@[i]@.len() as nat, |j: int| child_sizes_2d@[i]@[j]@));
        let body_cs: Seq<Seq<Size<RationalModel>>> = Seq::new(num_rows as nat, |r: int|
            Seq::new(num_cols as nat, |c: int| spec_cn[(r * num_cols as int + c)].size));
        assert(spec_cs_view =~= body_cs) by {
            assert(spec_cs_view.len() == body_cs.len());
            assert forall|ri: int| 0 <= ri < spec_cs_view.len() as int implies
                spec_cs_view[ri] =~= body_cs[ri]
            by {
                assert(spec_cs_view[ri].len() == body_cs[ri].len());
                assert forall|ci: int| 0 <= ci < spec_cs_view[ri].len() as int implies
                    spec_cs_view[ri][ci] == body_cs[ri][ci]
                by {
                    let j = ri * (num_cols as int) + ci;
                    //  From pre-merge bridging proof:
                    //    child_sizes_2d@[ri]@[ci]@ == cn_models[j].size
                    //  From cn_models =~= spec_cn:
                    //    cn_models[j].size == spec_cn[j].size == body_cs[ri][ci]
                    assert(child_sizes_2d@[ri]@[ci]@ == cn_models[j].size);
                    assert(cn_models[j] == spec_cn[j]);
                }
            }
        }
    }

    merged
}

} //  verus!
