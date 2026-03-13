use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::ring::Ring;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::flex::*;
use crate::runtime::widget::RuntimeFlexItem;
use crate::runtime::widget::layout_widget_exec;
use crate::runtime::widget::merge_layout_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::alignment::Alignment;
use crate::widget::FlexDirection;
use crate::widget::FlexItem;
use crate::widget::Widget;
use crate::widget::layout_widget;
use crate::widget::layout_flex_column_body;
use crate::widget::layout_flex_row_body;
use crate::widget::flex_column_widget_child_nodes;
use crate::widget::flex_row_widget_child_nodes;
use crate::layout::repeated_add;
use crate::layout::flex::*;

verus! {

/// Layout a flex widget: each child gets per-weight limits.
pub fn layout_flex_widget_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    alignment: &Alignment,
    direction: &FlexDirection,
    children: &Vec<RuntimeFlexItem>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==>
            children@[i].weight.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat),
        children@.len() > 0 ==> !sum_weights::<RationalModel>(
            Seq::new(children@.len() as nat, |i: int| children@[i].weight@),
            children@.len() as nat,
        ).eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_fi = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::Flex {
                padding: padding@, spacing: spacing@, alignment: *alignment,
                direction: *direction, children: spec_fi,
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_fi: Seq<FlexItem<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());
    let ghost spec_weights: Seq<RationalModel> =
        Seq::new(children@.len() as nat, |i: int| children@[i].weight@);

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    // Compute weights and total_weight
    let mut weights: Vec<RuntimeRational> = Vec::new();
    let mut total_weight = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, n == children@.len(),
            weights@.len() == i as int,
            total_weight.wf_spec(),
            total_weight@ == sum_weights::<RationalModel>(spec_weights, i as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] weights@[j]).wf_spec()
                &&& weights@[j]@ == children@[j].weight@
            },
            forall|j: int| 0 <= j < children@.len() ==> children@[j].weight.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==> spec_weights[j] == children@[j].weight@,
        decreases n - i,
    {
        let w = copy_rational(&children[i].weight);
        total_weight = total_weight.add(&children[i].weight);
        weights.push(w);
        i = i + 1;
    }

    // Compute total_spacing
    let total_spacing = if n > 0 {
        let sp_count = n - 1;
        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        while j < sp_count
            invariant
                0 <= j <= sp_count,
                sp.wf_spec(), spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }
        sp
    } else {
        RuntimeRational::from_int(0)
    };

    // Recursively layout each child with per-weight limits, collecting child nodes + cross sizes
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut cross_sizes: Vec<RuntimeRational> = Vec::new();
    let mut k: usize = 0;

    let ghost avail_spec: RationalModel;
    match direction {
        FlexDirection::Column => {
            let available = inner.max.height.sub(&total_spacing);
            proof { avail_spec = available@; }
            while k < n
                invariant
                    0 <= k <= n, n == children@.len(),
                    inner.wf_spec(),
                    inner@ == limits@.shrink(pad_h@, pad_v@),
                    total_weight.wf_spec(),
                    total_weight@ == sum_weights::<RationalModel>(spec_weights, n as nat),
                    n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
                    available.wf_spec(),
                    available@ == avail_spec,
                    child_nodes@.len() == k as int,
                    cross_sizes@.len() == k as int,
                    weights@.len() == n as int,
                    forall|j: int| 0 <= j < n ==> weights@[j].wf_spec(),
                    forall|j: int| 0 <= j < n ==> weights@[j]@ == spec_weights[j],
                    fuel > 0,
                    forall|j: int| 0 <= j < children@.len() ==>
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] child_nodes@[j]).wf_spec()
                        &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                            Limits { min: inner@.min, max: Size::new(inner@.max.width,
                                flex_child_main_size::<RationalModel>(spec_weights[j], total_weight@, avail_spec)) },
                            children@[j].child.model(), (fuel - 1) as nat)
                    },
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] cross_sizes@[j]).wf_spec()
                        &&& cross_sizes@[j]@ == child_nodes@[j]@.size.width
                    },
                decreases n - k,
            {
                let wd = weights[k].div(&total_weight);
                let main_alloc = wd.mul(&available);
                let child_lim = RuntimeLimits::new(
                    inner.min.copy_size(),
                    RuntimeSize::new(copy_rational(&inner.max.width), main_alloc),
                );
                let cn = layout_widget_exec(&child_lim, &children[k].child, fuel - 1);
                let cw = copy_rational(&cn.size.width);
                cross_sizes.push(cw);
                child_nodes.push(cn);
                k = k + 1;
            }

            // Prove flex_column_layout_exec preconditions
            proof {
                assert(Seq::new(weights@.len() as nat, |i: int| weights@[i]@)
                    =~= spec_weights);
                assert forall|j: int| 0 <= j < cross_sizes@.len() implies
                    (#[trigger] cross_sizes@[j]).wf_spec()
                by {}
            }
            let layout_result = flex_column_layout_exec(
                limits, padding, spacing, alignment, &weights, &cross_sizes);

            // Merge — layout_result.children@.len() == n from flex_column_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            // Connect merged result to spec layout_widget
            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_column_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                // 1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                // 2. Cross sizes view matches what layout_flex_column_body computes
                let cross_view: Seq<RationalModel> =
                    Seq::new(cross_sizes@.len() as nat, |i: int| cross_sizes@[i]@);
                let spec_cross: Seq<RationalModel> =
                    Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.width);
                assert(cross_view =~= spec_cross) by {
                    assert(cross_view.len() == spec_cross.len());
                    assert forall|j: int| 0 <= j < cross_view.len() as int implies
                        cross_view[j] == spec_cross[j]
                    by {
                        // cross_sizes@[j]@ == child_nodes@[j]@.size.width == cn_models[j].size.width == spec_cn[j].size.width
                    }
                }

                // 3. Weights from spec_fi match spec_weights
                let spec_weights_fi: Seq<RationalModel> =
                    Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
                assert(spec_weights_fi =~= spec_weights) by {
                    assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
                        spec_weights_fi[i] == spec_weights[i]
                    by {
                        let fi_i = spec_fi[i];
                        assert(fi_i == children@[i].model());
                    }
                }

                // 4. merged@ == layout_flex_column_body(...)
                assert(merged@ == layout_flex_column_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
        FlexDirection::Row => {
            let available = inner.max.width.sub(&total_spacing);
            proof { avail_spec = available@; }
            while k < n
                invariant
                    0 <= k <= n, n == children@.len(),
                    inner.wf_spec(),
                    inner@ == limits@.shrink(pad_h@, pad_v@),
                    total_weight.wf_spec(),
                    total_weight@ == sum_weights::<RationalModel>(spec_weights, n as nat),
                    n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
                    available.wf_spec(),
                    available@ == avail_spec,
                    child_nodes@.len() == k as int,
                    cross_sizes@.len() == k as int,
                    weights@.len() == n as int,
                    forall|j: int| 0 <= j < n ==> weights@[j].wf_spec(),
                    forall|j: int| 0 <= j < n ==> weights@[j]@ == spec_weights[j],
                    fuel > 0,
                    forall|j: int| 0 <= j < children@.len() ==>
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] child_nodes@[j]).wf_spec()
                        &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                            Limits { min: inner@.min, max: Size::new(
                                flex_child_main_size::<RationalModel>(spec_weights[j], total_weight@, avail_spec),
                                inner@.max.height) },
                            children@[j].child.model(), (fuel - 1) as nat)
                    },
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] cross_sizes@[j]).wf_spec()
                        &&& cross_sizes@[j]@ == child_nodes@[j]@.size.height
                    },
                decreases n - k,
            {
                let wd = weights[k].div(&total_weight);
                let main_alloc = wd.mul(&available);
                let child_lim = RuntimeLimits::new(
                    inner.min.copy_size(),
                    RuntimeSize::new(main_alloc, copy_rational(&inner.max.height)),
                );
                let cn = layout_widget_exec(&child_lim, &children[k].child, fuel - 1);
                let ch = copy_rational(&cn.size.height);
                cross_sizes.push(ch);
                child_nodes.push(cn);
                k = k + 1;
            }

            proof {
                assert(Seq::new(weights@.len() as nat, |i: int| weights@[i]@)
                    =~= spec_weights);
                assert forall|j: int| 0 <= j < cross_sizes@.len() implies
                    (#[trigger] cross_sizes@[j]).wf_spec()
                by {}
            }
            let layout_result = flex_row_layout_exec(
                limits, padding, spacing, alignment, &weights, &cross_sizes);

            // Merge — layout_result.children@.len() == n from flex_row_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_row_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                // 1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                // 2. Cross sizes view matches
                let cross_view: Seq<RationalModel> =
                    Seq::new(cross_sizes@.len() as nat, |i: int| cross_sizes@[i]@);
                let spec_cross: Seq<RationalModel> =
                    Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.height);
                assert(cross_view =~= spec_cross) by {
                    assert(cross_view.len() == spec_cross.len());
                    assert forall|j: int| 0 <= j < cross_view.len() as int implies
                        cross_view[j] == spec_cross[j]
                    by {}
                }

                // 3. Weights from spec_fi match
                let spec_weights_fi: Seq<RationalModel> =
                    Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
                assert(spec_weights_fi =~= spec_weights) by {
                    assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
                        spec_weights_fi[i] == spec_weights[i]
                    by {
                        let fi_i = spec_fi[i];
                        assert(fi_i == children@[i].model());
                    }
                }

                // 4. merged@ == layout_flex_row_body(...)
                assert(merged@ == layout_flex_row_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
    }
}

} // verus!
