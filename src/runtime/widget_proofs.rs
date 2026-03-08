use vstd::prelude::*;
use crate::runtime::RationalModel;
use crate::runtime::widget::{RuntimeWidget, RuntimeFlexItem, RuntimeAbsoluteChild};
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::padding::Padding;
use crate::alignment::Alignment;
use crate::widget::*;
use crate::layout::flex::*;
use crate::layout::absolute::*;

verus! {

// ── Fuel bridge helpers ──────────────────────────────────────────

/// Bridge fuel arithmetic: (fuel as nat - 1) as nat == (fuel - 1) as nat.
pub proof fn lemma_fuel_nat_eq(fuel: usize)
    requires fuel > 0,
    ensures (fuel as nat - 1) as nat == (fuel - 1) as nat,
{}

/// Bridge fuel arithmetic for Vec<RuntimeWidget> children.
pub proof fn lemma_fuel_bridge_children(children: Seq<RuntimeWidget>, fuel: usize)
    requires
        fuel > 0,
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).wf_spec((fuel as nat - 1) as nat),
    ensures
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).wf_spec((fuel - 1) as nat),
{
    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
}

/// Bridge fuel arithmetic for Vec<RuntimeFlexItem> children.
pub proof fn lemma_fuel_bridge_flex_children(children: Seq<RuntimeFlexItem>, fuel: usize)
    requires
        fuel > 0,
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).child.wf_spec((fuel as nat - 1) as nat),
    ensures
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).child.wf_spec((fuel - 1) as nat),
{
    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
}

/// Bridge fuel arithmetic for Vec<RuntimeAbsoluteChild> children.
pub proof fn lemma_fuel_bridge_absolute_children(children: Seq<RuntimeAbsoluteChild>, fuel: usize)
    requires
        fuel > 0,
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).child.wf_spec((fuel as nat - 1) as nat),
    ensures
        forall|j: int| 0 <= j < children.len() ==>
            (#[trigger] children[j]).child.wf_spec((fuel - 1) as nat),
{
    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
}

// ── Flex spec connection proofs ──────────────────────────────────

/// Connect flex column exec result to spec layout_flex_column_body.
///
/// Proves: merged == layout_flex_column_body(limits, padding, spacing, alignment, weights_fi, spec_cn)
/// by establishing cn_models =~= spec_cn, cross_view =~= spec_cross, weight_view =~= weights_fi.
pub proof fn lemma_flex_column_spec_connection(
    limits: Limits<RationalModel>,
    padding: Padding<RationalModel>,
    spacing: RationalModel,
    alignment: Alignment,
    spec_fi: Seq<FlexItem<RationalModel>>,
    spec_weights: Seq<RationalModel>,
    total_weight: RationalModel,
    avail: RationalModel,
    cn_models: Seq<Node<RationalModel>>,
    cross_view: Seq<RationalModel>,
    weight_view: Seq<RationalModel>,
    merged: Node<RationalModel>,
    fuel_nat: nat,
)
    requires
        spec_fi.len() == cn_models.len(),
        spec_fi.len() == cross_view.len(),
        spec_fi.len() == spec_weights.len(),
        spec_fi.len() == weight_view.len(),
        // cn_models match spec: each element from same layout_widget call
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            forall|j: int| 0 <= j < cn_models.len() ==>
                cn_models[j] == layout_widget::<RationalModel>(
                    Limits { min: inner.min, max: Size::new(inner.max.width,
                        flex_child_main_size(spec_weights[j], total_weight, avail)) },
                    spec_fi[j].child, fuel_nat)
        }),
        // cross sizes = widths of cn_models
        forall|j: int| 0 <= j < cross_view.len() ==>
            cross_view[j] == cn_models[j].size.width,
        // weight_view == spec_weights
        forall|j: int| 0 <= j < weight_view.len() ==>
            weight_view[j] == spec_weights[j],
        // spec_weights derived from spec_fi
        forall|j: int| 0 <= j < spec_weights.len() ==>
            spec_weights[j] == spec_fi[j].weight,
        // merged from merge_layout(flex_column_layout(..., weight_view, cross_view), cn_models)
        merged == merge_layout::<RationalModel>(
            flex_column_layout(limits, padding, spacing, alignment, weight_view, cross_view),
            cn_models),
    ensures
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let spec_weights_fi = Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
            let spec_cn = flex_column_widget_child_nodes(
                inner, spec_fi, spec_weights, total_weight, avail, fuel_nat);
            merged == layout_flex_column_body::<RationalModel>(
                limits, padding, spacing, alignment, spec_weights_fi, spec_cn)
        }),
{
    let inner = limits.shrink(padding.horizontal(), padding.vertical());
    let spec_cn = flex_column_widget_child_nodes(
        inner, spec_fi, spec_weights, total_weight, avail, fuel_nat);

    // 1. cn_models =~= spec_cn
    assert(cn_models.len() == spec_cn.len());
    assert forall|j: int| 0 <= j < cn_models.len() as int implies
        cn_models[j] == spec_cn[j]
    by {}
    assert(cn_models =~= spec_cn);

    // 2. Cross sizes view matches
    let spec_cross: Seq<RationalModel> =
        Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.width);
    assert(cross_view =~= spec_cross) by {
        assert(cross_view.len() == spec_cross.len());
        assert forall|j: int| 0 <= j < cross_view.len() as int implies
            cross_view[j] == spec_cross[j]
        by {}
    }

    // 3. Weights from spec_fi match spec_weights
    let spec_weights_fi: Seq<RationalModel> =
        Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
    assert(spec_weights_fi =~= spec_weights) by {
        assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
            spec_weights_fi[i] == spec_weights[i]
        by {}
    }

    // weight_view =~= spec_weights =~= spec_weights_fi
    assert(weight_view =~= spec_weights) by {
        assert forall|i: int| 0 <= i < weight_view.len() as int implies
            weight_view[i] == spec_weights[i]
        by {}
    }
}

/// Connect flex row exec result to spec layout_flex_row_body.
pub proof fn lemma_flex_row_spec_connection(
    limits: Limits<RationalModel>,
    padding: Padding<RationalModel>,
    spacing: RationalModel,
    alignment: Alignment,
    spec_fi: Seq<FlexItem<RationalModel>>,
    spec_weights: Seq<RationalModel>,
    total_weight: RationalModel,
    avail: RationalModel,
    cn_models: Seq<Node<RationalModel>>,
    cross_view: Seq<RationalModel>,
    weight_view: Seq<RationalModel>,
    merged: Node<RationalModel>,
    fuel_nat: nat,
)
    requires
        spec_fi.len() == cn_models.len(),
        spec_fi.len() == cross_view.len(),
        spec_fi.len() == spec_weights.len(),
        spec_fi.len() == weight_view.len(),
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            forall|j: int| 0 <= j < cn_models.len() ==>
                cn_models[j] == layout_widget::<RationalModel>(
                    Limits { min: inner.min, max: Size::new(
                        flex_child_main_size(spec_weights[j], total_weight, avail),
                        inner.max.height) },
                    spec_fi[j].child, fuel_nat)
        }),
        forall|j: int| 0 <= j < cross_view.len() ==>
            cross_view[j] == cn_models[j].size.height,
        forall|j: int| 0 <= j < weight_view.len() ==>
            weight_view[j] == spec_weights[j],
        forall|j: int| 0 <= j < spec_weights.len() ==>
            spec_weights[j] == spec_fi[j].weight,
        merged == merge_layout::<RationalModel>(
            flex_row_layout(limits, padding, spacing, alignment, weight_view, cross_view),
            cn_models),
    ensures
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let spec_weights_fi = Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
            let spec_cn = flex_row_widget_child_nodes(
                inner, spec_fi, spec_weights, total_weight, avail, fuel_nat);
            merged == layout_flex_row_body::<RationalModel>(
                limits, padding, spacing, alignment, spec_weights_fi, spec_cn)
        }),
{
    let inner = limits.shrink(padding.horizontal(), padding.vertical());
    let spec_cn = flex_row_widget_child_nodes(
        inner, spec_fi, spec_weights, total_weight, avail, fuel_nat);

    // 1. cn_models =~= spec_cn
    assert(cn_models.len() == spec_cn.len());
    assert forall|j: int| 0 <= j < cn_models.len() as int implies
        cn_models[j] == spec_cn[j]
    by {}
    assert(cn_models =~= spec_cn);

    // 2. Cross sizes view matches (height for row direction)
    let spec_cross: Seq<RationalModel> =
        Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.height);
    assert(cross_view =~= spec_cross) by {
        assert(cross_view.len() == spec_cross.len());
        assert forall|j: int| 0 <= j < cross_view.len() as int implies
            cross_view[j] == spec_cross[j]
        by {}
    }

    // 3. Weights match
    let spec_weights_fi: Seq<RationalModel> =
        Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
    assert(spec_weights_fi =~= spec_weights) by {
        assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
            spec_weights_fi[i] == spec_weights[i]
        by {}
    }

    assert(weight_view =~= spec_weights) by {
        assert forall|i: int| 0 <= i < weight_view.len() as int implies
            weight_view[i] == spec_weights[i]
        by {}
    }
}

// ── Absolute spec connection proof ───────────────────────────────

/// Connect absolute exec result to spec layout_absolute_body.
pub proof fn lemma_absolute_spec_connection(
    limits: Limits<RationalModel>,
    padding: Padding<RationalModel>,
    spec_ac: Seq<AbsoluteChild<RationalModel>>,
    cn_models: Seq<Node<RationalModel>>,
    sizes_view: Seq<Size<RationalModel>>,
    ox_view: Seq<RationalModel>,
    oy_view: Seq<RationalModel>,
    exec_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)>,
    merged: Node<RationalModel>,
    fuel_nat: nat,
)
    requires
        spec_ac.len() == cn_models.len(),
        spec_ac.len() == sizes_view.len(),
        spec_ac.len() == ox_view.len(),
        spec_ac.len() == oy_view.len(),
        spec_ac.len() == exec_data.len(),
        // cn_models match spec
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            forall|j: int| 0 <= j < cn_models.len() ==>
                cn_models[j] == layout_widget::<RationalModel>(
                    inner, spec_ac[j].child, fuel_nat)
        }),
        // sizes match cn_models
        forall|j: int| 0 <= j < sizes_view.len() ==>
            sizes_view[j] == cn_models[j].size,
        // offsets match spec_ac
        forall|j: int| 0 <= j < ox_view.len() ==>
            ox_view[j] == spec_ac[j].x,
        forall|j: int| 0 <= j < oy_view.len() ==>
            oy_view[j] == spec_ac[j].y,
        // exec_data built from offsets + sizes
        forall|j: int| 0 <= j < exec_data.len() ==>
            exec_data[j] == (ox_view[j], oy_view[j], sizes_view[j]),
        // merged from merge_layout(absolute_layout(..., exec_data), cn_models)
        merged == merge_layout::<RationalModel>(
            absolute_layout(limits, padding, exec_data),
            cn_models),
    ensures
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let spec_cn = absolute_widget_child_nodes(inner, spec_ac, fuel_nat);
            let body_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)> =
                Seq::new(spec_cn.len(), |i: int|
                    (spec_ac[i].x, spec_ac[i].y, spec_cn[i].size));
            merged == merge_layout::<RationalModel>(
                absolute_layout(limits, padding, body_data),
                spec_cn)
        }),
{
    let inner = limits.shrink(padding.horizontal(), padding.vertical());
    let spec_cn = absolute_widget_child_nodes(inner, spec_ac, fuel_nat);

    // 1. cn_models =~= spec_cn
    assert(cn_models.len() == spec_cn.len());
    assert forall|j: int| 0 <= j < cn_models.len() as int implies
        cn_models[j] == spec_cn[j]
    by {}
    assert(cn_models =~= spec_cn);

    // 2. sizes match
    let spec_sizes: Seq<Size<RationalModel>> =
        Seq::new(spec_cn.len(), |i: int| spec_cn[i].size);
    assert(sizes_view =~= spec_sizes) by {
        assert forall|j: int| 0 <= j < sizes_view.len() as int implies
            sizes_view[j] == spec_sizes[j]
        by {}
    }

    // 3. exec_data matches body_data
    let body_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)> =
        Seq::new(spec_cn.len(), |i: int| (spec_ac[i].x, spec_ac[i].y, spec_cn[i].size));
    assert(exec_data =~= body_data) by {
        assert forall|j: int| 0 <= j < exec_data.len() as int implies
            exec_data[j] == body_data[j]
        by {
            assert(ox_view[j] == spec_ac[j].x);
            assert(oy_view[j] == spec_ac[j].y);
        }
    }
}

} // verus!
