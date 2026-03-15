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
use crate::layout::flex::*;
use crate::layout::flex_proofs::*;

verus! {

/// Execute flex column layout: distribute height proportionally by weights.
pub fn flex_column_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    h_align: &Alignment,
    weights: &Vec<RuntimeRational>,
    child_cross_sizes: &Vec<RuntimeRational>,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        weights@.len() == child_cross_sizes@.len(),
        forall|i: int| 0 <= i < weights@.len() ==> weights@[i].wf_spec(),
        forall|i: int| 0 <= i < child_cross_sizes@.len() ==> child_cross_sizes@[i].wf_spec(),
        // Total weight must be nonzero for proportional division
        weights@.len() > 0 ==> !sum_weights::<RationalModel>(
            Seq::new(weights@.len() as nat, |i: int| weights@[i]@),
            weights@.len() as nat,
        ).eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == flex_column_layout::<RationalModel>(
            limits@, padding@, spacing@, *h_align,
            Seq::new(weights@.len() as nat, |i: int| weights@[i]@),
            Seq::new(child_cross_sizes@.len() as nat, |i: int| child_cross_sizes@[i]@),
        ),
        out.children@.len() == weights@.len(),
{
    proof { reveal(flex_column_layout); }
    let ghost spec_weights: Seq<RationalModel> =
        Seq::new(weights@.len() as nat, |i: int| weights@[i]@);
    let ghost spec_cross: Seq<RationalModel> =
        Seq::new(child_cross_sizes@.len() as nat, |i: int| child_cross_sizes@[i]@);
    // Carry the nonzero total weight fact as ghost
    proof {
        if weights@.len() > 0 {
            assert(!sum_weights::<RationalModel>(spec_weights, weights@.len() as nat)
                .eqv_spec(RationalModel::from_int_spec(0)));
        }
    }

    let n = weights.len();

    // Compute total_weight = sum of all weights
    let mut total_weight = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == weights@.len(),
            total_weight.wf_spec(),
            total_weight@ == sum_weights::<RationalModel>(spec_weights, i as nat),
            forall|j: int| 0 <= j < weights@.len() ==> weights@[j].wf_spec(),
            forall|j: int| 0 <= j < weights@.len() ==> spec_weights[j] == weights@[j]@,
        decreases n - i,
    {
        total_weight = total_weight.add(&weights[i]);
        i = i + 1;
    }

    // Compute available dimensions
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let available_width = limits.max.width.sub(&pad_h);

    // Compute total_spacing
    let mut total_spacing = RuntimeRational::from_int(0);
    if n > 0 {
        let mut j: usize = 0;
        let n_minus_1 = n - 1;
        while j < n_minus_1
            invariant
                0 <= j <= n_minus_1,
                n_minus_1 == n - 1,
                n > 0,
                total_spacing.wf_spec(),
                spacing.wf_spec(),
                total_spacing@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases n_minus_1 - j,
        {
            total_spacing = total_spacing.add(spacing);
            j = j + 1;
        }
    }

    let avail_minus_pad = limits.max.height.sub(&pad_v);
    let available_height = avail_minus_pad.sub(&total_spacing);

    // Resolve parent size
    let parent_size_w = copy_rational(&limits.max.width);
    let parent_size_h = copy_rational(&limits.max.height);
    let parent_width = limits.min.width.max(&parent_size_w.min(&limits.max.width));
    let parent_height = limits.min.height.max(&parent_size_h.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    // Establish children sequence length
    proof {
        lemma_flex_column_children_len::<RationalModel>(
            padding@, spacing@, *h_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0,
        );
    }

    // Build children
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut y_pos = copy_rational(&padding.top);
    let mut main_sum = RuntimeRational::from_int(0);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == weights@.len(),
            spec_weights.len() == n as nat,
            spec_cross.len() == n as nat,
            y_pos.wf_spec(),
            main_sum.wf_spec(),
            main_sum@ == flex_main_sum::<RationalModel>(
                spec_weights, total_weight@, available_height@, k as nat,
            ),
            k < n ==> y_pos@ == flex_column_child_y::<RationalModel>(
                padding@.top, spec_weights, total_weight@, available_height@, spacing@, k as nat,
            ),
            available_width.wf_spec(),
            available_height.wf_spec(),
            total_weight.wf_spec(),
            n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
            spacing.wf_spec(),
            padding.wf_spec(),
            n == child_cross_sizes@.len(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < weights@.len() ==> weights@[j].wf_spec(),
            forall|j: int| 0 <= j < weights@.len() ==> spec_weights[j] == weights@[j]@,
            forall|j: int| 0 <= j < child_cross_sizes@.len() ==> child_cross_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_cross_sizes@.len() ==> spec_cross[j] == child_cross_sizes@[j]@,
            flex_column_children::<RationalModel>(
                padding@, spacing@, *h_align, spec_weights, spec_cross,
                total_weight@, available_width@, available_height@, 0,
            ).len() == spec_weights.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == flex_column_children::<RationalModel>(
                    padding@, spacing@, *h_align, spec_weights, spec_cross,
                    total_weight@, available_width@, available_height@, 0,
                )[j]
            },
        decreases n - k,
    {
        proof {
            lemma_flex_column_children_element::<RationalModel>(
                padding@, spacing@, *h_align, spec_weights, spec_cross,
                total_weight@, available_width@, available_height@, k as nat,
            );
        }

        // child_h = weight[k] / total_weight * available_height
        let w_k = copy_rational(&weights[k]);
        let child_h = w_k.div(&total_weight).mul(&available_height);
        let cross_k = copy_rational(&child_cross_sizes[k]);
        let x_offset = align_offset_exec(h_align, &available_width, &cross_k);
        let child_x = padding.left.add(&x_offset);
        let child_y = copy_rational(&y_pos);
        let cs = RuntimeSize::new(copy_rational(&child_cross_sizes[k]), copy_rational(&child_h));
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        // Update main_sum and y_pos
        main_sum = main_sum.add(&child_h);
        if k + 1 < n {
            y_pos = padding.top.add(&main_sum);
            y_pos = y_pos.add(&{
                // repeated_add(spacing, k+1)
                let mut sp = RuntimeRational::from_int(0);
                let mut m: usize = 0;
                let target = k + 1;
                while m < target
                    invariant
                        0 <= m <= target,
                        target == k + 1,
                        sp.wf_spec(),
                        spacing.wf_spec(),
                        sp@ == repeated_add::<RationalModel>(spacing@, m as nat),
                    decreases target - m,
                {
                    sp = sp.add(spacing);
                    m = m + 1;
                }
                sp
            });
        }

        k = k + 1;
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = flex_column_layout::<RationalModel>(
        limits@, padding@, spacing@, *h_align, spec_weights, spec_cross,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        let fc = flex_column_children::<RationalModel>(
            padding@, spacing@, *h_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0,
        );
        lemma_flex_column_children_len::<RationalModel>(
            padding@, spacing@, *h_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0nat,
        );
        assert(out@.children == fc);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

/// Execute flex row layout: distribute width proportionally by weights.
pub fn flex_row_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    v_align: &Alignment,
    weights: &Vec<RuntimeRational>,
    child_cross_sizes: &Vec<RuntimeRational>,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        weights@.len() == child_cross_sizes@.len(),
        forall|i: int| 0 <= i < weights@.len() ==> weights@[i].wf_spec(),
        forall|i: int| 0 <= i < child_cross_sizes@.len() ==> child_cross_sizes@[i].wf_spec(),
        weights@.len() > 0 ==> !sum_weights::<RationalModel>(
            Seq::new(weights@.len() as nat, |i: int| weights@[i]@),
            weights@.len() as nat,
        ).eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == flex_row_layout::<RationalModel>(
            limits@, padding@, spacing@, *v_align,
            Seq::new(weights@.len() as nat, |i: int| weights@[i]@),
            Seq::new(child_cross_sizes@.len() as nat, |i: int| child_cross_sizes@[i]@),
        ),
        out.children@.len() == weights@.len(),
{
    proof { reveal(flex_row_layout); }
    let ghost spec_weights: Seq<RationalModel> =
        Seq::new(weights@.len() as nat, |i: int| weights@[i]@);
    let ghost spec_cross: Seq<RationalModel> =
        Seq::new(child_cross_sizes@.len() as nat, |i: int| child_cross_sizes@[i]@);
    proof {
        if weights@.len() > 0 {
            assert(!sum_weights::<RationalModel>(spec_weights, weights@.len() as nat)
                .eqv_spec(RationalModel::from_int_spec(0)));
        }
    }

    let n = weights.len();

    // Compute total_weight
    let mut total_weight = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == weights@.len(),
            total_weight.wf_spec(),
            total_weight@ == sum_weights::<RationalModel>(spec_weights, i as nat),
            forall|j: int| 0 <= j < weights@.len() ==> weights@[j].wf_spec(),
            forall|j: int| 0 <= j < weights@.len() ==> spec_weights[j] == weights@[j]@,
        decreases n - i,
    {
        total_weight = total_weight.add(&weights[i]);
        i = i + 1;
    }

    // Compute available dimensions
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let available_height = limits.max.height.sub(&pad_v);

    // Compute total_spacing
    let mut total_spacing = RuntimeRational::from_int(0);
    if n > 0 {
        let mut j: usize = 0;
        let n_minus_1 = n - 1;
        while j < n_minus_1
            invariant
                0 <= j <= n_minus_1,
                n_minus_1 == n - 1,
                n > 0,
                total_spacing.wf_spec(),
                spacing.wf_spec(),
                total_spacing@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases n_minus_1 - j,
        {
            total_spacing = total_spacing.add(spacing);
            j = j + 1;
        }
    }

    let avail_minus_pad = limits.max.width.sub(&pad_h);
    let available_width = avail_minus_pad.sub(&total_spacing);

    // Resolve parent size
    let parent_size_w = copy_rational(&limits.max.width);
    let parent_size_h = copy_rational(&limits.max.height);
    let parent_width = limits.min.width.max(&parent_size_w.min(&limits.max.width));
    let parent_height = limits.min.height.max(&parent_size_h.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    // Establish children sequence length
    proof {
        lemma_flex_row_children_len::<RationalModel>(
            padding@, spacing@, *v_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0,
        );
    }

    // Build children
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut x_pos = copy_rational(&padding.left);
    let mut main_sum = RuntimeRational::from_int(0);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == weights@.len(),
            spec_weights.len() == n as nat,
            spec_cross.len() == n as nat,
            x_pos.wf_spec(),
            main_sum.wf_spec(),
            main_sum@ == flex_main_sum::<RationalModel>(
                spec_weights, total_weight@, available_width@, k as nat,
            ),
            k < n ==> x_pos@ == flex_row_child_x::<RationalModel>(
                padding@.left, spec_weights, total_weight@, available_width@, spacing@, k as nat,
            ),
            available_width.wf_spec(),
            available_height.wf_spec(),
            total_weight.wf_spec(),
            n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
            spacing.wf_spec(),
            padding.wf_spec(),
            n == child_cross_sizes@.len(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < weights@.len() ==> weights@[j].wf_spec(),
            forall|j: int| 0 <= j < weights@.len() ==> spec_weights[j] == weights@[j]@,
            forall|j: int| 0 <= j < child_cross_sizes@.len() ==> child_cross_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_cross_sizes@.len() ==> spec_cross[j] == child_cross_sizes@[j]@,
            flex_row_children::<RationalModel>(
                padding@, spacing@, *v_align, spec_weights, spec_cross,
                total_weight@, available_width@, available_height@, 0,
            ).len() == spec_weights.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == flex_row_children::<RationalModel>(
                    padding@, spacing@, *v_align, spec_weights, spec_cross,
                    total_weight@, available_width@, available_height@, 0,
                )[j]
            },
        decreases n - k,
    {
        proof {
            lemma_flex_row_children_element::<RationalModel>(
                padding@, spacing@, *v_align, spec_weights, spec_cross,
                total_weight@, available_width@, available_height@, k as nat,
            );
        }

        // child_w = weight[k] / total_weight * available_width
        let w_k = copy_rational(&weights[k]);
        let child_w = w_k.div(&total_weight).mul(&available_width);
        let cross_k = copy_rational(&child_cross_sizes[k]);
        let y_offset = align_offset_exec(v_align, &available_height, &cross_k);
        let child_x = copy_rational(&x_pos);
        let child_y = padding.top.add(&y_offset);
        let cs = RuntimeSize::new(copy_rational(&child_w), copy_rational(&child_cross_sizes[k]));
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        // Update main_sum and x_pos
        main_sum = main_sum.add(&child_w);
        if k + 1 < n {
            x_pos = padding.left.add(&main_sum);
            x_pos = x_pos.add(&{
                let mut sp = RuntimeRational::from_int(0);
                let mut m: usize = 0;
                let target = k + 1;
                while m < target
                    invariant
                        0 <= m <= target,
                        target == k + 1,
                        sp.wf_spec(),
                        spacing.wf_spec(),
                        sp@ == repeated_add::<RationalModel>(spacing@, m as nat),
                    decreases target - m,
                {
                    sp = sp.add(spacing);
                    m = m + 1;
                }
                sp
            });
        }

        k = k + 1;
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = flex_row_layout::<RationalModel>(
        limits@, padding@, spacing@, *v_align, spec_weights, spec_cross,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        let fr = flex_row_children::<RationalModel>(
            padding@, spacing@, *v_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0,
        );
        lemma_flex_row_children_len::<RationalModel>(
            padding@, spacing@, *v_align, spec_weights, spec_cross,
            total_weight@, available_width@, available_height@, 0nat,
        );
        assert(out@.children == fr);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} // verus!
