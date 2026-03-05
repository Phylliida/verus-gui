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
use crate::limits::Limits;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::alignment::align_offset;
use crate::layout::*;
use crate::layout::proofs::*;

verus! {

/// Execute row layout: build a parent Node with children laid out horizontally.
pub fn row_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    alignment: &Alignment,
    child_sizes: &Vec<RuntimeSize>,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == row_layout::<RationalModel>(
            limits@, padding@, spacing@, *alignment,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@),
        ),
{
    let ghost spec_sizes: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);

    // Compute available height
    let pad_v = padding.vertical_exec();
    let available_height = limits.max.height.sub(&pad_v);

    // Compute content width: sum of child widths + (n-1) * spacing
    let n = child_sizes.len();
    let mut content_width = RuntimeRational::from_int(0);
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            content_width.wf_spec(),
            content_width@ == sum_widths::<RationalModel>(spec_sizes, i as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - i,
    {
        content_width = content_width.add(&child_sizes[i].width);
        i = i + 1;
    }

    // Add spacing
    if n > 0 {
        let mut sp_total = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        let n_minus_1 = n - 1;

        while j < n_minus_1
            invariant
                0 <= j <= n_minus_1,
                n_minus_1 == n - 1,
                n > 0,
                sp_total.wf_spec(),
                spacing.wf_spec(),
                sp_total@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases n_minus_1 - j,
        {
            sp_total = sp_total.add(spacing);
            j = j + 1;
        }

        content_width = content_width.add(&sp_total);
    }

    // Compute total width and resolve parent size
    let pad_h = padding.horizontal_exec();
    let total_width = pad_h.add(&content_width);
    let total_height = copy_rational(&limits.max.height);

    // Resolve: clamp each dimension — max(min, min(val, max)) to match limits.resolve()
    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    // Establish children sequence length
    proof {
        lemma_row_children_len::<RationalModel>(
            padding@, spacing@, *alignment, spec_sizes, available_height@, 0,
        );
    }

    // Build children
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut x_pos = copy_rational(&padding.left);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            x_pos.wf_spec(),
            k < n ==> x_pos@ == child_x_position::<RationalModel>(padding@.left, spec_sizes, spacing@, k as nat),
            available_height.wf_spec(),
            spacing.wf_spec(),
            padding.wf_spec(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
            row_children::<RationalModel>(
                padding@, spacing@, *alignment, spec_sizes, available_height@, 0,
            ).len() == spec_sizes.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == row_children::<RationalModel>(
                    padding@, spacing@, *alignment, spec_sizes, available_height@, 0,
                )[j]
            },
        decreases n - k,
    {
        // Tell Z3 what row_children[k] should be
        proof {
            lemma_row_children_element::<RationalModel>(
                padding@, spacing@, *alignment, spec_sizes, available_height@, k as nat,
            );
        }

        let child_h = copy_rational(&child_sizes[k].height);
        let y_offset = align_offset_exec(alignment, &available_height, &child_h);
        let child_y = padding.top.add(&y_offset);
        let child_x = copy_rational(&x_pos);
        let cs = child_sizes[k].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        // Advance x position
        if k + 1 < n {
            x_pos = x_pos.add(&child_sizes[k].width);
            x_pos = x_pos.add(spacing);
        }

        k = k + 1;
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = row_layout::<RationalModel>(
        limits@, padding@, spacing@, *alignment, spec_sizes,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        // Help Z3: children match model
        let rc = row_children::<RationalModel>(
            padding@, spacing@, *alignment, spec_sizes, available_height@, 0,
        );
        assert(out@.children == rc);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} // verus!
