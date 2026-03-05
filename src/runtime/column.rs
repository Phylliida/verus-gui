use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::alignment::align_offset;
use crate::layout::*;
use crate::layout::proofs::*;

verus! {

/// Compute align_offset at runtime.
pub fn align_offset_exec(
    alignment: &Alignment,
    available: &RuntimeRational,
    used: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        available.wf_spec(),
        used.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == align_offset::<RationalModel>(*alignment, available@, used@),
{
    match alignment {
        Alignment::Start => {
            RuntimeRational::from_int(0)
        },
        Alignment::Center => {
            let diff = available.sub(used);
            let two = RuntimeRational::from_int(2);
            diff.div(&two)
        },
        Alignment::End => {
            available.sub(used)
        },
    }
}

/// Execute column layout: build a parent Node with children laid out vertically.
pub fn column_layout_exec(
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
        out@ == column_layout::<RationalModel>(
            limits@, padding@, spacing@, *alignment,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@),
        ),
{
    let ghost spec_sizes: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);

    // Compute available width
    let pad_h = padding.horizontal_exec();
    let available_width = limits.max.width.sub(&pad_h);

    // Compute content height: sum of child heights + (n-1) * spacing
    let n = child_sizes.len();
    let mut content_height = RuntimeRational::from_int(0);
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            content_height.wf_spec(),
            content_height@ == sum_heights::<RationalModel>(spec_sizes, i as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - i,
    {
        content_height = content_height.add(&child_sizes[i].height);
        i = i + 1;
    }

    // Add spacing: (n-1) * spacing for n > 0
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

        content_height = content_height.add(&sp_total);
    }

    // Compute total height and resolve parent size
    let pad_v = padding.vertical_exec();
    let total_height = pad_v.add(&content_height);
    let total_width = copy_rational(&limits.max.width);

    // Resolve: clamp each dimension — max(min, min(val, max)) to match limits.resolve()
    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    // Establish children sequence length
    proof {
        lemma_column_children_len::<RationalModel>(
            padding@, spacing@, *alignment, spec_sizes, available_width@, 0,
        );
    }

    // Build children
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut y_pos = copy_rational(&padding.top);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            y_pos.wf_spec(),
            k < n ==> y_pos@ == child_y_position::<RationalModel>(padding@.top, spec_sizes, spacing@, k as nat),
            available_width.wf_spec(),
            spacing.wf_spec(),
            padding.wf_spec(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
            column_children::<RationalModel>(
                padding@, spacing@, *alignment, spec_sizes, available_width@, 0,
            ).len() == spec_sizes.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == column_children::<RationalModel>(
                    padding@, spacing@, *alignment, spec_sizes, available_width@, 0,
                )[j]
            },
        decreases n - k,
    {
        // Tell Z3 what column_children[k] should be
        proof {
            lemma_column_children_element::<RationalModel>(
                padding@, spacing@, *alignment, spec_sizes, available_width@, k as nat,
            );
        }

        let child_w = copy_rational(&child_sizes[k].width);
        let x_offset = align_offset_exec(alignment, &available_width, &child_w);
        let child_x = padding.left.add(&x_offset);
        let child_y = copy_rational(&y_pos);
        let cs = child_sizes[k].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        // Advance y position
        if k + 1 < n {
            y_pos = y_pos.add(&child_sizes[k].height);
            y_pos = y_pos.add(spacing);
        }

        k = k + 1;
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = column_layout::<RationalModel>(
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
        let cc = column_children::<RationalModel>(
            padding@, spacing@, *alignment, spec_sizes, available_width@, 0,
        );
        assert(out@.children == cc);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} // verus!
