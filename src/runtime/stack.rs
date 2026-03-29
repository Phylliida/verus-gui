use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::linear::align_offset_exec;
use crate::size::Size;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::alignment::align_offset;
use crate::layout::stack::*;
use crate::layout::proofs::*;

verus! {

///  Execute stack layout: build a parent Node with all children overlapping,
///  each independently aligned on both axes.
pub fn stack_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_align: &Alignment,
    v_align: &Alignment,
    child_sizes: &Vec<RuntimeSize>,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == stack_layout::<RationalModel>(
            limits@, padding@, *h_align, *v_align,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@),
        ),
{
    let ghost spec_sizes: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);

    let n = child_sizes.len();

    //  Compute content size: max_width x max_height
    let mut max_w = RuntimeRational::from_int(0);
    let mut max_h = RuntimeRational::from_int(0);
    let mut i: usize = 0;

    //  Reveal initial step: max_width(spec_sizes, 0) == T::zero()
    proof {
        reveal(max_width);
        reveal(max_height);
    }

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            max_w.wf_spec(),
            max_h.wf_spec(),
            max_w@ == max_width::<RationalModel>(spec_sizes, i as nat),
            max_h@ == max_height::<RationalModel>(spec_sizes, i as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - i,
    {
        proof {
            //  Unfold one step: max_width(sizes, i+1) == max(max_width(sizes, i), sizes[i].width)
            reveal(max_width);
            reveal(max_height);
        }
        max_w = max_w.max(&child_sizes[i].width);
        max_h = max_h.max(&child_sizes[i].height);
        i = i + 1;
    }

    //  Compute total size and resolve
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&max_w);
    let total_height = pad_v.add(&max_h);

    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    //  Available space for alignment
    let available_width = limits.max.width.sub(&padding.horizontal_exec());
    let available_height = limits.max.height.sub(&padding.vertical_exec());

    //  Establish children sequence length
    proof {
        lemma_stack_children_len::<RationalModel>(
            padding@, *h_align, *v_align, spec_sizes,
            available_width@, available_height@, 0,
        );
    }

    //  Build children — each independently aligned, no cumulative position
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            available_width.wf_spec(),
            available_height.wf_spec(),
            padding.wf_spec(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
            stack_children::<RationalModel>(
                padding@, *h_align, *v_align, spec_sizes,
                available_width@, available_height@, 0,
            ).len() == spec_sizes.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == stack_children::<RationalModel>(
                    padding@, *h_align, *v_align, spec_sizes,
                    available_width@, available_height@, 0,
                )[j]
            },
        decreases n - k,
    {
        proof {
            lemma_stack_children_element::<RationalModel>(
                padding@, *h_align, *v_align, spec_sizes,
                available_width@, available_height@, k as nat,
            );
        }

        let child_w = copy_rational(&child_sizes[k].width);
        let child_h = copy_rational(&child_sizes[k].height);
        let x_offset = align_offset_exec(h_align, &available_width, &child_w);
        let y_offset = align_offset_exec(v_align, &available_height, &child_h);
        let child_x = padding.left.add(&x_offset);
        let child_y = padding.top.add(&y_offset);
        let cs = child_sizes[k].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        k = k + 1;
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = stack_layout::<RationalModel>(
        limits@, padding@, *h_align, *v_align, spec_sizes,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        reveal(stack_layout);
        reveal(stack_content_size);
        let sc = stack_children::<RationalModel>(
            padding@, *h_align, *v_align, spec_sizes,
            available_width@, available_height@, 0,
        );
        assert(out@.children == sc);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} //  verus!
