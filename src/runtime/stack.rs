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
use crate::layout::stack::*;
use crate::layout::proofs::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub fn stack_layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    h_align: &Alignment,
    v_align: &Alignment,
    child_sizes: &Vec<RuntimeSize<R, V>>,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == stack_layout::<V>(
            limits@, padding@, *h_align, *v_align,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@),
        ),
{
    let ghost spec_sizes: Seq<Size<V>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@);

    let n = child_sizes.len();

    //  Compute content size: max_width x max_height
    let mut max_w = limits.min.width.zero_like();
    let mut max_h = limits.min.width.zero_like();
    let mut i: usize = 0;

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
            max_w@ == max_width::<V>(spec_sizes, i as nat),
            max_h@ == max_height::<V>(spec_sizes, i as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j].model@,
        decreases n - i,
    {
        proof {
            reveal(max_width);
            reveal(max_height);
        }
        max_w = max_w.max(&child_sizes[i].width);
        max_h = max_h.max(&child_sizes[i].height);
        i = i + 1;
    }

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&max_w);
    let total_height = pad_v.add(&max_h);

    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    let available_width = limits.max.width.sub(&padding.horizontal_exec());
    let available_height = limits.max.height.sub(&padding.vertical_exec());

    proof {
        lemma_stack_children_len::<V>(
            padding@, *h_align, *v_align, spec_sizes,
            available_width@, available_height@, 0,
        );
    }

    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
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
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j].model@,
            stack_children::<V>(
                padding@, *h_align, *v_align, spec_sizes,
                available_width@, available_height@, 0,
            ).len() == spec_sizes.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j].model@ == stack_children::<V>(
                    padding@, *h_align, *v_align, spec_sizes,
                    available_width@, available_height@, 0,
                )[j]
            },
        decreases n - k,
    {
        proof {
            lemma_stack_children_element::<V>(
                padding@, *h_align, *v_align, spec_sizes,
                available_width@, available_height@, k as nat,
            );
        }

        let child_w = child_sizes[k].width.copy();
        let child_h = child_sizes[k].height.copy();
        let x_offset = align_offset_exec(h_align, &available_width, &child_w);
        let y_offset = align_offset_exec(v_align, &available_height, &child_h);
        let child_x = padding.left.add(&x_offset);
        let child_y = padding.top.add(&y_offset);
        let cs = child_sizes[k].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        k = k + 1;
    }

    let x = limits.min.width.zero_like();
    let y = limits.min.width.zero_like();

    let ghost parent_model = stack_layout::<V>(
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
        let sc = stack_children::<V>(
            padding@, *h_align, *v_align, spec_sizes,
            available_width@, available_height@, 0,
        );
        assert(out@.children == sc);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i].model@ == out@.children[i]
        } by {};
    }

    out
}

} //  verus!
