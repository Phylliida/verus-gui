use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::size::Size;
use crate::node::Node;
use crate::layout::absolute::*;
use crate::layout::absolute_proofs::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Execute absolute layout: position each child at (padding.left + x, padding.top + y),
///  compute bounding box for content size.
pub fn absolute_layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    offsets_x: &Vec<R>,
    offsets_y: &Vec<R>,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        child_sizes@.len() == offsets_x@.len(),
        child_sizes@.len() == offsets_y@.len(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
        forall|i: int| 0 <= i < offsets_x@.len() ==> offsets_x@[i].wf_spec(),
        forall|i: int| 0 <= i < offsets_y@.len() ==> offsets_y@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == absolute_layout::<V>(
            limits@, padding@,
            Seq::new(child_sizes@.len() as nat, |i: int|
                (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@)),
        ),
{
    proof { reveal(absolute_layout); }
    let ghost spec_data: Seq<(V, V, Size<V>)> =
        Seq::new(child_sizes@.len() as nat, |i: int|
            (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@));

    let n = child_sizes.len();

    //  Compute bounding box: max of (x + width) and max of (y + height)
    let mut max_right = padding.left.zero_like();
    let mut max_bottom = padding.left.zero_like();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            n == offsets_x@.len(),
            n == offsets_y@.len(),
            max_right.wf_spec(),
            max_bottom.wf_spec(),
            max_right@ == absolute_max_right::<V>(spec_data, i as nat),
            max_bottom@ == absolute_max_bottom::<V>(spec_data, i as nat),
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] offsets_x@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] offsets_y@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> spec_data[j] ==
                (offsets_x@[j]@, offsets_y@[j]@, child_sizes@[j]@),
        decreases n - i,
    {
        let right = offsets_x[i].add(&child_sizes[i].width);
        let bottom = offsets_y[i].add(&child_sizes[i].height);
        max_right = max_right.max(&right);
        max_bottom = max_bottom.max(&bottom);
        i = i + 1;
    }

    //  Compute total size and resolve
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&max_right);
    let total_height = pad_v.add(&max_bottom);

    let parent_size = limits.resolve_exec(RuntimeSize::new(total_width, total_height));

    //  Build children nodes: each at (padding.left + x, padding.top + y)
    proof {
        lemma_absolute_children_len::<V>(padding@, spec_data, 0);
    }

    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            n == offsets_x@.len(),
            n == offsets_y@.len(),
            spec_data.len() == n as nat,
            padding.wf_spec(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] offsets_x@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] offsets_y@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> spec_data[j] ==
                (offsets_x@[j]@, offsets_y@[j]@, child_sizes@[j]@),
            absolute_children::<V>(padding@, spec_data, 0).len() == n as nat,
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_shallow()
                &&& children@[j]@ == absolute_children::<V>(
                    padding@, spec_data, 0)[j]
            },
        decreases n - k,
    {
        proof {
            lemma_absolute_children_element::<V>(
                padding@, spec_data, k as nat);
        }

        let child_x = padding.left.add(&offsets_x[k]);
        let child_y = padding.top.add(&offsets_y[k]);
        let cs = child_sizes[k].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);
        children.push(child_node);

        k = k + 1;
    }

    let x = padding.left.zero_like();
    let y = padding.left.zero_like();

    let ghost parent_model = absolute_layout::<V>(
        limits@, padding@, spec_data);

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        let ac = absolute_children::<V>(padding@, spec_data, 0);
        assert(out@.children == ac);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} //  verus!
