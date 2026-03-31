use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::size::Size;
use crate::node::Node;
use crate::layout::wrap::*;
use crate::layout::wrap_proofs::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub fn wrap_layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    h_spacing: &R,
    v_spacing: &R,
    child_sizes: &Vec<RuntimeSize<R, V>>,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == wrap_layout::<V>(
            limits.model@, padding.model@, h_spacing.model(), v_spacing.model(),
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@),
        ),
{
    proof { reveal(wrap_layout); }
    let ghost spec_sizes: Seq<Size<V>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@);

    let n = child_sizes.len();
    let available_width = limits.max.width.sub(&padding.horizontal_exec());

    let mut cursor_x = h_spacing.zero_like();
    let mut cursor_y = h_spacing.zero_like();
    let mut line_height = h_spacing.zero_like();
    let mut content_width = h_spacing.zero_like();

    let ghost spec_children = wrap_children(
        padding.model@, h_spacing.model(), v_spacing.model(), spec_sizes, available_width.model(), 0,
    );
    proof {
        lemma_wrap_children_len::<V>(
            padding.model@, h_spacing.model(), v_spacing.model(), spec_sizes, available_width.model(), 0,
        );
    }

    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut i: usize = 0;
    let zero = h_spacing.zero_like();

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            cursor_x.wf_spec(), cursor_y.wf_spec(),
            line_height.wf_spec(), content_width.wf_spec(),
            available_width.wf_spec(),
            h_spacing.wf_spec(), v_spacing.wf_spec(), padding.wf_spec(),
            zero.wf_spec(), zero.model() == V::zero(),
            ({
                let wc = wrap_cursor(spec_sizes, h_spacing.model(), v_spacing.model(), available_width.model(), i as nat);
                &&& cursor_x.model() == wc.x
                &&& cursor_y.model() == wc.y
                &&& line_height.model() == wc.line_height
                &&& content_width.model() == wc.content_width
            }),
            children@.len() == i as int,
            spec_children.len() == spec_sizes.len(),
            spec_children =~= wrap_children(
                padding.model@, h_spacing.model(), v_spacing.model(), spec_sizes, available_width.model(), 0nat,
            ),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j].model@,
            forall|j: int| 0 <= j < children@.len() ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j].model@ == spec_children[j]
            },
        decreases n - i,
    {
        proof {
            lemma_wrap_children_element::<V>(
                padding.model@, h_spacing.model(), v_spacing.model(), spec_sizes, available_width.model(), i as nat,
            );
        }

        let child_w = child_sizes[i].width.copy();
        let child_h = child_sizes[i].height.copy();

        let at_line_start = cursor_x.le(&zero);
        let would_fit = cursor_x.add(&child_w).le(&available_width);
        let needs_break = !at_line_start && !would_fit;

        let (cx, cy) = if needs_break {
            let new_y = cursor_y.add(&line_height).add(v_spacing);
            (h_spacing.zero_like(), new_y)
        } else {
            (cursor_x.copy(), cursor_y.copy())
        };

        let child_x = padding.left.add(&cx);
        let child_y = padding.top.add(&cy);
        let cs = child_sizes[i].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);

        children.push(child_node);

        if needs_break {
            cursor_x = child_w.add(h_spacing);
            cursor_y = cy;
            line_height = child_h;
            content_width = content_width.max(&child_w);
        } else {
            let new_line_w = cursor_x.add(&child_w);
            content_width = content_width.max(&new_line_w);
            cursor_x = new_line_w.add(h_spacing);
            line_height = line_height.max(&child_h);
        }

        i = i + 1;
    }

    let content_size = if n == 0 {
        RuntimeSize::new(h_spacing.zero_like(), h_spacing.zero_like())
    } else {
        RuntimeSize::new(content_width, cursor_y.add(&line_height))
    };

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let total_width = pad_h.add(&content_size.width);
    let total_height = pad_v.add(&content_size.height);
    let parent_width = limits.min.width.max(&total_width.min(&limits.max.width));
    let parent_height = limits.min.height.max(&total_height.min(&limits.max.height));
    let parent_size = RuntimeSize::new(parent_width, parent_height);

    let x = h_spacing.zero_like();
    let y = h_spacing.zero_like();

    let ghost parent_model = wrap_layout::<V>(
        limits.model@, padding.model@, h_spacing.model(), v_spacing.model(), spec_sizes,
    );

    let out = RuntimeNode {
        x, y, size: parent_size, children,
        model: Ghost(parent_model),
    };

    proof {
        assert(out.model@.children == spec_children);
        assert(out.children@.len() == out.model@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i].model@ == out.model@.children[i]
        } by {};
    }

    out
}

} //  verus!
