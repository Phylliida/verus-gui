use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::size::Size;
use crate::node::Node;
use crate::layout::wrap::*;
use crate::layout::wrap_proofs::*;

verus! {

/// Execute wrap layout: place children left-to-right with line wrapping.
pub fn wrap_layout_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_spacing: &RuntimeRational,
    v_spacing: &RuntimeRational,
    child_sizes: &Vec<RuntimeSize>,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == wrap_layout::<RationalModel>(
            limits@, padding@, h_spacing@, v_spacing@,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@),
        ),
{
    let ghost spec_sizes: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);

    let n = child_sizes.len();

    // Available width for wrapping
    let available_width = limits.max.width.sub(&padding.horizontal_exec());

    // ── Build children via cursor tracking ──
    let mut cursor_x = RuntimeRational::from_int(0);
    let mut cursor_y = RuntimeRational::from_int(0);
    let mut line_height = RuntimeRational::from_int(0);
    let mut content_width = RuntimeRational::from_int(0);

    // Establish children length
    let ghost spec_children = wrap_children(
        padding@, h_spacing@, v_spacing@, spec_sizes, available_width@, 0,
    );
    proof {
        lemma_wrap_children_len::<RationalModel>(
            padding@, h_spacing@, v_spacing@, spec_sizes, available_width@, 0,
        );
    }

    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut i: usize = 0;
    let zero = RuntimeRational::from_int(0);

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            cursor_x.wf_spec(), cursor_y.wf_spec(),
            line_height.wf_spec(), content_width.wf_spec(),
            available_width.wf_spec(),
            h_spacing.wf_spec(), v_spacing.wf_spec(), padding.wf_spec(),
            zero.wf_spec(), zero@ == RationalModel::from_int_spec(0),
            ({
                let wc = wrap_cursor(spec_sizes, h_spacing@, v_spacing@, available_width@, i as nat);
                &&& cursor_x@ == wc.x
                &&& cursor_y@ == wc.y
                &&& line_height@ == wc.line_height
                &&& content_width@ == wc.content_width
            }),
            children@.len() == i as int,
            spec_children.len() == spec_sizes.len(),
            spec_children =~= wrap_children(
                padding@, h_spacing@, v_spacing@, spec_sizes, available_width@, 0nat,
            ),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
            forall|j: int| 0 <= j < children@.len() ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j]@ == spec_children[j]
            },
        decreases n - i,
    {
        proof {
            lemma_wrap_children_element::<RationalModel>(
                padding@, h_spacing@, v_spacing@, spec_sizes, available_width@, i as nat,
            );
        }

        let child_w = copy_rational(&child_sizes[i].width);
        let child_h = copy_rational(&child_sizes[i].height);

        // Check if we need a line break
        let at_line_start = cursor_x.le(&zero);
        let would_fit = cursor_x.add(&child_w).le(&available_width);
        let needs_break = !at_line_start && !would_fit;

        let (cx, cy) = if needs_break {
            // New line
            let new_y = cursor_y.add(&line_height).add(v_spacing);
            (RuntimeRational::from_int(0), new_y)
        } else {
            // Same line
            (copy_rational(&cursor_x), copy_rational(&cursor_y))
        };

        // Position the child
        let child_x = padding.left.add(&cx);
        let child_y = padding.top.add(&cy);
        let cs = child_sizes[i].copy_size();
        let child_node = RuntimeNode::leaf_exec(child_x, child_y, cs);

        proof {
            // Z3 connects runtime values to spec via invariant + element lemma
        }

        children.push(child_node);

        // Update cursor
        if needs_break {
            cursor_x = child_w.add(h_spacing);
            cursor_y = cy;
            line_height = child_h;
            content_width = content_width.max(&child_w);
        } else {
            let new_line_w = cursor_x.add(&child_w);
            content_width = content_width.max(&new_line_w);
            cursor_x = new_line_w.add(h_spacing);
            // cursor_y unchanged
            line_height = line_height.max(&child_h);
        }

        i = i + 1;
    }

    // ── Compute content size + parent size ──
    let content_size = if n == 0 {
        RuntimeSize::zero_exec()
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

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = wrap_layout::<RationalModel>(
        limits@, padding@, h_spacing@, v_spacing@, spec_sizes,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        assert(out@.children == spec_children);
        assert(out.children@.len() == out@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i]@ == out@.children[i]
        } by {};
    }

    out
}

} // verus!
