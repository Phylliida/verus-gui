use vstd::prelude::*;
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
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Compute align_offset at runtime.
pub fn align_offset_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    alignment: &Alignment,
    available: &R,
    used: &R,
) -> (out: R)
    requires available.wf_spec(), used.wf_spec(),
    ensures out.wf_spec(), out.model() == align_offset::<V>(*alignment, available.model(), used.model()),
{
    proof { reveal(align_offset); }
    match alignment {
        Alignment::Start => {
            available.zero_like()
        },
        Alignment::Center => {
            let diff = available.sub(used);
            let two = available.one_like().add(&available.one_like());
            proof {
                //  0 < 1+1, so 1+1 ≢ 0 (required for div precondition)
                verus_algebra::lemmas::ordered_ring_lemmas::lemma_zero_lt_one::<V>();
                V::axiom_lt_iff_le_and_not_eqv(V::zero(), V::one());
                verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_pos_nonneg::<V>(V::one(), V::one());
                V::axiom_lt_iff_le_and_not_eqv(
                    V::zero(), V::one().add(V::one()));
                V::axiom_eqv_symmetric(
                    V::zero(), V::one().add(V::one()));
            }
            diff.div(&two)
        },
        Alignment::End => {
            available.sub(used)
        },
    }
}

///  Execute linear layout: build a parent Node with children laid out along axis.
pub fn linear_layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    spacing: &R,
    alignment: &Alignment,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    axis: &Axis,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == linear_layout::<V>(
            limits.model@, padding.model@, spacing.model(), *alignment,
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@),
            *axis,
        ),
{
    proof { reveal(linear_layout); }
    let ghost spec_sizes: Seq<Size<V>> =
        Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i].model@);

    //  Compute available cross-axis dimension
    let pad_cross = padding.cross_padding_exec(axis);
    let available_cross = limits.max.cross_exec(axis).sub(&pad_cross);

    //  Compute content main: sum of child main dimensions + (n-1) * spacing
    let n = child_sizes.len();
    let mut content_main = spacing.zero_like();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == child_sizes@.len(),
            content_main.wf_spec(),
            content_main.model() == sum_main::<V>(spec_sizes, *axis, i as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j].model@,
        decreases n - i,
    {
        content_main = content_main.add(&child_sizes[i].main_exec(axis));
        i = i + 1;
    }

    //  Add spacing: (n-1) * spacing for n > 0
    if n > 0 {
        let mut sp_total = spacing.zero_like();
        let mut j: usize = 0;
        let n_minus_1 = n - 1;

        while j < n_minus_1
            invariant
                0 <= j <= n_minus_1,
                n_minus_1 == n - 1,
                n > 0,
                sp_total.wf_spec(),
                spacing.wf_spec(),
                sp_total.model() == repeated_add::<V>(spacing.model(), j as nat),
            decreases n_minus_1 - j,
        {
            sp_total = sp_total.add(spacing);
            j = j + 1;
        }

        content_main = content_main.add(&sp_total);
    }

    //  Compute parent size: pad + content for main, max for cross, then resolve
    let pad_main = padding.main_padding_exec(axis);
    let total_main = pad_main.add(&content_main);
    let max_cross = limits.max.cross_exec(axis);
    let parent_size_unclamped = RuntimeSize::from_axes_exec(axis, total_main, max_cross);

    //  Resolve: clamp to limits
    let parent_size = limits.resolve_exec(parent_size_unclamped);

    //  Establish children sequence length
    proof {
        lemma_linear_children_len::<V>(
            padding.model@, spacing.model(), *alignment, spec_sizes, *axis, available_cross.model(), 0,
        );
    }

    //  Build children
    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut main_pos = padding.main_start_exec(axis);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            main_pos.wf_spec(),
            k < n ==> main_pos.model() == child_main_position::<V>(
                padding.model@.main_start(*axis), spec_sizes, *axis, spacing.model(), k as nat),
            available_cross.wf_spec(),
            spacing.wf_spec(),
            padding.wf_spec(),
            children@.len() == k as int,
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j].model@,
            linear_children::<V>(
                padding.model@, spacing.model(), *alignment, spec_sizes, *axis, available_cross.model(), 0,
            ).len() == spec_sizes.len(),
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] children@[j]).wf_spec()
                &&& children@[j].model@ == linear_children::<V>(
                    padding.model@, spacing.model(), *alignment, spec_sizes, *axis, available_cross.model(), 0,
                )[j]
            },
        decreases n - k,
    {
        //  Tell Z3 what linear_children[k] should be
        proof {
            lemma_linear_children_element::<V>(
                padding.model@, spacing.model(), *alignment, spec_sizes, *axis, available_cross.model(), k as nat,
            );
        }

        let child_cross = child_sizes[k].cross_exec(axis);
        let cross_offset = align_offset_exec(alignment, &available_cross, &child_cross);
        let child_cross_pos = padding.cross_start_exec(axis).add(&cross_offset);
        let child_main_pos = main_pos.copy();
        let cs = child_sizes[k].copy_size();

        //  Build node with correct (x, y) based on axis
        let child_node = match axis {
            Axis::Vertical => RuntimeNode::leaf_exec(child_cross_pos, child_main_pos, cs),
            Axis::Horizontal => RuntimeNode::leaf_exec(child_main_pos, child_cross_pos, cs),
        };
        children.push(child_node);

        //  Advance main position
        if k + 1 < n {
            main_pos = main_pos.add(&child_sizes[k].main_exec(axis));
            main_pos = main_pos.add(spacing);
        }

        k = k + 1;
    }

    let x = spacing.zero_like();
    let y = spacing.zero_like();

    let ghost parent_model = linear_layout::<V>(
        limits.model@, padding.model@, spacing.model(), *alignment, spec_sizes, *axis,
    );

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children,
        model: Ghost(parent_model),
    };

    proof {
        //  Help Z3: children match model
        let lc = linear_children::<V>(
            padding.model@, spacing.model(), *alignment, spec_sizes, *axis, available_cross.model(), 0,
        );
        assert(out.model@.children == lc);
        assert(out.children@.len() == out.model@.children.len());
        assert forall|i: int| 0 <= i < out.children@.len() implies {
            &&& (#[trigger] out.children@[i]).wf_shallow()
            &&& out.children@[i].model@ == out.model@.children[i]
        } by {};
    }

    out
}

} //  verus!
