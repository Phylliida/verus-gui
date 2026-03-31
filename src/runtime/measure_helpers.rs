use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::size::Size;
use crate::measure::*;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;

use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

//  ── Content-size helpers per variant ──────────────────────────────

pub fn measure_column_size_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    spacing: &R,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    ghost_sizes: Ghost<Seq<Size<V>>>,
    pad_h: &R,
    pad_v: &R,
) -> (out: RuntimeSize<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        pad_h.wf_spec(),
        pad_v.wf_spec(),
        pad_h@ == padding@.horizontal(),
        pad_v@ == padding@.vertical(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
        ghost_sizes@.len() == child_sizes@.len() as nat,
        forall|i: int| 0 <= i < child_sizes@.len() ==>
            ghost_sizes@[i] == child_sizes@[i]@,
    ensures
        out.wf_spec(),
        out@ == measure_column_result::<V>(
            limits@, padding@, spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut content_height = spacing.zero_like();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            content_height.wf_spec(),
            content_height@ == sum_heights::<V>(spec_sizes, k as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        content_height = content_height.add(&child_sizes[k].height);
        k = k + 1;
    }

    if n > 0 {
        let mut sp = spacing.zero_like();
        let mut j: usize = 0;
        let nm1 = n - 1;

        while j < nm1
            invariant
                0 <= j <= nm1,
                nm1 == n - 1,
                n > 0,
                sp.wf_spec(),
                spacing.wf_spec(),
                sp@ == repeated_add::<V>(spacing@, j as nat),
            decreases nm1 - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }

        content_height = content_height.add(&sp);
    }

    let total_height = pad_v.add(&content_height);
    let total_width = limits.max.width.copy();
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

pub fn measure_row_size_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    spacing: &R,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    ghost_sizes: Ghost<Seq<Size<V>>>,
    pad_h: &R,
    pad_v: &R,
) -> (out: RuntimeSize<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        pad_h.wf_spec(),
        pad_v.wf_spec(),
        pad_h@ == padding@.horizontal(),
        pad_v@ == padding@.vertical(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
        ghost_sizes@.len() == child_sizes@.len() as nat,
        forall|i: int| 0 <= i < child_sizes@.len() ==>
            ghost_sizes@[i] == child_sizes@[i]@,
    ensures
        out.wf_spec(),
        out@ == measure_row_result::<V>(
            limits@, padding@, spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut content_width = spacing.zero_like();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            content_width.wf_spec(),
            content_width@ == sum_widths::<V>(spec_sizes, k as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        content_width = content_width.add(&child_sizes[k].width);
        k = k + 1;
    }

    if n > 0 {
        let mut sp = spacing.zero_like();
        let mut j: usize = 0;
        let nm1 = n - 1;

        while j < nm1
            invariant
                0 <= j <= nm1,
                nm1 == n - 1,
                n > 0,
                sp.wf_spec(),
                spacing.wf_spec(),
                sp@ == repeated_add::<V>(spacing@, j as nat),
            decreases nm1 - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }

        content_width = content_width.add(&sp);
    }

    let total_width = pad_h.add(&content_width);
    let total_height = limits.max.height.copy();
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

pub fn measure_stack_size_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    ghost_sizes: Ghost<Seq<Size<V>>>,
    pad_h: &R,
    pad_v: &R,
) -> (out: RuntimeSize<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        pad_h.wf_spec(),
        pad_v.wf_spec(),
        pad_h@ == padding@.horizontal(),
        pad_v@ == padding@.vertical(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
        ghost_sizes@.len() == child_sizes@.len() as nat,
        forall|i: int| 0 <= i < child_sizes@.len() ==>
            ghost_sizes@[i] == child_sizes@[i]@,
    ensures
        out.wf_spec(),
        out@ == measure_stack_result::<V>(
            limits@, padding@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut max_w = pad_h.zero_like();
    let mut max_h = pad_h.zero_like();
    let mut k: usize = 0;

    proof {
        reveal(max_width);
        reveal(max_height);
    }

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            max_w.wf_spec(),
            max_h.wf_spec(),
            max_w@ == max_width::<V>(spec_sizes, k as nat),
            max_h@ == max_height::<V>(spec_sizes, k as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        proof {
            reveal(max_width);
            reveal(max_height);
        }
        max_w = max_w.max(&child_sizes[k].width);
        max_h = max_h.max(&child_sizes[k].height);
        k = k + 1;
    }

    proof {
        reveal(stack_content_size);
    }

    let total_width = pad_h.add(&max_w);
    let total_height = pad_v.add(&max_h);
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

pub fn measure_wrap_size_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    h_spacing: &R,
    v_spacing: &R,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    ghost_sizes: Ghost<Seq<Size<V>>>,
    pad_h: &R,
    pad_v: &R,
) -> (out: RuntimeSize<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        pad_h.wf_spec(),
        pad_v.wf_spec(),
        pad_h@ == padding@.horizontal(),
        pad_v@ == padding@.vertical(),
        forall|i: int| 0 <= i < child_sizes@.len() ==> child_sizes@[i].wf_spec(),
        ghost_sizes@.len() == child_sizes@.len() as nat,
        forall|i: int| 0 <= i < child_sizes@.len() ==>
            ghost_sizes@[i] == child_sizes@[i]@,
    ensures
        out.wf_spec(),
        out@ == measure_wrap_result::<V>(
            limits@, padding@, h_spacing@, v_spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let available_width = limits.max.width.sub(pad_h);

    let mut cursor_x = h_spacing.zero_like();
    let mut cursor_y = h_spacing.zero_like();
    let mut line_height = h_spacing.zero_like();
    let mut content_width = h_spacing.zero_like();
    let zero = h_spacing.zero_like();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            cursor_x.wf_spec(),
            cursor_y.wf_spec(),
            line_height.wf_spec(),
            content_width.wf_spec(),
            available_width.wf_spec(),
            h_spacing.wf_spec(),
            v_spacing.wf_spec(),
            zero.wf_spec(),
            zero@ == V::zero(),
            ({
                let wc = wrap_cursor(spec_sizes, h_spacing@, v_spacing@, available_width@, k as nat);
                &&& cursor_x@ == wc.x
                &&& cursor_y@ == wc.y
                &&& line_height@ == wc.line_height
                &&& content_width@ == wc.content_width
            }),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        let child_w = child_sizes[k].width.copy();
        let child_h = child_sizes[k].height.copy();

        let at_line_start = cursor_x.le(&zero);
        let would_fit = cursor_x.add(&child_w).le(&available_width);
        let needs_break = !at_line_start && !would_fit;

        if needs_break {
            let new_y = cursor_y.add(&line_height).add(v_spacing);
            cursor_x = child_w.add(h_spacing);
            cursor_y = new_y;
            line_height = child_h;
            content_width = content_width.max(&child_sizes[k].width.copy());
        } else {
            let new_line_w = cursor_x.add(&child_w);
            content_width = content_width.max(&new_line_w);
            cursor_x = new_line_w.add(h_spacing);
            line_height = line_height.max(&child_h);
        }

        k = k + 1;
    }

    let content_size = if n == 0 {
        RuntimeSize::new(h_spacing.zero_like(), h_spacing.zero_like())
    } else {
        RuntimeSize::new(content_width, cursor_y.add(&line_height))
    };

    let total_width = pad_h.add(&content_size.width);
    let total_height = pad_v.add(&content_size.height);
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

} //  verus!
