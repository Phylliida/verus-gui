use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::size::Size;
use crate::measure::*;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;

verus! {

// ── Content-size helpers per variant ──────────────────────────────

pub fn measure_column_size_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    child_sizes: &Vec<RuntimeSize>,
    ghost_sizes: Ghost<Seq<Size<RationalModel>>>,
    pad_h: &RuntimeRational,
    pad_v: &RuntimeRational,
) -> (out: RuntimeSize)
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
        out@ == measure_column_result::<RationalModel>(
            limits@, padding@, spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut content_height = RuntimeRational::from_int(0);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            content_height.wf_spec(),
            content_height@ == sum_heights::<RationalModel>(spec_sizes, k as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        content_height = content_height.add(&child_sizes[k].height);
        k = k + 1;
    }

    if n > 0 {
        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        let nm1 = n - 1;

        while j < nm1
            invariant
                0 <= j <= nm1,
                nm1 == n - 1,
                n > 0,
                sp.wf_spec(),
                spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases nm1 - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }

        content_height = content_height.add(&sp);
    }

    let total_height = pad_v.add(&content_height);
    let total_width = copy_rational(&limits.max.width);
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

pub fn measure_row_size_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    child_sizes: &Vec<RuntimeSize>,
    ghost_sizes: Ghost<Seq<Size<RationalModel>>>,
    pad_h: &RuntimeRational,
    pad_v: &RuntimeRational,
) -> (out: RuntimeSize)
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
        out@ == measure_row_result::<RationalModel>(
            limits@, padding@, spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut content_width = RuntimeRational::from_int(0);
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == child_sizes@.len(),
            content_width.wf_spec(),
            content_width@ == sum_widths::<RationalModel>(spec_sizes, k as nat),
            forall|j: int| 0 <= j < child_sizes@.len() ==> child_sizes@[j].wf_spec(),
            forall|j: int| 0 <= j < child_sizes@.len() ==> spec_sizes[j] == child_sizes@[j]@,
        decreases n - k,
    {
        content_width = content_width.add(&child_sizes[k].width);
        k = k + 1;
    }

    if n > 0 {
        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        let nm1 = n - 1;

        while j < nm1
            invariant
                0 <= j <= nm1,
                nm1 == n - 1,
                n > 0,
                sp.wf_spec(),
                spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases nm1 - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }

        content_width = content_width.add(&sp);
    }

    let total_width = pad_h.add(&content_width);
    let total_height = copy_rational(&limits.max.height);
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

pub fn measure_stack_size_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    child_sizes: &Vec<RuntimeSize>,
    ghost_sizes: Ghost<Seq<Size<RationalModel>>>,
    pad_h: &RuntimeRational,
    pad_v: &RuntimeRational,
) -> (out: RuntimeSize)
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
        out@ == measure_stack_result::<RationalModel>(
            limits@, padding@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let mut max_w = RuntimeRational::from_int(0);
    let mut max_h = RuntimeRational::from_int(0);
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
            max_w@ == max_width::<RationalModel>(spec_sizes, k as nat),
            max_h@ == max_height::<RationalModel>(spec_sizes, k as nat),
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

pub fn measure_wrap_size_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_spacing: &RuntimeRational,
    v_spacing: &RuntimeRational,
    child_sizes: &Vec<RuntimeSize>,
    ghost_sizes: Ghost<Seq<Size<RationalModel>>>,
    pad_h: &RuntimeRational,
    pad_v: &RuntimeRational,
) -> (out: RuntimeSize)
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
        out@ == measure_wrap_result::<RationalModel>(
            limits@, padding@, h_spacing@, v_spacing@, ghost_sizes@),
{
    let ghost spec_sizes = ghost_sizes@;
    let n = child_sizes.len();

    let available_width = limits.max.width.sub(pad_h);

    let mut cursor_x = RuntimeRational::from_int(0);
    let mut cursor_y = RuntimeRational::from_int(0);
    let mut line_height = RuntimeRational::from_int(0);
    let mut content_width = RuntimeRational::from_int(0);
    let zero = RuntimeRational::from_int(0);
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
            zero@ == RationalModel::from_int_spec(0),
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
        let child_w = copy_rational(&child_sizes[k].width);
        let child_h = copy_rational(&child_sizes[k].height);

        let at_line_start = cursor_x.le(&zero);
        let would_fit = cursor_x.add(&child_w).le(&available_width);
        let needs_break = !at_line_start && !would_fit;

        if needs_break {
            let new_y = cursor_y.add(&line_height).add(v_spacing);
            cursor_x = child_w.add(h_spacing);
            cursor_y = new_y;
            line_height = child_h;
            content_width = content_width.max(&copy_rational(&child_sizes[k].width));
        } else {
            let new_line_w = cursor_x.add(&child_w);
            content_width = content_width.max(&new_line_w);
            cursor_x = new_line_w.add(h_spacing);
            line_height = line_height.max(&child_h);
        }

        k = k + 1;
    }

    let content_size = if n == 0 {
        RuntimeSize::zero_exec()
    } else {
        RuntimeSize::new(content_width, cursor_y.add(&line_height))
    };

    let total_width = pad_h.add(&content_size.width);
    let total_height = pad_v.add(&content_size.height);
    limits.resolve_exec(RuntimeSize::new(total_width, total_height))
}

} // verus!
