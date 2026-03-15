use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::widget::{RuntimeWidget, RuntimeAbsoluteChild, ContainerKind};
use crate::runtime::grid::{grid_content_width_exec, grid_content_height_exec};
use crate::size::Size;
use crate::limits::Limits;
use verus_algebra::traits::field::Field;
use crate::widget::Widget;
use crate::widget::AbsoluteChild;
use crate::measure::*;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;
use crate::layout::grid::*;
use crate::layout::absolute::*;

verus! {

/// Recursively measure a RuntimeWidget tree, returning its preferred size.
pub fn measure_widget_exec(
    limits: &RuntimeLimits,
    widget: &RuntimeWidget,
    fuel: usize,
) -> (out: RuntimeSize)
    requires
        limits.wf_spec(),
        widget.wf_spec(fuel as nat),
    ensures
        out.wf_spec(),
        out@ == measure_widget::<RationalModel>(limits@, widget.model(), fuel as nat),
    decreases fuel, 1nat,
{
    if fuel == 0 {
        // Unreachable: wf_spec(0) is false
        RuntimeSize::zero_exec()
    } else {
        match widget {
            RuntimeWidget::Leaf { size, model } => {
                limits.resolve_exec(size.copy_size())
            },
            RuntimeWidget::Column { padding, spacing, alignment, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let dummy_sp = RuntimeRational::from_int(0);
                measure_container_exec(limits, padding, spacing, &dummy_sp,
                    children, fuel, ContainerKind::Column)
            },
            RuntimeWidget::Row { padding, spacing, alignment, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let dummy_sp = RuntimeRational::from_int(0);
                measure_container_exec(limits, padding, spacing, &dummy_sp,
                    children, fuel, ContainerKind::Row)
            },
            RuntimeWidget::Stack { padding, h_align, v_align, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let dummy_sp1 = RuntimeRational::from_int(0);
                let dummy_sp2 = RuntimeRational::from_int(0);
                measure_container_exec(limits, padding, &dummy_sp1, &dummy_sp2,
                    children, fuel, ContainerKind::Stack)
            },
            RuntimeWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                measure_container_exec(limits, padding, h_spacing, v_spacing,
                    children, fuel, ContainerKind::Wrap)
            },
            RuntimeWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                // Flex fills limits.max regardless of children
                limits.resolve_exec(limits.max.copy_size())
            },
            RuntimeWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                  col_widths, row_heights, children, model } => {
                let pad_h = padding.horizontal_exec();
                let pad_v = padding.vertical_exec();
                let content_w = grid_content_width_exec(col_widths, h_spacing);
                let content_h = grid_content_height_exec(row_heights, v_spacing);
                let tw = pad_h.add(&content_w);
                let th = pad_v.add(&content_h);
                limits.resolve_exec(RuntimeSize::new(tw, th))
            },
            RuntimeWidget::Absolute { padding, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                measure_absolute_exec(limits, padding, children, fuel)
            },
            RuntimeWidget::Margin { margin, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let pad_h = margin.horizontal_exec();
                let pad_v = margin.vertical_exec();
                let inner = limits.shrink_exec(&pad_h, &pad_v);
                let child_size = measure_widget_exec(&inner, child, fuel - 1);
                let pad_h2 = margin.horizontal_exec();
                let pad_v2 = margin.vertical_exec();
                let tw = pad_h2.add(&child_size.width);
                let th = pad_v2.add(&child_size.height);
                limits.resolve_exec(RuntimeSize::new(tw, th))
            },
            RuntimeWidget::Conditional { visible, child, model } => {
                if *visible {
                    proof {
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                        assert(child.wf_spec((fuel - 1) as nat)) by {
                            assert(child.wf_spec((fuel as nat - 1) as nat));
                        }
                    }
                    let child_size = measure_widget_exec(limits, child, fuel - 1);
                    limits.resolve_exec(child_size)
                } else {
                    limits.resolve_exec(RuntimeSize::zero_exec())
                }
            },
            RuntimeWidget::SizedBox { inner_limits: il, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let effective = limits.intersect_exec(il);
                let child_size = measure_widget_exec(&effective, child, fuel - 1);
                limits.resolve_exec(child_size)
            },
            RuntimeWidget::AspectRatio { ratio, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let w1 = copy_rational(&limits.max.width);
                let h1 = w1.div(ratio);
                let child_size = if h1.le(&limits.max.height) {
                    let eff_max = RuntimeSize::new(
                        copy_rational(&limits.max.width), h1);
                    let eff = RuntimeLimits {
                        min: limits.min.copy_size(),
                        max: eff_max,
                        model: Ghost(Limits {
                            min: limits@.min,
                            max: Size::new(limits@.max.width, limits@.max.width.div(ratio@)),
                        }),
                    };
                    measure_widget_exec(&eff, child, fuel - 1)
                } else {
                    let h2 = copy_rational(&limits.max.height);
                    let w2 = h2.mul(ratio);
                    let eff_max = RuntimeSize::new(w2, copy_rational(&limits.max.height));
                    let eff = RuntimeLimits {
                        min: limits.min.copy_size(),
                        max: eff_max,
                        model: Ghost(Limits {
                            min: limits@.min,
                            max: Size::new(limits@.max.height.mul_spec(ratio@), limits@.max.height),
                        }),
                    };
                    measure_widget_exec(&eff, child, fuel - 1)
                };
                limits.resolve_exec(child_size)
            },
            RuntimeWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                // measure = limits.resolve(viewport), child doesn't affect output
                limits.resolve_exec(viewport.copy_size())
            },
            RuntimeWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                // measure = limits.resolve(viewport), children don't affect output
                limits.resolve_exec(viewport.copy_size())
            },
            RuntimeWidget::TextInput { preferred_size, text_input_id, config, model } => {
                limits.resolve_exec(preferred_size.copy_size())
            },
        }
    }
}

/// Shared container measure: recursively measure children, compute content size, resolve.
fn measure_container_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing1: &RuntimeRational,
    spacing2: &RuntimeRational,
    children: &Vec<RuntimeWidget>,
    fuel: usize,
    kind: ContainerKind,
) -> (out: RuntimeSize)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing1.wf_spec(),
        spacing2.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let inner = limits@.shrink(padding@.horizontal(), padding@.vertical());
            let spec_wc = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let cs = measure_children(inner, spec_wc, (fuel - 1) as nat);
            match kind {
                ContainerKind::Column =>
                    measure_column_result::<RationalModel>(limits@, padding@, spacing1@, cs),
                ContainerKind::Row =>
                    measure_row_result::<RationalModel>(limits@, padding@, spacing1@, cs),
                ContainerKind::Stack =>
                    measure_stack_result::<RationalModel>(limits@, padding@, cs),
                ContainerKind::Wrap =>
                    measure_wrap_result::<RationalModel>(limits@, padding@, spacing1@, spacing2@, cs),
            }
        }),
    decreases fuel, 0nat,
{
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);

    let n = children.len();

    // Ghost: spec-level children sequence
    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |j: int| children@[j].model());
    let ghost spec_cs = measure_children(inner@, spec_wc, (fuel - 1) as nat);

    // 1. Recursively measure children
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_wc.len() == n as nat,
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] children@[j]).model(),
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_sizes@.len() == i as int,
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == measure_widget::<RationalModel>(
                        inner@, spec_wc[j], (fuel - 1) as nat)
            },
        decreases n - i,
    {
        let cs = measure_widget_exec(&inner, &children[i], fuel - 1);
        child_sizes.push(cs);
        i = i + 1;
    }

    // Ghost: child_sizes_seq matches spec measure_children
    let ghost child_sizes_seq: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);

    proof {
        assert(child_sizes_seq.len() == spec_cs.len());
        assert forall|j: int| 0 <= j < child_sizes_seq.len() implies
            child_sizes_seq[j] == spec_cs[j]
        by {}
        assert(child_sizes_seq =~= spec_cs);
    }

    // 2. Compute content size and resolve per variant
    match kind {
        ContainerKind::Column => {
            measure_column_size_exec(limits, padding, spacing1, &child_sizes,
                Ghost(child_sizes_seq), &pad_h, &pad_v)
        },
        ContainerKind::Row => {
            measure_row_size_exec(limits, padding, spacing1, &child_sizes,
                Ghost(child_sizes_seq), &pad_h, &pad_v)
        },
        ContainerKind::Stack => {
            measure_stack_size_exec(limits, padding, &child_sizes,
                Ghost(child_sizes_seq), &pad_h, &pad_v)
        },
        ContainerKind::Wrap => {
            measure_wrap_size_exec(limits, padding, spacing1, spacing2, &child_sizes,
                Ghost(child_sizes_seq), &pad_h, &pad_v)
        },
    }
}

/// Measure an absolute widget: recursively measure children, compute bounding box, resolve.
fn measure_absolute_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    children: &Vec<RuntimeAbsoluteChild>,
    fuel: usize,
) -> (out: RuntimeSize)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==> children@[i].x.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==> children@[i].y.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_ac = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let inner = limits@.shrink(padding@.horizontal(), padding@.vertical());
            let cs = measure_absolute_children(inner, spec_ac, (fuel - 1) as nat);
            measure_absolute_result::<RationalModel>(limits@, padding@, spec_ac, cs)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_ac: Seq<AbsoluteChild<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    // Measure children
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_ac.len() == n as nat,
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_sizes@.len() == i as int,
            forall|j: int| 0 <= j < n ==>
                spec_ac[j] == (#[trigger] children@[j]).model(),
            forall|j: int| 0 <= j < children@.len() ==> children@[j].x.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==> children@[j].y.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == measure_widget::<RationalModel>(
                        inner@, spec_ac[j].child, (fuel - 1) as nat)
            },
        decreases n - i,
    {
        let cs = measure_widget_exec(&inner, &children[i].child, fuel - 1);
        child_sizes.push(cs);
        i = i + 1;
    }

    let ghost child_sizes_seq: Seq<Size<RationalModel>> =
        Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
    let ghost spec_cs = measure_absolute_children(inner@, spec_ac, (fuel - 1) as nat);

    proof {
        assert(child_sizes_seq.len() == spec_cs.len());
        assert forall|j: int| 0 <= j < child_sizes_seq.len() implies
            child_sizes_seq[j] == spec_cs[j]
        by {}
        assert(child_sizes_seq =~= spec_cs);
    }

    // Compute bounding box
    let mut max_right = RuntimeRational::from_int(0);
    let mut max_bottom = RuntimeRational::from_int(0);

    let ghost spec_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)> =
        Seq::new(n as nat, |i: int| (spec_ac[i].x, spec_ac[i].y, child_sizes_seq[i]));

    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == children@.len(),
            n == children@.len(),
            n == child_sizes@.len(),
            max_right.wf_spec(),
            max_bottom.wf_spec(),
            max_right@ == absolute_max_right::<RationalModel>(spec_data, k as nat),
            max_bottom@ == absolute_max_bottom::<RationalModel>(spec_data, k as nat),
            forall|j: int| 0 <= j < n ==> (#[trigger] children@[j]).x.wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] children@[j]).y.wf_spec(),
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> spec_data[j] ==
                (spec_ac[j].x, spec_ac[j].y, child_sizes_seq[j]),
            forall|j: int| 0 <= j < n ==> spec_ac[j] == children@[j].model(),
            child_sizes_seq.len() == n as nat,
            forall|j: int| 0 <= j < n ==> child_sizes_seq[j] == child_sizes@[j]@,
        decreases n - k,
    {
        assert(children@[k as int].x.wf_spec());
        assert(children@[k as int].y.wf_spec());
        assert(child_sizes@[k as int].wf_spec());
        let right = children[k].x.add(&child_sizes[k].width);
        let bottom = children[k].y.add(&child_sizes[k].height);
        max_right = max_right.max(&right);
        max_bottom = max_bottom.max(&bottom);
        k = k + 1;
    }

    let pad_h2 = padding.horizontal_exec();
    let pad_v2 = padding.vertical_exec();
    let tw = pad_h2.add(&max_right);
    let th = pad_v2.add(&max_bottom);
    limits.resolve_exec(RuntimeSize::new(tw, th))
}

// ── Content-size helpers per variant ──────────────────────────────

fn measure_column_size_exec(
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

fn measure_row_size_exec(
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

fn measure_stack_size_exec(
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

fn measure_wrap_size_exec(
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
