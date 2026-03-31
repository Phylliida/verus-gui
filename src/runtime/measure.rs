use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::widget::{RuntimeWidget, RuntimeLeafWidget, RuntimeWrapperWidget, RuntimeContainerWidget, RuntimeAbsoluteChild};
use crate::runtime::widget::ContainerKind;
use crate::layout::Axis;
use crate::runtime::grid::{grid_content_width_exec, grid_content_height_exec};
use crate::runtime::measure_helpers::*;
use crate::size::Size;
use crate::limits::Limits;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;
use crate::widget::Widget;
use crate::widget::AbsoluteChild;
use crate::measure::*;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;
use crate::layout::grid::*;
use crate::layout::absolute::*;

verus! {

///  Recursively measure a RuntimeWidget tree, returning its preferred size.
pub fn measure_widget_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    widget: &RuntimeWidget<R, V>,
    fuel: usize,
) -> (out: RuntimeSize<R, V>)
    requires
        limits.wf_spec(),
        widget.wf_spec(fuel as nat),
    ensures
        out.wf_spec(),
        out@ == measure_widget::<V>(limits@, widget.model(), fuel as nat),
    decreases fuel, 1nat,
{
    proof { reveal(measure_widget); }
    if fuel == 0 {
        //  Unreachable: wf_spec(0) is false
        RuntimeSize::new(limits.min.width.zero_like(), limits.min.width.zero_like())
    } else {
        //  Fuel bridge: one proof for all variants
        proof { assert((fuel as nat - 1) as nat == (fuel - 1) as nat); }

        match widget {
            RuntimeWidget::Leaf(leaf) => {
                match leaf {
                    RuntimeLeafWidget::Leaf { size, model } => {
                        limits.resolve_exec(size.copy_size())
                    },
                    RuntimeLeafWidget::TextInput { preferred_size, text_input_id, config, model } => {
                        limits.resolve_exec(preferred_size.copy_size())
                    },
                }
            },
            RuntimeWidget::Wrapper(wrapper) => {
                match wrapper {
                    RuntimeWrapperWidget::Margin { margin, child, model } => {
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
                    RuntimeWrapperWidget::Conditional { visible, child, model } => {
                        if *visible {
                            let child_size = measure_widget_exec(limits, child, fuel - 1);
                            limits.resolve_exec(child_size)
                        } else {
                            limits.resolve_exec(RuntimeSize::new(limits.min.width.zero_like(), limits.min.width.zero_like()))
                        }
                    },
                    RuntimeWrapperWidget::SizedBox { inner_limits: il, child, model } => {
                        let effective = limits.intersect_exec(il);
                        let child_size = measure_widget_exec(&effective, child, fuel - 1);
                        limits.resolve_exec(child_size)
                    },
                    RuntimeWrapperWidget::AspectRatio { ratio, child, model } => {
                        let w1 = limits.max.width.copy();
                        let h1 = w1.div(ratio);
                        let child_size = if h1.le(&limits.max.height) {
                            let eff_max = RuntimeSize::new(
                                limits.max.width.copy(), h1);
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
                            let h2 = limits.max.height.copy();
                            let w2 = h2.mul(ratio);
                            let eff_max = RuntimeSize::new(w2, limits.max.height.copy());
                            let eff = RuntimeLimits {
                                min: limits.min.copy_size(),
                                max: eff_max,
                                model: Ghost(Limits {
                                    min: limits@.min,
                                    max: Size::new(limits@.max.height.mul(ratio@), limits@.max.height),
                                }),
                            };
                            measure_widget_exec(&eff, child, fuel - 1)
                        };
                        limits.resolve_exec(child_size)
                    },
                    RuntimeWrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                        //  measure = limits.resolve(viewport), child doesn't affect output
                        limits.resolve_exec(viewport.copy_size())
                    },
                }
            },
            RuntimeWidget::Container(container) => {
                match container {
                    RuntimeContainerWidget::Column { padding, spacing, alignment, children, model } => {
                        let dummy_sp = limits.min.width.zero_like();
                        measure_container_exec(limits, padding, spacing, &dummy_sp,
                            children, fuel, ContainerKind::Linear(Axis::Vertical))
                    },
                    RuntimeContainerWidget::Row { padding, spacing, alignment, children, model } => {
                        let dummy_sp = limits.min.width.zero_like();
                        measure_container_exec(limits, padding, spacing, &dummy_sp,
                            children, fuel, ContainerKind::Linear(Axis::Horizontal))
                    },
                    RuntimeContainerWidget::Stack { padding, h_align, v_align, children, model } => {
                        let dummy_sp1 = limits.min.width.zero_like();
                        let dummy_sp2 = limits.min.width.zero_like();
                        measure_container_exec(limits, padding, &dummy_sp1, &dummy_sp2,
                            children, fuel, ContainerKind::Stack)
                    },
                    RuntimeContainerWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                        measure_container_exec(limits, padding, h_spacing, v_spacing,
                            children, fuel, ContainerKind::Wrap)
                    },
                    RuntimeContainerWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                        //  Flex fills limits.max regardless of children
                        limits.resolve_exec(limits.max.copy_size())
                    },
                    RuntimeContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                                   col_widths, row_heights, children, model } => {
                        let pad_h = padding.horizontal_exec();
                        let pad_v = padding.vertical_exec();
                        let content_w = grid_content_width_exec(col_widths, h_spacing);
                        let content_h = grid_content_height_exec(row_heights, v_spacing);
                        let tw = pad_h.add(&content_w);
                        let th = pad_v.add(&content_h);
                        limits.resolve_exec(RuntimeSize::new(tw, th))
                    },
                    RuntimeContainerWidget::Absolute { padding, children, model } => {
                        measure_absolute_exec(limits, padding, children, fuel)
                    },
                    RuntimeContainerWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                        //  measure = limits.resolve(viewport), children don't affect output
                        limits.resolve_exec(viewport.copy_size())
                    },
                }
            },
        }
    }
}

///  Shared container measure: recursively measure children, compute content size, resolve.
fn measure_container_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    spacing1: &R,
    spacing2: &R,
    children: &Vec<RuntimeWidget<R, V>>,
    fuel: usize,
    kind: ContainerKind,
) -> (out: RuntimeSize<R, V>)
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
                ContainerKind::Linear(Axis::Vertical) =>
                    measure_column_result::<V>(limits@, padding@, spacing1@, cs),
                ContainerKind::Linear(Axis::Horizontal) =>
                    measure_row_result::<V>(limits@, padding@, spacing1@, cs),
                ContainerKind::Stack =>
                    measure_stack_result::<V>(limits@, padding@, cs),
                ContainerKind::Wrap =>
                    measure_wrap_result::<V>(limits@, padding@, spacing1@, spacing2@, cs),
            }
        }),
    decreases fuel, 0nat,
{
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);

    let n = children.len();

    //  Ghost: spec-level children sequence
    let ghost spec_wc: Seq<Widget<V>> =
        Seq::new(children@.len() as nat, |j: int| children@[j].model());
    let ghost spec_cs = measure_children(inner@, spec_wc, (fuel - 1) as nat);

    //  1. Recursively measure children
    let mut child_sizes: Vec<RuntimeSize<R, V>> = Vec::new();
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
                &&& child_sizes@[j]@ == measure_widget::<V>(
                        inner@, spec_wc[j], (fuel - 1) as nat)
            },
        decreases n - i,
    {
        let cs = measure_widget_exec(&inner, &children[i], fuel - 1);
        child_sizes.push(cs);
        i = i + 1;
    }

    //  Ghost: child_sizes_seq matches spec measure_children
    let ghost child_sizes_seq: Seq<Size<V>> =
        Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);

    proof {
        reveal(measure_widget);
        assert(child_sizes_seq.len() == spec_cs.len());
        assert forall|j: int| 0 <= j < child_sizes_seq.len() implies
            child_sizes_seq[j] == spec_cs[j]
        by {
            reveal(measure_widget);
        }
        assert(child_sizes_seq =~= spec_cs);
    }

    //  2. Compute content size and resolve per variant
    match kind {
        ContainerKind::Linear(Axis::Vertical) => {
            measure_column_size_exec(limits, padding, spacing1, &child_sizes,
                Ghost(child_sizes_seq), &pad_h, &pad_v)
        },
        ContainerKind::Linear(Axis::Horizontal) => {
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

///  Measure an absolute widget: recursively measure children, compute bounding box, resolve.
fn measure_absolute_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    children: &Vec<RuntimeAbsoluteChild<R, V>>,
    fuel: usize,
) -> (out: RuntimeSize<R, V>)
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
            measure_absolute_result::<V>(limits@, padding@, spec_ac, cs)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_ac: Seq<AbsoluteChild<V>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    //  Measure children
    let mut child_sizes: Vec<RuntimeSize<R, V>> = Vec::new();
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
                &&& child_sizes@[j]@ == measure_widget::<V>(
                        inner@, spec_ac[j].child, (fuel - 1) as nat)
            },
        decreases n - i,
    {
        let cs = measure_widget_exec(&inner, &children[i].child, fuel - 1);
        child_sizes.push(cs);
        i = i + 1;
    }

    let ghost child_sizes_seq: Seq<Size<V>> =
        Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
    let ghost spec_cs = measure_absolute_children(inner@, spec_ac, (fuel - 1) as nat);

    proof {
        reveal(measure_widget);
        assert(child_sizes_seq =~= spec_cs);
    }

    //  Compute bounding box
    let mut max_right = padding.left.zero_like();
    let mut max_bottom = padding.left.zero_like();

    let ghost spec_data: Seq<(V, V, Size<V>)> =
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
            max_right@ == absolute_max_right::<V>(spec_data, k as nat),
            max_bottom@ == absolute_max_bottom::<V>(spec_data, k as nat),
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

} //  verus!
