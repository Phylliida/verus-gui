use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_rational::RuntimeRational;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::partial_order::PartialOrder;
use verus_algebra::traits::ring::Ring;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::column::*;
use crate::runtime::row::*;
use crate::runtime::stack::*;
use crate::runtime::wrap::*;
use crate::runtime::flex::*;
use crate::runtime::grid::*;
use crate::runtime::absolute::*;
use crate::layout::absolute::*;
use crate::layout::absolute_proofs::*;
use crate::layout::listview::*;
use crate::runtime::listview::*;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::alignment::Alignment;
use crate::widget::*;
use crate::layout::*;
use crate::layout::proofs::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;
use crate::layout::wrap_proofs::*;
use crate::layout::flex::*;
use crate::layout::flex_proofs::*;
use crate::layout::grid::*;
use crate::layout::grid_proofs::*;
use crate::runtime::widget_sized_box::layout_sized_box_widget_exec;

verus! {

/// Runtime flex child: weight + child widget.
pub struct RuntimeFlexItem {
    pub weight: RuntimeRational,
    pub child: RuntimeWidget,
}

/// Runtime absolute child: explicit (x, y) offset + child widget.
pub struct RuntimeAbsoluteChild {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub child: RuntimeWidget,
}

/// Runtime Widget tree mirroring the spec Widget enum.
pub enum RuntimeWidget {
    Leaf {
        size: RuntimeSize,
        model: Ghost<Widget<RationalModel>>,
    },
    Column {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Row {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Stack {
        padding: RuntimePadding,
        h_align: Alignment,
        v_align: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Wrap {
        padding: RuntimePadding,
        h_spacing: RuntimeRational,
        v_spacing: RuntimeRational,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Flex {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        direction: FlexDirection,
        children: Vec<RuntimeFlexItem>,
        model: Ghost<Widget<RationalModel>>,
    },
    Grid {
        padding: RuntimePadding,
        h_spacing: RuntimeRational,
        v_spacing: RuntimeRational,
        h_align: Alignment,
        v_align: Alignment,
        col_widths: Vec<RuntimeSize>,
        row_heights: Vec<RuntimeSize>,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Absolute {
        padding: RuntimePadding,
        children: Vec<RuntimeAbsoluteChild>,
        model: Ghost<Widget<RationalModel>>,
    },
    Margin {
        margin: RuntimePadding,
        child: Box<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Conditional {
        visible: bool,
        child: Box<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    SizedBox {
        inner_limits: RuntimeLimits,
        child: Box<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    AspectRatio {
        ratio: RuntimeRational,
        child: Box<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    ScrollView {
        viewport: RuntimeSize,
        scroll_x: RuntimeRational,
        scroll_y: RuntimeRational,
        child: Box<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    ListView {
        spacing: RuntimeRational,
        scroll_y: RuntimeRational,
        viewport: RuntimeSize,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
}

impl RuntimeFlexItem {
    pub open spec fn model(&self) -> FlexItem<RationalModel> {
        FlexItem { weight: self.weight@, child: self.child.model() }
    }
}

impl RuntimeAbsoluteChild {
    pub open spec fn model(&self) -> AbsoluteChild<RationalModel> {
        AbsoluteChild { x: self.x@, y: self.y@, child: self.child.model() }
    }
}

impl RuntimeWidget {
    /// Extract the ghost model.
    pub open spec fn model(&self) -> Widget<RationalModel> {
        match self {
            RuntimeWidget::Leaf { model, .. } => model@,
            RuntimeWidget::Column { model, .. } => model@,
            RuntimeWidget::Row { model, .. } => model@,
            RuntimeWidget::Stack { model, .. } => model@,
            RuntimeWidget::Wrap { model, .. } => model@,
            RuntimeWidget::Flex { model, .. } => model@,
            RuntimeWidget::Grid { model, .. } => model@,
            RuntimeWidget::Absolute { model, .. } => model@,
            RuntimeWidget::Margin { model, .. } => model@,
            RuntimeWidget::Conditional { model, .. } => model@,
            RuntimeWidget::SizedBox { model, .. } => model@,
            RuntimeWidget::AspectRatio { model, .. } => model@,
            RuntimeWidget::ScrollView { model, .. } => model@,
            RuntimeWidget::ListView { model, .. } => model@,
        }
    }

    /// Shallow well-formedness: direct fields match model, no recursive child check.
    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeWidget::Leaf { size, model } => {
                &&& size.wf_spec()
                &&& model@ == Widget::Leaf { size: size@ }
            },
            RuntimeWidget::Column { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == Widget::Column {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Row { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == Widget::Row {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Stack { padding, h_align, v_align, children, model } => {
                &&& padding.wf_spec()
                &&& model@ == Widget::Stack {
                    padding: padding@,
                    h_align: *h_align,
                    v_align: *v_align,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                &&& padding.wf_spec()
                &&& h_spacing.wf_spec()
                &&& v_spacing.wf_spec()
                &&& model@ == Widget::Wrap {
                    padding: padding@,
                    h_spacing: h_spacing@,
                    v_spacing: v_spacing@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].weight.wf_spec()
                &&& children@.len() > 0 ==> !sum_weights::<RationalModel>(
                    Seq::new(children@.len() as nat, |i: int| children@[i].weight@),
                    children@.len() as nat,
                ).eqv_spec(RationalModel::from_int_spec(0))
                &&& model@ == Widget::Flex {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    direction: *direction,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                  col_widths, row_heights, children, model } => {
                &&& padding.wf_spec()
                &&& h_spacing.wf_spec()
                &&& v_spacing.wf_spec()
                &&& forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec()
                &&& forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec()
                &&& children@.len() == col_widths@.len() * row_heights@.len()
                &&& model@ == Widget::Grid {
                    padding: padding@,
                    h_spacing: h_spacing@,
                    v_spacing: v_spacing@,
                    h_align: *h_align,
                    v_align: *v_align,
                    col_widths: Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@),
                    row_heights: Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@),
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Absolute { padding, children, model } => {
                &&& padding.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].x.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].y.wf_spec()
                &&& model@ == Widget::Absolute {
                    padding: padding@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Margin { margin, child, model } => {
                &&& margin.wf_spec()
                &&& model@ == Widget::Margin {
                    margin: margin@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWidget::Conditional { visible, child, model } => {
                model@ == Widget::Conditional {
                    visible: *visible,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWidget::SizedBox { inner_limits, child, model } => {
                &&& inner_limits.wf_spec()
                &&& model@ == Widget::SizedBox {
                    inner_limits: inner_limits@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWidget::AspectRatio { ratio, child, model } => {
                &&& ratio.wf_spec()
                &&& !ratio@.eqv_spec(RationalModel::from_int_spec(0))
                &&& model@ == Widget::AspectRatio {
                    ratio: ratio@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                &&& viewport.wf_spec()
                &&& scroll_x.wf_spec()
                &&& scroll_y.wf_spec()
                &&& model@ == Widget::ScrollView {
                    viewport: viewport@,
                    scroll_x: scroll_x@,
                    scroll_y: scroll_y@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                &&& spacing.wf_spec()
                &&& scroll_y.wf_spec()
                &&& viewport.wf_spec()
                &&& model@ == Widget::ListView {
                    spacing: spacing@,
                    scroll_y: scroll_y@,
                    viewport: viewport@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
        }
    }

    /// Full well-formedness at a given fuel depth.
    pub open spec fn wf_spec(&self, fuel: nat) -> bool
        decreases fuel,
    {
        if fuel == 0 {
            false
        } else {
            &&& self.wf_shallow()
            &&& match self {
                RuntimeWidget::Leaf { .. } => true,
                RuntimeWidget::Column { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Row { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Stack { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Wrap { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Flex { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Grid { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Absolute { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Margin { child, .. } => {
                    child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Conditional { child, .. } => {
                    child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::SizedBox { child, .. } => {
                    child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::AspectRatio { child, .. } => {
                    child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::ScrollView { child, .. } => {
                    child.wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::ListView { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
            }
        }
    }
}

// ── Conditional widget helper ────────────────────────────────────

/// Layout a conditional widget: visible child or zero-sized leaf.
fn layout_conditional_exec(
    limits: &RuntimeLimits,
    visible: bool,
    child: &Box<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == layout_widget::<RationalModel>(
            limits@,
            Widget::Conditional { visible, child: Box::new(child.model()) },
            fuel as nat,
        ),
    decreases fuel, 0nat,
{
    if visible {
        let child_node = layout_widget_exec(limits, child, fuel - 1);
        let resolved = limits.resolve_exec(child_node.size.copy_size());
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let ghost parent_model = layout_widget::<RationalModel>(
            limits@,
            Widget::Conditional { visible: true, child: Box::new(child.model()) },
            fuel as nat,
        );
        RuntimeNode {
            x,
            y,
            size: resolved,
            children: child_node.children,
            model: Ghost(parent_model),
        }
    } else {
        let resolved = limits.resolve_exec(RuntimeSize::zero_exec());
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        RuntimeNode::leaf_exec(x, y, resolved)
    }
}

// ── Layout widget exec ───────────────────────────────────────────

/// Recursively lay out a RuntimeWidget tree.
pub fn layout_widget_exec(
    limits: &RuntimeLimits,
    widget: &RuntimeWidget,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        widget.wf_spec(fuel as nat),
    ensures
        out.wf_spec(),
        out@ == layout_widget::<RationalModel>(limits@, widget.model(), fuel as nat),
    decreases fuel, 1nat,
{
    if fuel == 0 {
        // Unreachable: wf_spec(0) is false
        let z1 = RuntimeRational::from_int(0);
        let z2 = RuntimeRational::from_int(0);
        RuntimeNode::leaf_exec(z1, z2, RuntimeSize::zero_exec())
    } else {
        match widget {
            RuntimeWidget::Leaf { size, model } => {
                let resolved = limits.resolve_exec(size.copy_size());
                let x = RuntimeRational::from_int(0);
                let y = RuntimeRational::from_int(0);
                RuntimeNode::leaf_exec(x, y, resolved)
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
                layout_container_exec(limits, padding, spacing, &Alignment::Start,
                    alignment, &dummy_sp, children, fuel, ContainerKind::Column)
            },
            RuntimeWidget::Row { padding, spacing, alignment, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                let dummy_sp = RuntimeRational::from_int(0);
                layout_container_exec(limits, padding, spacing, alignment,
                    &Alignment::Start, &dummy_sp, children, fuel, ContainerKind::Row)
            },
            RuntimeWidget::Stack { padding, h_align, v_align, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                let zero_sp = RuntimeRational::from_int(0);
                let dummy_sp = RuntimeRational::from_int(0);
                layout_container_exec(limits, padding, &zero_sp, h_align,
                    v_align, &dummy_sp, children, fuel, ContainerKind::Stack)
            },
            RuntimeWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                layout_container_exec(limits, padding, h_spacing, &Alignment::Start,
                    &Alignment::Start, v_spacing, children, fuel, ContainerKind::Wrap)
            },
            RuntimeWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_flex_widget_exec(limits, padding, spacing, alignment,
                    direction, children, fuel)
            },
            RuntimeWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                  col_widths, row_heights, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_grid_widget_exec(limits, padding, h_spacing, v_spacing,
                    h_align, v_align, col_widths, row_heights, children, fuel)
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
                layout_absolute_widget_exec(limits, padding, children, fuel)
            },
            RuntimeWidget::Margin { margin, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_margin_widget_exec(limits, margin, child, fuel)
            },
            RuntimeWidget::Conditional { visible, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_conditional_exec(limits, *visible, child, fuel)
            },
            RuntimeWidget::SizedBox { inner_limits: il, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_sized_box_widget_exec(limits, il, child, fuel)
            },
            RuntimeWidget::AspectRatio { ratio, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_aspect_ratio_widget_exec(limits, ratio, child, fuel)
            },
            RuntimeWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert(child.wf_spec((fuel - 1) as nat)) by {
                        assert(child.wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_scroll_view_exec(limits, viewport, scroll_x, scroll_y, child, fuel)
            },
            RuntimeWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                layout_listview_widget_exec(limits, spacing, scroll_y,
                    viewport, children, fuel)
            },
        }
    }
}

/// Layout with verified children-within-bounds guarantee.
/// Wraps `layout_widget_exec` and calls `lemma_layout_widget_cwb` in a proof block
/// to establish that all children are positioned within the parent's bounds.
pub fn layout_widget_checked(
    limits: &RuntimeLimits,
    widget: &RuntimeWidget,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        limits@.wf(),
        widget.wf_spec(fuel as nat),
        fuel > 0,
        widget_wf::<RationalModel>(limits@, widget.model(), fuel as nat),
        widget_cwb_ok::<RationalModel>(widget.model(), fuel as nat),
    ensures
        out.wf_spec(),
        out@ == layout_widget::<RationalModel>(limits@, widget.model(), fuel as nat),
        out@.children_within_bounds(),
{
    let out = layout_widget_exec(limits, widget, fuel);
    proof {
        lemma_layout_widget_cwb::<RationalModel>(limits@, widget.model(), fuel as nat);
    }
    out
}

/// Which layout strategy to use.
pub enum ContainerKind {
    Column,
    Row,
    Stack,
    Wrap,
}

/// Shared container layout: recursively compute children, call layout exec, merge.
fn layout_container_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing1: &RuntimeRational,  // spacing (col/row), h_spacing (wrap), unused (stack)
    align1: &Alignment,          // alignment (row), h_align (stack), unused (col/wrap)
    align2: &Alignment,          // alignment (col), v_align (stack), unused (row/wrap)
    spacing2: &RuntimeRational,  // v_spacing (wrap), unused (col/row/stack)
    children: &Vec<RuntimeWidget>,
    fuel: usize,
    kind: ContainerKind,
) -> (out: RuntimeNode)
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
            let cn = widget_child_nodes(inner, spec_wc, (fuel - 1) as nat);
            match kind {
                ContainerKind::Column =>
                    layout_column_body(limits@, padding@, spacing1@, *align2, cn),
                ContainerKind::Row =>
                    layout_row_body(limits@, padding@, spacing1@, *align1, cn),
                ContainerKind::Stack =>
                    layout_stack_body(limits@, padding@, *align1, *align2, cn),
                ContainerKind::Wrap =>
                    layout_wrap_body(limits@, padding@, spacing1@, spacing2@, cn),
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

    // 1. Recursively compute child nodes
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_wc.len() == n as nat,
            // Pointwise Seq::new unfolding (ghost let not available in loop)
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] children@[j]).model(),
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_nodes@.len() == i as int,
            child_sizes@.len() == i as int,
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                        inner@, spec_wc[j], (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == child_nodes@[j]@.size
            },
        decreases n - i,
    {
        let cn = layout_widget_exec(&inner, &children[i], fuel - 1);
        child_sizes.push(cn.size.copy_size());
        child_nodes.push(cn);
        i = i + 1;
    }

    // Assert child_sizes wf for layout exec preconditions
    proof {
        assert forall|j: int| 0 <= j < child_sizes@.len() implies
            (#[trigger] child_sizes@[j]).wf_spec()
        by {
            // From loop invariant: child_sizes@[j].wf_spec() for j < i == n
        }
    }

    // 2. Call the appropriate layout exec
    let layout_result = match kind {
        ContainerKind::Column => {
            column_layout_exec(limits, padding, spacing1, align2, &child_sizes)
        },
        ContainerKind::Row => {
            row_layout_exec(limits, padding, spacing1, align1, &child_sizes)
        },
        ContainerKind::Stack => {
            stack_layout_exec(limits, padding, align1, align2, &child_sizes)
        },
        ContainerKind::Wrap => {
            wrap_layout_exec(limits, padding, spacing1, spacing2, &child_sizes)
        },
    };

    // Prove layout_result has n children (needed for merge precondition)
    proof {
        let child_sizes_seq: Seq<Size<RationalModel>> =
            Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        match kind {
            ContainerKind::Column => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                lemma_column_children_len::<RationalModel>(
                    padding@, spacing1@, *align2, child_sizes_seq, avail_w, 0nat);
            },
            ContainerKind::Row => {
                let avail_h = limits@.max.height.sub(padding@.vertical());
                lemma_row_children_len::<RationalModel>(
                    padding@, spacing1@, *align1, child_sizes_seq, avail_h, 0nat);
            },
            ContainerKind::Stack => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                let avail_h = limits@.max.height.sub(padding@.vertical());
                lemma_stack_children_len::<RationalModel>(
                    padding@, *align1, *align2, child_sizes_seq, avail_w, avail_h, 0nat);
            },
            ContainerKind::Wrap => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                lemma_wrap_children_len::<RationalModel>(
                    padding@, spacing1@, spacing2@, child_sizes_seq, avail_w, 0nat);
            },
        }
        assert(layout_result.children@.len() == child_nodes@.len());
    }

    // 3. Merge positions from layout_result with child_nodes
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);

    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    // 4. Connect to spec
    proof {
        let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
        let spec_cn = widget_child_nodes(inner_spec, spec_wc, (fuel - 1) as nat);

        // Show cn_models == spec_cn via extensional equality
        assert(cn_models.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < cn_models.len() as int implies
            cn_models[j] == spec_cn[j]
        by {
            // cn_models[j] = child_nodes@[j]@ = layout_widget(inner@, spec_wc[j], fuel-1)
            // spec_cn[j] = layout_widget(inner_spec, spec_wc[j], fuel-1)
            // inner@ == inner_spec, so they're equal
        }
        assert(cn_models =~= spec_cn);

        let child_sizes_seq = Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        assert(child_sizes_seq.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < child_sizes_seq.len() as int implies
            child_sizes_seq[j] == spec_cn[j].size
        by {}
        assert(child_sizes_seq =~= Seq::new(spec_cn.len(), |j: int| spec_cn[j].size));
    }

    merged
}

// ── Flex widget exec ─────────────────────────────────────────────

/// Layout a flex widget: each child gets per-weight limits.
fn layout_flex_widget_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing: &RuntimeRational,
    alignment: &Alignment,
    direction: &FlexDirection,
    children: &Vec<RuntimeFlexItem>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==>
            children@[i].weight.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat),
        children@.len() > 0 ==> !sum_weights::<RationalModel>(
            Seq::new(children@.len() as nat, |i: int| children@[i].weight@),
            children@.len() as nat,
        ).eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_fi = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::Flex {
                padding: padding@, spacing: spacing@, alignment: *alignment,
                direction: *direction, children: spec_fi,
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_fi: Seq<FlexItem<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());
    let ghost spec_weights: Seq<RationalModel> =
        Seq::new(children@.len() as nat, |i: int| children@[i].weight@);

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    // Compute weights and total_weight
    let mut weights: Vec<RuntimeRational> = Vec::new();
    let mut total_weight = RuntimeRational::from_int(0);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, n == children@.len(),
            weights@.len() == i as int,
            total_weight.wf_spec(),
            total_weight@ == sum_weights::<RationalModel>(spec_weights, i as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] weights@[j]).wf_spec()
                &&& weights@[j]@ == children@[j].weight@
            },
            forall|j: int| 0 <= j < children@.len() ==> children@[j].weight.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==> spec_weights[j] == children@[j].weight@,
        decreases n - i,
    {
        let w = copy_rational(&children[i].weight);
        total_weight = total_weight.add(&children[i].weight);
        weights.push(w);
        i = i + 1;
    }

    // Compute total_spacing
    let total_spacing = if n > 0 {
        let sp_count = n - 1;
        let mut sp = RuntimeRational::from_int(0);
        let mut j: usize = 0;
        while j < sp_count
            invariant
                0 <= j <= sp_count,
                sp.wf_spec(), spacing.wf_spec(),
                sp@ == repeated_add::<RationalModel>(spacing@, j as nat),
            decreases sp_count - j,
        {
            sp = sp.add(spacing);
            j = j + 1;
        }
        sp
    } else {
        RuntimeRational::from_int(0)
    };

    // Recursively layout each child with per-weight limits, collecting child nodes + cross sizes
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut cross_sizes: Vec<RuntimeRational> = Vec::new();
    let mut k: usize = 0;

    let ghost avail_spec: RationalModel;
    match direction {
        FlexDirection::Column => {
            let available = inner.max.height.sub(&total_spacing);
            proof { avail_spec = available@; }
            while k < n
                invariant
                    0 <= k <= n, n == children@.len(),
                    inner.wf_spec(),
                    inner@ == limits@.shrink(pad_h@, pad_v@),
                    total_weight.wf_spec(),
                    total_weight@ == sum_weights::<RationalModel>(spec_weights, n as nat),
                    n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
                    available.wf_spec(),
                    available@ == avail_spec,
                    child_nodes@.len() == k as int,
                    cross_sizes@.len() == k as int,
                    weights@.len() == n as int,
                    forall|j: int| 0 <= j < n ==> weights@[j].wf_spec(),
                    forall|j: int| 0 <= j < n ==> weights@[j]@ == spec_weights[j],
                    fuel > 0,
                    forall|j: int| 0 <= j < children@.len() ==>
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] child_nodes@[j]).wf_spec()
                        &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                            Limits { min: inner@.min, max: Size::new(inner@.max.width,
                                flex_child_main_size::<RationalModel>(spec_weights[j], total_weight@, avail_spec)) },
                            children@[j].child.model(), (fuel - 1) as nat)
                    },
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] cross_sizes@[j]).wf_spec()
                        &&& cross_sizes@[j]@ == child_nodes@[j]@.size.width
                    },
                decreases n - k,
            {
                let wd = weights[k].div(&total_weight);
                let main_alloc = wd.mul(&available);
                let child_lim = RuntimeLimits::new(
                    inner.min.copy_size(),
                    RuntimeSize::new(copy_rational(&inner.max.width), main_alloc),
                );
                let cn = layout_widget_exec(&child_lim, &children[k].child, fuel - 1);
                let cw = copy_rational(&cn.size.width);
                cross_sizes.push(cw);
                child_nodes.push(cn);
                k = k + 1;
            }

            // Prove flex_column_layout_exec preconditions
            proof {
                assert(Seq::new(weights@.len() as nat, |i: int| weights@[i]@)
                    =~= spec_weights);
                assert forall|j: int| 0 <= j < cross_sizes@.len() implies
                    (#[trigger] cross_sizes@[j]).wf_spec()
                by {}
            }
            let layout_result = flex_column_layout_exec(
                limits, padding, spacing, alignment, &weights, &cross_sizes);

            // Merge — layout_result.children@.len() == n from flex_column_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            // Connect merged result to spec layout_widget
            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_column_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                // 1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                // 2. Cross sizes view matches what layout_flex_column_body computes
                let cross_view: Seq<RationalModel> =
                    Seq::new(cross_sizes@.len() as nat, |i: int| cross_sizes@[i]@);
                let spec_cross: Seq<RationalModel> =
                    Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.width);
                assert(cross_view =~= spec_cross) by {
                    assert(cross_view.len() == spec_cross.len());
                    assert forall|j: int| 0 <= j < cross_view.len() as int implies
                        cross_view[j] == spec_cross[j]
                    by {
                        // cross_sizes@[j]@ == child_nodes@[j]@.size.width == cn_models[j].size.width == spec_cn[j].size.width
                    }
                }

                // 3. Weights from spec_fi match spec_weights
                let spec_weights_fi: Seq<RationalModel> =
                    Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
                assert(spec_weights_fi =~= spec_weights) by {
                    assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
                        spec_weights_fi[i] == spec_weights[i]
                    by {
                        let fi_i = spec_fi[i];
                        assert(fi_i == children@[i].model());
                    }
                }

                // 4. merged@ == layout_flex_column_body(...)
                //    layout_flex_column_body unfolds to:
                //      merge_layout(flex_column_layout(limits@, padding@, spacing@, alignment, weights, cross_from_cn), cn)
                //    And merged@ == merge_layout(layout_result@, cn_models)
                //    where layout_result@ == flex_column_layout(limits@, padding@, spacing@, alignment, weight_view, cross_view)
                //    Since weight_view =~= spec_weights =~= spec_weights_fi and cross_view =~= spec_cross
                //    and cn_models =~= spec_cn, these are equal.
                assert(merged@ == layout_flex_column_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
        FlexDirection::Row => {
            let available = inner.max.width.sub(&total_spacing);
            proof { avail_spec = available@; }
            while k < n
                invariant
                    0 <= k <= n, n == children@.len(),
                    inner.wf_spec(),
                    inner@ == limits@.shrink(pad_h@, pad_v@),
                    total_weight.wf_spec(),
                    total_weight@ == sum_weights::<RationalModel>(spec_weights, n as nat),
                    n > 0 ==> !total_weight@.eqv_spec(RationalModel::from_int_spec(0)),
                    available.wf_spec(),
                    available@ == avail_spec,
                    child_nodes@.len() == k as int,
                    cross_sizes@.len() == k as int,
                    weights@.len() == n as int,
                    forall|j: int| 0 <= j < n ==> weights@[j].wf_spec(),
                    forall|j: int| 0 <= j < n ==> weights@[j]@ == spec_weights[j],
                    fuel > 0,
                    forall|j: int| 0 <= j < children@.len() ==>
                        (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] child_nodes@[j]).wf_spec()
                        &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                            Limits { min: inner@.min, max: Size::new(
                                flex_child_main_size::<RationalModel>(spec_weights[j], total_weight@, avail_spec),
                                inner@.max.height) },
                            children@[j].child.model(), (fuel - 1) as nat)
                    },
                    forall|j: int| 0 <= j < k ==> {
                        &&& (#[trigger] cross_sizes@[j]).wf_spec()
                        &&& cross_sizes@[j]@ == child_nodes@[j]@.size.height
                    },
                decreases n - k,
            {
                let wd = weights[k].div(&total_weight);
                let main_alloc = wd.mul(&available);
                let child_lim = RuntimeLimits::new(
                    inner.min.copy_size(),
                    RuntimeSize::new(main_alloc, copy_rational(&inner.max.height)),
                );
                let cn = layout_widget_exec(&child_lim, &children[k].child, fuel - 1);
                let ch = copy_rational(&cn.size.height);
                cross_sizes.push(ch);
                child_nodes.push(cn);
                k = k + 1;
            }

            proof {
                assert(Seq::new(weights@.len() as nat, |i: int| weights@[i]@)
                    =~= spec_weights);
                assert forall|j: int| 0 <= j < cross_sizes@.len() implies
                    (#[trigger] cross_sizes@[j]).wf_spec()
                by {}
            }
            let layout_result = flex_row_layout_exec(
                limits, padding, spacing, alignment, &weights, &cross_sizes);

            // Merge — layout_result.children@.len() == n from flex_row_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_row_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                // 1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                // 2. Cross sizes view matches
                let cross_view: Seq<RationalModel> =
                    Seq::new(cross_sizes@.len() as nat, |i: int| cross_sizes@[i]@);
                let spec_cross: Seq<RationalModel> =
                    Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.height);
                assert(cross_view =~= spec_cross) by {
                    assert(cross_view.len() == spec_cross.len());
                    assert forall|j: int| 0 <= j < cross_view.len() as int implies
                        cross_view[j] == spec_cross[j]
                    by {}
                }

                // 3. Weights from spec_fi match
                let spec_weights_fi: Seq<RationalModel> =
                    Seq::new(spec_fi.len(), |i: int| spec_fi[i].weight);
                assert(spec_weights_fi =~= spec_weights) by {
                    assert forall|i: int| 0 <= i < spec_weights_fi.len() as int implies
                        spec_weights_fi[i] == spec_weights[i]
                    by {
                        let fi_i = spec_fi[i];
                        assert(fi_i == children@[i].model());
                    }
                }

                // 4. merged@ == layout_flex_row_body(...)
                assert(merged@ == layout_flex_row_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
    }
}

// ── Grid widget exec ─────────────────────────────────────────────

/// Layout a grid widget: each child gets cell-sized limits.
fn layout_grid_widget_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    h_spacing: &RuntimeRational,
    v_spacing: &RuntimeRational,
    h_align: &Alignment,
    v_align: &Alignment,
    col_widths: &Vec<RuntimeSize>,
    row_heights: &Vec<RuntimeSize>,
    children: &Vec<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        h_spacing.wf_spec(),
        v_spacing.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
        forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
        children@.len() == col_widths@.len() * row_heights@.len(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_cw = Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
            let spec_rh = Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
            let spec_wc = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::Grid {
                padding: padding@, h_spacing: h_spacing@, v_spacing: v_spacing@,
                h_align: *h_align, v_align: *v_align,
                col_widths: spec_cw, row_heights: spec_rh, children: spec_wc,
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_cw: Seq<Size<RationalModel>> =
        Seq::new(col_widths@.len() as nat, |i: int| col_widths@[i]@);
    let ghost spec_rh: Seq<Size<RationalModel>> =
        Seq::new(row_heights@.len() as nat, |i: int| row_heights@[i]@);
    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let num_cols = col_widths.len();
    let num_rows = row_heights.len();
    let n = children.len();

    let ghost inner_spec = limits@.shrink(pad_h@, pad_v@);

    // Recursively layout each child with cell-sized limits (flat iteration)
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes_2d: Vec<Vec<RuntimeSize>> = Vec::new();
    let mut flat_idx: usize = 0;
    let mut r: usize = 0;

    while r < num_rows
        invariant
            0 <= r <= num_rows,
            num_cols == col_widths@.len(),
            num_rows == row_heights@.len(),
            n == children@.len(),
            n == num_cols * num_rows,
            flat_idx == r * num_cols,
            inner.wf_spec(),
            inner@ == inner_spec,
            fuel > 0,
            forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
            forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
            forall|i: int| 0 <= i < children@.len() ==>
                (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
            child_nodes@.len() == flat_idx as int,
            child_sizes_2d@.len() == r as int,
            // Each child node is wf
            forall|j: int| 0 <= j < flat_idx as int ==>
                (#[trigger] child_nodes@[j]).wf_spec(),
            // Each child node was laid out with cell-sized limits (using row/col indices)
            forall|ri: int, ci: int| 0 <= ri < r as int && 0 <= ci < num_cols as int ==> {
                child_nodes@[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                    Limits { min: inner_spec.min, max: Size::new(
                        col_widths@[ci]@.width, row_heights@[ri]@.height) },
                    children@[ri * num_cols as int + ci].model(),
                    (fuel - 1) as nat)
            },
            // child_sizes_2d rows have right length and wf, and match child node sizes
            forall|ri: int| 0 <= ri < r as int ==> {
                &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                &&& forall|ci: int| 0 <= ci < num_cols ==> {
                    &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                    &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                }
            },
        decreases num_rows - r,
    {
        let mut row_sizes: Vec<RuntimeSize> = Vec::new();
        let mut c: usize = 0;
        let ghost row_base: int = flat_idx as int;
        let ghost pre_inner_cn: Seq<RuntimeNode> = child_nodes@;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                num_cols == col_widths@.len(),
                num_rows == row_heights@.len(),
                n == children@.len(),
                n == num_cols * num_rows,
                r < num_rows,
                flat_idx == r * num_cols + c,
                row_base == (r * num_cols) as int,
                inner.wf_spec(),
                inner@ == inner_spec,
                fuel > 0,
                forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec(),
                forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec(),
                forall|i: int| 0 <= i < children@.len() ==>
                    (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
                child_nodes@.len() == flat_idx as int,
                child_sizes_2d@.len() == r as int,
                row_sizes@.len() == c as int,
                // Ghost snapshot: old elements unchanged
                pre_inner_cn.len() == row_base,
                forall|j: int| 0 <= j < row_base ==>
                    child_nodes@[j] == (#[trigger] pre_inner_cn[j]),
                // Preserve existing wf facts
                forall|j: int| 0 <= j < row_base ==>
                    (#[trigger] child_nodes@[j]).wf_spec(),
                // Completed rows' layout facts (via snapshot, invariant through inner loop)
                forall|ri: int, ci: int| 0 <= ri < r as int && 0 <= ci < num_cols as int ==> {
                    pre_inner_cn[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                        Limits { min: inner_spec.min, max: Size::new(
                            col_widths@[ci]@.width, row_heights@[ri]@.height) },
                        children@[ri * num_cols as int + ci].model(),
                        (fuel - 1) as nat)
                },
                // Completed rows' child_sizes_2d facts (via snapshot)
                forall|ri: int| 0 <= ri < r as int ==> {
                    &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                    &&& forall|ci: int| 0 <= ci < num_cols ==> {
                        &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                        &&& child_sizes_2d@[ri]@[ci]@ == pre_inner_cn[ri * num_cols as int + ci]@.size
                    }
                },
                // New child nodes in this row
                forall|ci: int| 0 <= ci < c ==> {
                    &&& (#[trigger] child_nodes@[row_base + ci]).wf_spec()
                    &&& child_nodes@[row_base + ci]@ == layout_widget::<RationalModel>(
                        Limits { min: inner_spec.min, max: Size::new(
                            col_widths@[ci]@.width, row_heights@[r as int]@.height) },
                        children@[row_base + ci].model(),
                        (fuel - 1) as nat)
                },
                // Row sizes match child node sizes
                forall|ci: int| 0 <= ci < c ==> {
                    &&& (#[trigger] row_sizes@[ci]).wf_spec()
                    &&& row_sizes@[ci]@ == child_nodes@[row_base + ci]@.size
                },
            decreases num_cols - c,
        {
            proof {
                assert(flat_idx < n) by(nonlinear_arith)
                    requires flat_idx == r * num_cols + c,
                        c < num_cols, r < num_rows,
                        n == num_cols * num_rows;
                // Help Z3 instantiate quantifiers for preconditions
                assert(col_widths@[c as int].wf_spec());
                assert(row_heights@[r as int].wf_spec());
                assert(children@[flat_idx as int].wf_spec((fuel - 1) as nat));
            }
            let child_lim = RuntimeLimits::new(
                inner.min.copy_size(),
                RuntimeSize::new(
                    copy_rational(&col_widths[c].width),
                    copy_rational(&row_heights[r].height)),
            );
            let cn = layout_widget_exec(&child_lim, &children[flat_idx], fuel - 1);
            row_sizes.push(cn.size.copy_size());
            child_nodes.push(cn);
            c = c + 1;
            flat_idx = flat_idx + 1;
        }
        // Capture row_sizes facts before push moves it
        let ghost row_sizes_len = row_sizes@.len();
        let ghost row_sizes_view: Seq<RuntimeSize> = row_sizes@;

        child_sizes_2d.push(row_sizes);

        proof {
            // row_sizes had num_cols elements, all wf, matching child node sizes
            assert(row_sizes_len == num_cols as int);

            // child_sizes_2d@[r] is the just-pushed row_sizes
            assert(child_sizes_2d@[r as int]@ =~= row_sizes_view);

            // Combine child_nodes wf facts from both ranges
            assert forall|j: int| 0 <= j < flat_idx as int implies
                (#[trigger] child_nodes@[j]).wf_spec()
            by {
                if j < row_base {
                } else {
                    let ci = j - row_base;
                    assert(child_nodes@[row_base + ci].wf_spec());
                }
            }

            // Establish snapshot preservation for old rows
            assert forall|ri: int, ci: int|
                0 <= ri < r as int && 0 <= ci < num_cols as int implies
                #[trigger] child_nodes@[ri * (num_cols as int) + ci]
                    == pre_inner_cn[ri * (num_cols as int) + ci]
            by {
                let idx = ri * (num_cols as int) + ci;
                assert((ri + 1) * (num_cols as int) <= row_base) by(nonlinear_arith)
                    requires ri + 1 <= (r as int), (num_cols as int) >= 0,
                        row_base == (r as int) * (num_cols as int);
                assert(idx < (ri + 1) * (num_cols as int)) by(nonlinear_arith)
                    requires idx == ri * (num_cols as int) + ci,
                        ci < (num_cols as int);
            }

            // Reconstruct completed rows' layout_widget facts from snapshot
            assert forall|ri: int, ci: int|
                0 <= ri < (r + 1) as int && 0 <= ci < num_cols as int implies
                child_nodes@[ri * num_cols as int + ci]@ == layout_widget::<RationalModel>(
                    Limits { min: inner_spec.min, max: Size::new(
                        col_widths@[ci]@.width, row_heights@[ri]@.height) },
                    children@[ri * num_cols as int + ci].model(),
                    (fuel - 1) as nat)
            by {
                if ri < r as int {
                    assert(child_nodes@[ri * (num_cols as int) + ci]
                        == pre_inner_cn[ri * (num_cols as int) + ci]);
                } else {
                    assert(ri == r as int);
                    assert(ri * (num_cols as int) + ci == row_base + ci);
                }
            }

            // child_sizes_2d invariant for all rows including the new one
            assert forall|ri: int| 0 <= ri < (r + 1) as int implies {
                &&& (#[trigger] child_sizes_2d@[ri])@.len() == num_cols
                &&& forall|ci: int| 0 <= ci < num_cols ==> {
                    &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                    &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                }
            } by {
                if ri < r as int {
                    assert forall|ci: int| 0 <= ci < num_cols as int implies {
                        &&& (#[trigger] child_sizes_2d@[ri]@[ci]).wf_spec()
                        &&& child_sizes_2d@[ri]@[ci]@ == child_nodes@[ri * num_cols as int + ci]@.size
                    } by {
                        assert(child_nodes@[ri * (num_cols as int) + ci]
                            == pre_inner_cn[ri * (num_cols as int) + ci]);
                    }
                } else {
                    assert(ri == r as int);
                    assert(child_sizes_2d@[ri]@ =~= row_sizes_view);
                    assert(row_sizes_view.len() == num_cols as int);
                    assert(ri * (num_cols as int) == row_base);
                }
            }

            // flat_idx arithmetic
            assert(flat_idx == r * num_cols + num_cols);
            assert((r + 1) * num_cols == r * num_cols + num_cols) by(nonlinear_arith)
                requires r >= 0nat, num_cols >= 0nat;
        }

        r = r + 1;
    }

    // Call grid_layout_exec
    let layout_result = grid_layout_exec(
        limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, &child_sizes_2d);

    // Merge
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);
    proof {
        // After outer loop: r == num_rows, flat_idx == num_rows * num_cols
        // n == num_cols * num_rows (commutativity: flat_idx == n)
        assert(flat_idx == n) by(nonlinear_arith)
            requires flat_idx == (num_rows as int) * (num_cols as int),
                n == (num_cols as int) * (num_rows as int);
        assert(child_nodes@.len() == n as int);
        assert(cn_models.len() == n as nat);

        // Bridge child_sizes_2d to cn_models BEFORE child_nodes is consumed by merge
        assert forall|ri: int, ci: int|
            0 <= ri < num_rows as int && 0 <= ci < num_cols as int implies
            child_sizes_2d@[ri]@[ci]@ == cn_models[ri * (num_cols as int) + ci].size
        by {
            let nc = num_cols as int;
            let j = ri * nc + ci;
            // j is in range [0, n)
            assert(j < (n as int)) by(nonlinear_arith)
                requires 0 <= ri, ri < (num_rows as int), 0 <= ci, ci < nc,
                    (n as int) == nc * (num_rows as int), j == ri * nc + ci;
            assert(child_sizes_2d@[ri]@[ci]@ == child_nodes@[j]@.size);
            // Seq::new trigger: cn_models[j] == child_nodes@[j]@
        }
    }
    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    // Connect to spec layout_widget
    proof {
        let spec_cn: Seq<Node<RationalModel>> = grid_widget_child_nodes(
            inner_spec, spec_cw, spec_rh, spec_wc,
            num_cols as nat, (fuel - 1) as nat);

        // cn_models matches spec_cn: each element is the same layout_widget call
        assert(cn_models.len() == spec_cn.len());

        // When n > 0, we have num_cols > 0 (needed for div/mod)
        if n > 0 {
            assert(num_cols > 0 && num_rows > 0) by(nonlinear_arith)
                requires n as int == (num_cols as int) * (num_rows as int),
                    n > 0;

            assert forall|j: int| 0 <= j < cn_models.len() as int implies
                cn_models[j] == spec_cn[j]
            by {
                let nc = num_cols as int;
                let nr = num_rows as int;
                let ri = j / nc;
                let ci = j % nc;
                // vstd div/mod lemma: j == nc * (j / nc) + (j % nc)
                lemma_fundamental_div_mod(j, nc);
                assert(nc * ri + ci == j);
                assert(0 <= ci && ci < nc);
                assert(ri >= 0);
                // Now use nonlinear_arith with these Z3-derived facts:
                assert(ri < nr) by(nonlinear_arith)
                    requires ri >= 0, nc * ri + ci == j, 0 <= ci, ci < nc,
                        j < nc * nr, nc > 0;
                // Trigger Seq::new unfoldings for spec sequences
                let cw_ci = spec_cw[ci];
                assert(cw_ci == col_widths@[ci]@);
                let rh_ri = spec_rh[ri];
                assert(rh_ri == row_heights@[ri]@);
                let wc_j = spec_wc[j];
                assert(wc_j == children@[j].model());
            }
        }
        assert(cn_models =~= spec_cn);

        // child_sizes_2d view matches layout_grid_body's computed child_sizes
        let spec_cs_view: Seq<Seq<Size<RationalModel>>> =
            Seq::new(child_sizes_2d@.len() as nat, |i: int|
                Seq::new(child_sizes_2d@[i]@.len() as nat, |j: int| child_sizes_2d@[i]@[j]@));
        let body_cs: Seq<Seq<Size<RationalModel>>> = Seq::new(num_rows as nat, |r: int|
            Seq::new(num_cols as nat, |c: int| spec_cn[(r * num_cols as int + c)].size));
        assert(spec_cs_view =~= body_cs) by {
            assert(spec_cs_view.len() == body_cs.len());
            assert forall|ri: int| 0 <= ri < spec_cs_view.len() as int implies
                spec_cs_view[ri] =~= body_cs[ri]
            by {
                assert(spec_cs_view[ri].len() == body_cs[ri].len());
                assert forall|ci: int| 0 <= ci < spec_cs_view[ri].len() as int implies
                    spec_cs_view[ri][ci] == body_cs[ri][ci]
                by {
                    let j = ri * (num_cols as int) + ci;
                    // From pre-merge bridging proof:
                    //   child_sizes_2d@[ri]@[ci]@ == cn_models[j].size
                    // From cn_models =~= spec_cn:
                    //   cn_models[j].size == spec_cn[j].size == body_cs[ri][ci]
                    assert(child_sizes_2d@[ri]@[ci]@ == cn_models[j].size);
                    assert(cn_models[j] == spec_cn[j]);
                }
            }
        }
    }

    merged
}

// ── Absolute widget exec ─────────────────────────────────────────

/// Layout an absolute widget: each child at explicit (x, y) offsets.
fn layout_absolute_widget_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    children: &Vec<RuntimeAbsoluteChild>,
    fuel: usize,
) -> (out: RuntimeNode)
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
            let spec_w = Widget::Absolute {
                padding: padding@,
                children: spec_ac,
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_ac: Seq<AbsoluteChild<RationalModel>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    // Recursively layout each child, collecting child nodes + sizes + offsets
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut offsets_x: Vec<RuntimeRational> = Vec::new();
    let mut offsets_y: Vec<RuntimeRational> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_ac.len() == n as nat,
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_nodes@.len() == i as int,
            child_sizes@.len() == i as int,
            offsets_x@.len() == i as int,
            offsets_y@.len() == i as int,
            forall|j: int| 0 <= j < children@.len() ==> children@[j].x.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==> children@[j].y.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < n ==>
                spec_ac[j] == (#[trigger] children@[j]).model(),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                        inner@, spec_ac[j].child, (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == child_nodes@[j]@.size
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] offsets_x@[j]).wf_spec()
                &&& offsets_x@[j]@ == spec_ac[j].x
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] offsets_y@[j]).wf_spec()
                &&& offsets_y@[j]@ == spec_ac[j].y
            },
        decreases n - i,
    {
        let cn = layout_widget_exec(&inner, &children[i].child, fuel - 1);
        child_sizes.push(cn.size.copy_size());
        offsets_x.push(copy_rational(&children[i].x));
        offsets_y.push(copy_rational(&children[i].y));
        child_nodes.push(cn);
        i = i + 1;
    }

    // Assert preconditions for absolute_layout_exec
    proof {
        assert forall|j: int| 0 <= j < child_sizes@.len() implies
            (#[trigger] child_sizes@[j]).wf_spec()
        by {}
        assert forall|j: int| 0 <= j < offsets_x@.len() implies
            (#[trigger] offsets_x@[j]).wf_spec()
        by {}
        assert forall|j: int| 0 <= j < offsets_y@.len() implies
            (#[trigger] offsets_y@[j]).wf_spec()
        by {}
    }

    let layout_result = absolute_layout_exec(limits, padding, &child_sizes,
        &offsets_x, &offsets_y);

    // Merge
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);

    proof {
        lemma_absolute_children_len::<RationalModel>(
            padding@,
            Seq::new(child_sizes@.len() as nat, |i: int|
                (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@)),
            0,
        );
        assert(layout_result.children@.len() == child_nodes@.len());
    }

    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    // Connect to spec
    proof {
        let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
        let spec_cn = absolute_widget_child_nodes(inner_spec, spec_ac, (fuel - 1) as nat);

        // cn_models =~= spec_cn
        assert(cn_models.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < cn_models.len() as int implies
            cn_models[j] == spec_cn[j]
        by {
            let ac_j = spec_ac[j];
            assert(ac_j == children@[j].model());
            assert(ac_j.child == children@[j].child.model());
        }
        assert(cn_models =~= spec_cn);

        // child_sizes view matches spec
        let sizes_view: Seq<Size<RationalModel>> =
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);
        let spec_sizes: Seq<Size<RationalModel>> =
            Seq::new(spec_cn.len(), |i: int| spec_cn[i].size);
        assert(sizes_view =~= spec_sizes) by {
            assert forall|j: int| 0 <= j < sizes_view.len() as int implies
                sizes_view[j] == spec_sizes[j]
            by {}
        }

        // offsets match spec
        let ox_view: Seq<RationalModel> =
            Seq::new(offsets_x@.len() as nat, |i: int| offsets_x@[i]@);
        let oy_view: Seq<RationalModel> =
            Seq::new(offsets_y@.len() as nat, |i: int| offsets_y@[i]@);

        // Build spec child_data from spec_ac
        let body_offsets: Seq<(RationalModel, RationalModel)> =
            Seq::new(spec_ac.len(), |i: int| (spec_ac[i].x, spec_ac[i].y));
        let body_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)> =
            Seq::new(spec_cn.len(), |i: int|
                (body_offsets[i].0, body_offsets[i].1, spec_cn[i].size));

        // layout_result data matches body_data
        let exec_data: Seq<(RationalModel, RationalModel, Size<RationalModel>)> =
            Seq::new(child_sizes@.len() as nat, |i: int|
                (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@));
        assert(exec_data =~= body_data) by {
            assert forall|j: int| 0 <= j < exec_data.len() as int implies
                exec_data[j] == body_data[j]
            by {
                assert(offsets_x@[j]@ == spec_ac[j].x);
                assert(offsets_y@[j]@ == spec_ac[j].y);
            }
        }
    }

    merged
}

// ── Margin widget exec ──────────────────────────────────────────

/// Layout a margin widget: shrink limits, layout child, wrap with offsets.
fn layout_margin_widget_exec(
    limits: &RuntimeLimits,
    margin: &RuntimePadding,
    child: &Box<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        margin.wf_spec(),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::Margin {
                margin: margin@,
                child: Box::new(child.model()),
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let pad_h = margin.horizontal_exec();
    let pad_v = margin.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);

    let child_node = layout_widget_exec(&inner, child, fuel - 1);

    // Compute total size
    let pad_h2 = margin.horizontal_exec();
    let pad_v2 = margin.vertical_exec();
    let total_w = pad_h2.add(&child_node.size.width);
    let total_h = pad_v2.add(&child_node.size.height);
    let parent_size = limits.resolve_exec(RuntimeSize::new(total_w, total_h));

    // Build the single child with margin offsets
    let child_x = copy_rational(&margin.left);
    let child_y = copy_rational(&margin.top);
    let child_size = child_node.size.copy_size();

    let ghost child_spec = layout_widget::<RationalModel>(
        inner@, child.model(), (fuel - 1) as nat);

    let positioned_child = RuntimeNode {
        x: child_x,
        y: child_y,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<RationalModel> {
            x: margin@.left,
            y: margin@.top,
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    proof {
        assert(positioned_child.wf_shallow());
        assert(positioned_child@ == Node::<RationalModel> {
            x: margin@.left,
            y: margin@.top,
            size: child_spec.size,
            children: child_spec.children,
        });
    }

    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);

    let ghost parent_model = layout_widget::<RationalModel>(
        limits@,
        Widget::Margin { margin: margin@, child: Box::new(child.model()) },
        fuel as nat,
    );

    let mut result_children: Vec<RuntimeNode> = Vec::new();
    result_children.push(positioned_child);

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children: result_children,
        model: Ghost(parent_model),
    };

    proof {
        // Show out@ == parent_model
        // parent_model.children == Seq::empty().push(Node { x: margin.left, y: margin.top, ... })
        assert(parent_model.children.len() == 1);
        assert(out.children@.len() == 1);
        assert(out@.children.len() == 1);
        assert(out.children@[0].wf_shallow());
        assert(out.children@[0]@ == out@.children[0]);
    }

    out
}

// ── AspectRatio layout exec ─────────────────────────────────────

fn layout_aspect_ratio_widget_exec(
    limits: &RuntimeLimits,
    ratio: &RuntimeRational,
    child: &Box<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        ratio.wf_spec(),
        !ratio@.eqv_spec(RationalModel::from_int_spec(0)),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::AspectRatio {
                ratio: ratio@,
                child: Box::new(child.model()),
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let w1 = copy_rational(&limits.max.width);
    let h1 = w1.div(ratio);

    let child_node = if h1.le(&limits.max.height) {
        let eff_max = RuntimeSize::new(copy_rational(&limits.max.width), h1);
        let eff = RuntimeLimits {
            min: limits.min.copy_size(),
            max: eff_max,
            model: Ghost(Limits {
                min: limits@.min,
                max: Size::new(limits@.max.width, limits@.max.width.div(ratio@)),
            }),
        };
        layout_widget_exec(&eff, child, fuel - 1)
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
        layout_widget_exec(&eff, child, fuel - 1)
    };

    let resolved = limits.resolve_exec(child_node.size.copy_size());
    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);
    let cx = RuntimeRational::from_int(0);
    let cy = RuntimeRational::from_int(0);
    let child_size = child_node.size.copy_size();

    let ghost child_spec = if limits@.max.width.div(ratio@).le(limits@.max.height) {
        let eff = Limits {
            min: limits@.min,
            max: Size::new(limits@.max.width, limits@.max.width.div(ratio@)),
        };
        layout_widget::<RationalModel>(eff, child.model(), (fuel - 1) as nat)
    } else {
        let eff = Limits {
            min: limits@.min,
            max: Size::new(limits@.max.height.mul_spec(ratio@), limits@.max.height),
        };
        layout_widget::<RationalModel>(eff, child.model(), (fuel - 1) as nat)
    };

    let positioned_child = RuntimeNode {
        x: cx,
        y: cy,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<RationalModel> {
            x: RationalModel::from_int_spec(0),
            y: RationalModel::from_int_spec(0),
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    let ghost parent_model = layout_widget::<RationalModel>(
        limits@,
        Widget::AspectRatio { ratio: ratio@, child: Box::new(child.model()) },
        fuel as nat,
    );

    let mut result_children: Vec<RuntimeNode> = Vec::new();
    result_children.push(positioned_child);

    let out = RuntimeNode {
        x,
        y,
        size: resolved,
        children: result_children,
        model: Ghost(parent_model),
    };

    proof {
        assert(parent_model.children.len() == 1);
        assert(out.children@.len() == 1);
        assert(out@.children.len() == 1);
        assert(out.children@[0].wf_shallow());
        assert(out.children@[0]@ == out@.children[0]);
    }

    out
}

// ── ScrollView widget exec ───────────────────────────────────────

/// Layout a scroll view widget: child at (-scroll_x, -scroll_y) with viewport limits.
fn layout_scroll_view_exec(
    limits: &RuntimeLimits,
    viewport: &RuntimeSize,
    scroll_x: &RuntimeRational,
    scroll_y: &RuntimeRational,
    child: &Box<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        viewport.wf_spec(),
        scroll_x.wf_spec(),
        scroll_y.wf_spec(),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::ScrollView {
                viewport: viewport@,
                scroll_x: scroll_x@,
                scroll_y: scroll_y@,
                child: Box::new(child.model()),
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    // Child gets limits (zero_min, viewport)
    let child_min = RuntimeSize::zero_exec();
    let child_max = viewport.copy_size();
    let child_limits = RuntimeLimits::new(child_min, child_max);
    let child_node = layout_widget_exec(&child_limits, child, fuel - 1);

    let resolved = limits.resolve_exec(viewport.copy_size());
    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);
    let neg_sx = scroll_x.neg();
    let neg_sy = scroll_y.neg();
    let child_size = child_node.size.copy_size();

    let ghost child_spec = {
        let cl = Limits::<RationalModel> {
            min: Size::zero_size(),
            max: viewport@,
        };
        layout_widget::<RationalModel>(cl, child.model(), (fuel - 1) as nat)
    };

    let positioned_child = RuntimeNode {
        x: neg_sx,
        y: neg_sy,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<RationalModel> {
            x: scroll_x@.neg_spec(),
            y: scroll_y@.neg_spec(),
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    let ghost parent_model = layout_widget::<RationalModel>(
        limits@,
        Widget::ScrollView {
            viewport: viewport@,
            scroll_x: scroll_x@,
            scroll_y: scroll_y@,
            child: Box::new(child.model()),
        },
        fuel as nat,
    );

    let mut result_children: Vec<RuntimeNode> = Vec::new();
    result_children.push(positioned_child);

    let out = RuntimeNode {
        x,
        y,
        size: resolved,
        children: result_children,
        model: Ghost(parent_model),
    };

    proof {
        assert(parent_model.children.len() == 1);
        assert(out.children@.len() == 1);
        assert(out@.children.len() == 1);
        assert(out.children@[0].wf_shallow());
        assert(out.children@[0]@ == out@.children[0]);
    }

    out
}

// ── Merge layout exec ────────────────────────────────────────────

/// Merge positions from a layout result with recursively computed child nodes.
fn merge_layout_exec(
    layout_result: RuntimeNode,
    mut child_nodes: Vec<RuntimeNode>,
    ghost_child_models: Ghost<Seq<Node<RationalModel>>>,
) -> (out: RuntimeNode)
    requires
        layout_result.wf_spec(),
        layout_result.children@.len() == child_nodes@.len(),
        ghost_child_models@.len() == child_nodes@.len() as nat,
        forall|i: int| 0 <= i < child_nodes@.len() ==> {
            &&& (#[trigger] child_nodes@[i]).wf_spec()
            &&& child_nodes@[i]@ == ghost_child_models@[i]
        },
    ensures
        out.wf_spec(),
        out@ == merge_layout::<RationalModel>(layout_result@, ghost_child_models@),
{
    let ghost spec_cn = ghost_child_models@;
    let ghost merged_model = merge_layout::<RationalModel>(layout_result@, spec_cn);

    let n = child_nodes.len();
    let mut merged_children: Vec<RuntimeNode> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == layout_result.children@.len(),
            child_nodes@.len() == n,
            layout_result.wf_spec(),
            merged_children@.len() == i as int,
            spec_cn.len() == n as nat,
            merged_model.children.len() == n as nat,
            layout_result@.children.len() == n as nat,
            // Pointwise merge_layout unfolding (ghost let not available in loop)
            forall|j: int| 0 <= j < n ==>
                (#[trigger] merged_model.children[j]) == (Node::<RationalModel> {
                    x: layout_result@.children[j].x,
                    y: layout_result@.children[j].y,
                    size: spec_cn[j].size,
                    children: spec_cn[j].children,
                }),
            // Elements [i..n) still original
            forall|j: int| i as int <= j < n as int ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == spec_cn[j]
            },
            // Merged elements match model
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] merged_children@[j]).wf_shallow()
                &&& merged_children@[j]@ == merged_model.children[j]
            },
        decreases n - i,
    {
        let x = copy_rational(&layout_result.children[i].x);
        let y = copy_rational(&layout_result.children[i].y);

        // Capture facts about child_nodes[i] before the swap
        proof {
            assert(child_nodes@[i as int].wf_spec());
            assert(child_nodes@[i as int]@ == spec_cn[i as int]);
        }

        // Swap child_nodes[i] with a dummy to take ownership
        let mut swap_val = RuntimeNode::leaf_exec(
            RuntimeRational::from_int(0),
            RuntimeRational::from_int(0),
            RuntimeSize::zero_exec(),
        );
        child_nodes.set_and_swap(i, &mut swap_val);
        let cn = swap_val;

        // Construct ghost model directly from components
        let ghost child_model = Node::<RationalModel> {
            x: layout_result@.children[i as int].x,
            y: layout_result@.children[i as int].y,
            size: spec_cn[i as int].size,
            children: spec_cn[i as int].children,
        };

        let merged_child = RuntimeNode {
            x,
            y,
            size: cn.size,
            children: cn.children,
            model: Ghost(child_model),
        };

        proof {
            // child_model == merged_model.children[i] from pointwise invariant
            assert(child_model == merged_model.children[i as int]);
            // wf_shallow: fields match model
            assert(layout_result.children@[i as int].wf_shallow());
            assert(layout_result.children@[i as int]@ == layout_result@.children[i as int]);
            assert(merged_child.wf_shallow());
            assert(merged_child@ == merged_model.children[i as int]);
        }

        merged_children.push(merged_child);
        i = i + 1;
    }

    RuntimeNode {
        x: layout_result.x,
        y: layout_result.y,
        size: layout_result.size,
        children: merged_children,
        model: Ghost(merged_model),
    }
}

} // verus!
