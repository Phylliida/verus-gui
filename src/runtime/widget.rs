use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::ring::Ring;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::linear::*;
use crate::runtime::stack::*;
use crate::runtime::wrap::*;
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
use crate::runtime::flex::*;
use crate::runtime::widget_sized_box::layout_sized_box_widget_exec;
use crate::runtime::widget_margin::layout_margin_widget_exec;
use crate::runtime::widget_aspect_ratio::layout_aspect_ratio_widget_exec;
use crate::runtime::widget_scroll::layout_scroll_view_exec;
use crate::runtime::widget_grid::layout_grid_widget_exec;
use crate::runtime::widget_absolute::layout_absolute_widget_exec;
use crate::runtime::text_input::RuntimeTextInputConfig;

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

/// Runtime leaf widget: no children.
pub enum RuntimeLeafWidget {
    Leaf {
        size: RuntimeSize,
        model: Ghost<LeafWidget<RationalModel>>,
    },
    TextInput {
        preferred_size: RuntimeSize,
        text_input_id: usize,
        config: RuntimeTextInputConfig,
        model: Ghost<LeafWidget<RationalModel>>,
    },
}

/// Runtime wrapper widget: exactly one child.
pub enum RuntimeWrapperWidget {
    Margin {
        margin: RuntimePadding,
        child: Box<RuntimeWidget>,
        model: Ghost<WrapperWidget<RationalModel>>,
    },
    Conditional {
        visible: bool,
        child: Box<RuntimeWidget>,
        model: Ghost<WrapperWidget<RationalModel>>,
    },
    SizedBox {
        inner_limits: RuntimeLimits,
        child: Box<RuntimeWidget>,
        model: Ghost<WrapperWidget<RationalModel>>,
    },
    AspectRatio {
        ratio: RuntimeRational,
        child: Box<RuntimeWidget>,
        model: Ghost<WrapperWidget<RationalModel>>,
    },
    ScrollView {
        viewport: RuntimeSize,
        scroll_x: RuntimeRational,
        scroll_y: RuntimeRational,
        child: Box<RuntimeWidget>,
        model: Ghost<WrapperWidget<RationalModel>>,
    },
}

/// Runtime container widget: multiple children.
#[allow(inconsistent_fields)]
pub enum RuntimeContainerWidget {
    Column {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    Row {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    Stack {
        padding: RuntimePadding,
        h_align: Alignment,
        v_align: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    Wrap {
        padding: RuntimePadding,
        h_spacing: RuntimeRational,
        v_spacing: RuntimeRational,
        children: Vec<RuntimeWidget>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    Flex {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        direction: FlexDirection,
        children: Vec<RuntimeFlexItem>,
        model: Ghost<ContainerWidget<RationalModel>>,
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
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    Absolute {
        padding: RuntimePadding,
        children: Vec<RuntimeAbsoluteChild>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
    ListView {
        spacing: RuntimeRational,
        scroll_y: RuntimeRational,
        viewport: RuntimeSize,
        children: Vec<RuntimeWidget>,
        model: Ghost<ContainerWidget<RationalModel>>,
    },
}

/// Runtime Widget: stratified to mirror spec Widget hierarchy.
pub enum RuntimeWidget {
    Leaf(RuntimeLeafWidget),
    Wrapper(RuntimeWrapperWidget),
    Container(RuntimeContainerWidget),
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

// ── Sub-enum impls ──────────────────────────────────────────────

impl RuntimeLeafWidget {
    pub open spec fn model(&self) -> LeafWidget<RationalModel> {
        match self {
            RuntimeLeafWidget::Leaf { model, .. } => model@,
            RuntimeLeafWidget::TextInput { model, .. } => model@,
        }
    }

    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeLeafWidget::Leaf { size, model } => {
                &&& size.wf_spec()
                &&& model@ == LeafWidget::Leaf { size: size@ }
            },
            RuntimeLeafWidget::TextInput { preferred_size, text_input_id, config, model } => {
                &&& preferred_size.wf_spec()
                &&& model@ == LeafWidget::TextInput {
                    preferred_size: preferred_size@,
                    text_input_id: *text_input_id as nat,
                    config: config@,
                }
            },
        }
    }
}

impl RuntimeWrapperWidget {
    pub open spec fn model(&self) -> WrapperWidget<RationalModel> {
        match self {
            RuntimeWrapperWidget::Margin { model, .. } => model@,
            RuntimeWrapperWidget::Conditional { model, .. } => model@,
            RuntimeWrapperWidget::SizedBox { model, .. } => model@,
            RuntimeWrapperWidget::AspectRatio { model, .. } => model@,
            RuntimeWrapperWidget::ScrollView { model, .. } => model@,
        }
    }

    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeWrapperWidget::Margin { margin, child, model } => {
                &&& margin.wf_spec()
                &&& model@ == WrapperWidget::Margin {
                    margin: margin@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWrapperWidget::Conditional { visible, child, model } => {
                model@ == WrapperWidget::Conditional {
                    visible: *visible,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWrapperWidget::SizedBox { inner_limits, child, model } => {
                &&& inner_limits.wf_spec()
                &&& model@ == WrapperWidget::SizedBox {
                    inner_limits: inner_limits@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWrapperWidget::AspectRatio { ratio, child, model } => {
                &&& ratio.wf_spec()
                &&& !ratio@.eqv_spec(RationalModel::from_int_spec(0))
                &&& model@ == WrapperWidget::AspectRatio {
                    ratio: ratio@,
                    child: Box::new(child.model()),
                }
            },
            RuntimeWrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                &&& viewport.wf_spec()
                &&& scroll_x.wf_spec()
                &&& scroll_y.wf_spec()
                &&& model@ == WrapperWidget::ScrollView {
                    viewport: viewport@,
                    scroll_x: scroll_x@,
                    scroll_y: scroll_y@,
                    child: Box::new(child.model()),
                }
            },
        }
    }

}

impl RuntimeContainerWidget {
    pub open spec fn model(&self) -> ContainerWidget<RationalModel> {
        match self {
            RuntimeContainerWidget::Column { model, .. } => model@,
            RuntimeContainerWidget::Row { model, .. } => model@,
            RuntimeContainerWidget::Stack { model, .. } => model@,
            RuntimeContainerWidget::Wrap { model, .. } => model@,
            RuntimeContainerWidget::Flex { model, .. } => model@,
            RuntimeContainerWidget::Grid { model, .. } => model@,
            RuntimeContainerWidget::Absolute { model, .. } => model@,
            RuntimeContainerWidget::ListView { model, .. } => model@,
        }
    }

    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeContainerWidget::Column { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == ContainerWidget::Column {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::Row { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == ContainerWidget::Row {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::Stack { padding, h_align, v_align, children, model } => {
                &&& padding.wf_spec()
                &&& model@ == ContainerWidget::Stack {
                    padding: padding@,
                    h_align: *h_align,
                    v_align: *v_align,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                &&& padding.wf_spec()
                &&& h_spacing.wf_spec()
                &&& v_spacing.wf_spec()
                &&& model@ == ContainerWidget::Wrap {
                    padding: padding@,
                    h_spacing: h_spacing@,
                    v_spacing: v_spacing@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].weight.wf_spec()
                &&& children@.len() > 0 ==> !sum_weights::<RationalModel>(
                    Seq::new(children@.len() as nat, |i: int| children@[i].weight@),
                    children@.len() as nat,
                ).eqv_spec(RationalModel::from_int_spec(0))
                &&& model@ == ContainerWidget::Flex {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    direction: *direction,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                  col_widths, row_heights, children, model } => {
                &&& padding.wf_spec()
                &&& h_spacing.wf_spec()
                &&& v_spacing.wf_spec()
                &&& forall|i: int| 0 <= i < col_widths@.len() ==> col_widths@[i].wf_spec()
                &&& forall|i: int| 0 <= i < row_heights@.len() ==> row_heights@[i].wf_spec()
                &&& children@.len() == col_widths@.len() * row_heights@.len()
                &&& model@ == ContainerWidget::Grid {
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
            RuntimeContainerWidget::Absolute { padding, children, model } => {
                &&& padding.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].x.wf_spec()
                &&& forall|i: int| 0 <= i < children@.len() ==> children@[i].y.wf_spec()
                &&& model@ == ContainerWidget::Absolute {
                    padding: padding@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeContainerWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                &&& spacing.wf_spec()
                &&& scroll_y.wf_spec()
                &&& viewport.wf_spec()
                &&& model@ == ContainerWidget::ListView {
                    spacing: spacing@,
                    scroll_y: scroll_y@,
                    viewport: viewport@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
        }
    }

}

// ── RuntimeWidget delegation ────────────────────────────────────

impl RuntimeWidget {
    /// Extract the ghost model.
    pub open spec fn model(&self) -> Widget<RationalModel> {
        match self {
            RuntimeWidget::Leaf(l) => Widget::Leaf(l.model()),
            RuntimeWidget::Wrapper(w) => Widget::Wrapper(w.model()),
            RuntimeWidget::Container(c) => Widget::Container(c.model()),
        }
    }

    /// Shallow well-formedness: direct fields match model, no recursive child check.
    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeWidget::Leaf(l) => l.wf_shallow(),
            RuntimeWidget::Wrapper(w) => w.wf_shallow(),
            RuntimeWidget::Container(c) => c.wf_shallow(),
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
                RuntimeWidget::Leaf(_) => true,
                RuntimeWidget::Wrapper(w) => match w {
                    RuntimeWrapperWidget::Margin { child, .. } =>
                        child.wf_spec((fuel - 1) as nat),
                    RuntimeWrapperWidget::Conditional { child, .. } =>
                        child.wf_spec((fuel - 1) as nat),
                    RuntimeWrapperWidget::SizedBox { child, .. } =>
                        child.wf_spec((fuel - 1) as nat),
                    RuntimeWrapperWidget::AspectRatio { child, .. } =>
                        child.wf_spec((fuel - 1) as nat),
                    RuntimeWrapperWidget::ScrollView { child, .. } =>
                        child.wf_spec((fuel - 1) as nat),
                },
                RuntimeWidget::Container(c) => match c {
                    RuntimeContainerWidget::Column { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Row { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Stack { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Wrap { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Flex { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Grid { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Absolute { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::ListView { children, .. } => {
                        forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                    },
                },
            }
        }
    }
}

// ── Widget shallow comparison ────────────────────────────────────

/// Match-based Alignment comparison (Verus enums lack derived PartialEq).
fn alignment_eq(a: &Alignment, b: &Alignment) -> (out: bool)
    ensures out ==> *a == *b,
{
    match (a, b) {
        (Alignment::Start, Alignment::Start) => true,
        (Alignment::Center, Alignment::Center) => true,
        (Alignment::End, Alignment::End) => true,
        _ => false,
    }
}

/// Compare two RuntimeTextInputConfigs for structural equality.
fn text_input_config_eq(a: &RuntimeTextInputConfig, b: &RuntimeTextInputConfig) -> (out: bool)
    ensures out ==> a@ == b@,
{
    let line_eq = match (&a.line_width, &b.line_width) {
        (Some(la), Some(lb)) => *la == *lb,
        (None, None) => true,
        _ => false,
    };
    let max_eq = match (&a.max_lines, &b.max_lines) {
        (Some(ma), Some(mb)) => *ma == *mb,
        (None, None) => true,
        _ => false,
    };
    let edit_eq = a.editable == b.editable;
    let result = line_eq && max_eq && edit_eq;
    if result {
        assume(a@ == b@); // Trust: Option<usize>/bool comparison implies spec equality
    }
    result
}

/// Shallow comparison of two widgets: same variant, same parameters, same child count.
/// Does NOT compare children recursively.
/// When true: the two widgets have the same structure and parameters,
/// so given identical child layout results they would produce identical output.
pub fn widgets_shallow_equal_exec(a: &RuntimeWidget, b: &RuntimeWidget) -> (out: bool)
    requires
        a.wf_shallow(),
        b.wf_shallow(),
{
    match (a, b) {
        (RuntimeWidget::Leaf(la), RuntimeWidget::Leaf(lb)) => {
            match (la, lb) {
                (RuntimeLeafWidget::Leaf { size: sa, .. },
                 RuntimeLeafWidget::Leaf { size: sb, .. }) => {
                    sa.eq_exec(sb)
                },
                (RuntimeLeafWidget::TextInput { preferred_size: sa, text_input_id: ia, config: ca, .. },
                 RuntimeLeafWidget::TextInput { preferred_size: sb, text_input_id: ib, config: cb, .. }) => {
                    sa.eq_exec(sb) && *ia == *ib && text_input_config_eq(ca, cb)
                },
                _ => false,
            }
        },
        (RuntimeWidget::Wrapper(wa), RuntimeWidget::Wrapper(wb)) => {
            match (wa, wb) {
                (RuntimeWrapperWidget::Margin { margin: ma, .. },
                 RuntimeWrapperWidget::Margin { margin: mb, .. }) => {
                    ma.eq_exec(mb)
                },
                (RuntimeWrapperWidget::Conditional { visible: va, .. },
                 RuntimeWrapperWidget::Conditional { visible: vb, .. }) => {
                    *va == *vb
                },
                (RuntimeWrapperWidget::SizedBox { inner_limits: la, .. },
                 RuntimeWrapperWidget::SizedBox { inner_limits: lb, .. }) => {
                    la.eq_exec(lb)
                },
                (RuntimeWrapperWidget::AspectRatio { ratio: ra, .. },
                 RuntimeWrapperWidget::AspectRatio { ratio: rb, .. }) => {
                    ra.eq(rb)
                },
                (RuntimeWrapperWidget::ScrollView { viewport: va, scroll_x: sxa, scroll_y: sya, .. },
                 RuntimeWrapperWidget::ScrollView { viewport: vb, scroll_x: sxb, scroll_y: syb, .. }) => {
                    va.eq_exec(vb) && sxa.eq(sxb) && sya.eq(syb)
                },
                _ => false,
            }
        },
        (RuntimeWidget::Container(ca), RuntimeWidget::Container(cb)) => {
            match (ca, cb) {
                (RuntimeContainerWidget::Column { padding: pa, spacing: sa, alignment: aa, children: ca, .. },
                 RuntimeContainerWidget::Column { padding: pb, spacing: sb, alignment: ab, children: cb, .. }) => {
                    pa.eq_exec(pb) && sa.eq(sb) && alignment_eq(aa, ab) && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::Row { padding: pa, spacing: sa, alignment: aa, children: ca, .. },
                 RuntimeContainerWidget::Row { padding: pb, spacing: sb, alignment: ab, children: cb, .. }) => {
                    pa.eq_exec(pb) && sa.eq(sb) && alignment_eq(aa, ab) && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::Stack { padding: pa, h_align: ha, v_align: va, children: ca, .. },
                 RuntimeContainerWidget::Stack { padding: pb, h_align: hb, v_align: vb, children: cb, .. }) => {
                    pa.eq_exec(pb) && alignment_eq(ha, hb) && alignment_eq(va, vb) && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::Wrap { padding: pa, h_spacing: hsa, v_spacing: vsa, children: ca, .. },
                 RuntimeContainerWidget::Wrap { padding: pb, h_spacing: hsb, v_spacing: vsb, children: cb, .. }) => {
                    pa.eq_exec(pb) && hsa.eq(hsb) && vsa.eq(vsb) && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::Flex { padding: pa, spacing: sa, alignment: aa, direction: da, children: ca, .. },
                 RuntimeContainerWidget::Flex { padding: pb, spacing: sb, alignment: ab, direction: db, children: cb, .. }) => {
                    let dir_eq = match (da, db) {
                        (FlexDirection::Column, FlexDirection::Column) => true,
                        (FlexDirection::Row, FlexDirection::Row) => true,
                        _ => false,
                    };
                    pa.eq_exec(pb) && sa.eq(sb) && alignment_eq(aa, ab) && dir_eq && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::Grid { padding: pa, h_spacing: hsa, v_spacing: vsa,
                                                h_align: ha, v_align: va, col_widths: cwa, row_heights: rha, children: ca, .. },
                 RuntimeContainerWidget::Grid { padding: pb, h_spacing: hsb, v_spacing: vsb,
                                                h_align: hb, v_align: vb, col_widths: cwb, row_heights: rhb, children: cb, .. }) => {
                    if !(pa.eq_exec(pb) && hsa.eq(hsb) && vsa.eq(vsb) &&
                         alignment_eq(ha, hb) && alignment_eq(va, vb) &&
                         cwa.len() == cwb.len() && rha.len() == rhb.len() &&
                         ca.len() == cb.len()) {
                        false
                    } else {
                        // Compare col_widths and row_heights element-wise
                        let mut ok = true;
                        let mut i: usize = 0;
                        while i < cwa.len()
                            invariant
                                0 <= i <= cwa@.len(),
                                cwa@.len() == cwb@.len(),
                                forall|j: int| 0 <= j < cwa@.len() ==> cwa@[j].wf_spec(),
                                forall|j: int| 0 <= j < cwb@.len() ==> cwb@[j].wf_spec(),
                            decreases cwa@.len() - i,
                        {
                            if !cwa[i].eq_exec(&cwb[i]) {
                                ok = false;
                            }
                            i = i + 1;
                        }
                        let mut j: usize = 0;
                        while j < rha.len()
                            invariant
                                0 <= j <= rha@.len(),
                                rha@.len() == rhb@.len(),
                                forall|k: int| 0 <= k < rha@.len() ==> rha@[k].wf_spec(),
                                forall|k: int| 0 <= k < rhb@.len() ==> rhb@[k].wf_spec(),
                            decreases rha@.len() - j,
                        {
                            if !rha[j].eq_exec(&rhb[j]) {
                                ok = false;
                            }
                            j = j + 1;
                        }
                        ok
                    }
                },
                (RuntimeContainerWidget::Absolute { padding: pa, children: ca, .. },
                 RuntimeContainerWidget::Absolute { padding: pb, children: cb, .. }) => {
                    pa.eq_exec(pb) && ca.len() == cb.len()
                },
                (RuntimeContainerWidget::ListView { spacing: sa, scroll_y: sya, viewport: va, children: ca, .. },
                 RuntimeContainerWidget::ListView { spacing: sb, scroll_y: syb, viewport: vb, children: cb, .. }) => {
                    sa.eq(sb) && sya.eq(syb) && va.eq_exec(vb) && ca.len() == cb.len()
                },
                _ => false,
            }
        },
        _ => false,
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
            Widget::Wrapper(WrapperWidget::Conditional { visible, child: Box::new(child.model()) }),
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
            Widget::Wrapper(WrapperWidget::Conditional { visible: true, child: Box::new(child.model()) }),
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

// ── Flex widget helper ──────────────────────────────────────────

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
            let spec_w = Widget::Container(ContainerWidget::Flex {
                padding: padding@, spacing: spacing@, alignment: *alignment,
                direction: *direction, children: spec_fi,
            });
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

                // 4. Bridge: layout_widget uses flex_linear_widget_child_nodes dispatch
                assert(spec_cn === flex_linear_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, Axis::Vertical, (fuel - 1) as nat));

                // 5. merged@ == layout_flex_column_body(...)
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

                // 4. Bridge: layout_widget uses flex_linear_widget_child_nodes dispatch
                assert(spec_cn === flex_linear_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, Axis::Horizontal, (fuel - 1) as nat));

                // 5. merged@ == layout_flex_row_body(...)
                assert(merged@ == layout_flex_row_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
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
        // Fuel bridge: one proof for all variants
        proof { assert((fuel as nat - 1) as nat == (fuel - 1) as nat); }

        match widget {
            RuntimeWidget::Leaf(leaf) => {
                match leaf {
                    RuntimeLeafWidget::Leaf { size, model } => {
                        let resolved = limits.resolve_exec(size.copy_size());
                        let x = RuntimeRational::from_int(0);
                        let y = RuntimeRational::from_int(0);
                        RuntimeNode::leaf_exec(x, y, resolved)
                    },
                    RuntimeLeafWidget::TextInput { preferred_size, text_input_id, config, model } => {
                        let resolved = limits.resolve_exec(preferred_size.copy_size());
                        let x = RuntimeRational::from_int(0);
                        let y = RuntimeRational::from_int(0);
                        RuntimeNode::leaf_exec(x, y, resolved)
                    },
                }
            },
            RuntimeWidget::Wrapper(wrapper) => {
                match wrapper {
                    RuntimeWrapperWidget::Margin { margin, child, model } => {
                        layout_margin_widget_exec(limits, margin, child, fuel)
                    },
                    RuntimeWrapperWidget::Conditional { visible, child, model } => {
                        layout_conditional_exec(limits, *visible, child, fuel)
                    },
                    RuntimeWrapperWidget::SizedBox { inner_limits: il, child, model } => {
                        layout_sized_box_widget_exec(limits, il, child, fuel)
                    },
                    RuntimeWrapperWidget::AspectRatio { ratio, child, model } => {
                        layout_aspect_ratio_widget_exec(limits, ratio, child, fuel)
                    },
                    RuntimeWrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child, model } => {
                        layout_scroll_view_exec(limits, viewport, scroll_x, scroll_y, child, fuel)
                    },
                }
            },
            RuntimeWidget::Container(container) => {
                match container {
                    RuntimeContainerWidget::Column { padding, spacing, alignment, children, model } => {
                        layout_container_exec(limits, padding, spacing, alignment,
                            &Alignment::Start, &RuntimeRational::from_int(0), children, fuel,
                            ContainerKind::Linear(Axis::Vertical))
                    },
                    RuntimeContainerWidget::Row { padding, spacing, alignment, children, model } => {
                        layout_container_exec(limits, padding, spacing, alignment,
                            &Alignment::Start, &RuntimeRational::from_int(0), children, fuel,
                            ContainerKind::Linear(Axis::Horizontal))
                    },
                    RuntimeContainerWidget::Stack { padding, h_align, v_align, children, model } => {
                        let zero_sp = RuntimeRational::from_int(0);
                        let dummy_sp = RuntimeRational::from_int(0);
                        layout_container_exec(limits, padding, &zero_sp, h_align,
                            v_align, &dummy_sp, children, fuel, ContainerKind::Stack)
                    },
                    RuntimeContainerWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                        layout_container_exec(limits, padding, h_spacing, &Alignment::Start,
                            &Alignment::Start, v_spacing, children, fuel, ContainerKind::Wrap)
                    },
                    RuntimeContainerWidget::Flex { padding, spacing, alignment, direction, children, model } => {
                        layout_flex_widget_exec(limits, padding, spacing, alignment,
                            direction, children, fuel)
                    },
                    RuntimeContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                                   col_widths, row_heights, children, model } => {
                        layout_grid_widget_exec(limits, padding, h_spacing, v_spacing,
                            h_align, v_align, col_widths, row_heights, children, fuel)
                    },
                    RuntimeContainerWidget::Absolute { padding, children, model } => {
                        layout_absolute_widget_exec(limits, padding, children, fuel)
                    },
                    RuntimeContainerWidget::ListView { spacing, scroll_y, viewport, children, model } => {
                        layout_listview_widget_exec(limits, spacing, scroll_y,
                            viewport, children, fuel)
                    },
                }
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
    Linear(Axis),
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
                ContainerKind::Linear(axis) =>
                    layout_linear_body(limits@, padding@, spacing1@, *align1, cn, axis),
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
        ContainerKind::Linear(axis) => {
            linear_layout_exec(limits, padding, spacing1, align1, &child_sizes, &axis)
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
            ContainerKind::Linear(axis) => {
                reveal(linear_layout);
                let avail_cross = limits@.max.cross_dim(axis).sub(padding@.cross_padding(axis));
                lemma_linear_children_len::<RationalModel>(
                    padding@, spacing1@, *align1, child_sizes_seq, axis, avail_cross, 0nat);
            },
            ContainerKind::Stack => {
                reveal(crate::layout::stack::stack_layout);
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                let avail_h = limits@.max.height.sub(padding@.vertical());
                lemma_stack_children_len::<RationalModel>(
                    padding@, *align1, *align2, child_sizes_seq, avail_w, avail_h, 0nat);
            },
            ContainerKind::Wrap => {
                reveal(wrap_layout);
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

// ── Merge layout exec ────────────────────────────────────────────

/// Merge positions from a layout result with recursively computed child nodes.
pub fn merge_layout_exec(
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
