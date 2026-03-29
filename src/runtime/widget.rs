use vstd::prelude::*;
use verus_rational::RuntimeRational;
#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;
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

///  Runtime flex child: weight + child widget.
pub struct RuntimeFlexItem {
    pub weight: RuntimeRational,
    pub child: RuntimeWidget,
}

///  Runtime absolute child: explicit (x, y) offset + child widget.
pub struct RuntimeAbsoluteChild {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub child: RuntimeWidget,
}

///  Runtime leaf widget: no children.
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

///  Runtime wrapper widget: exactly one child.
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

///  Runtime container widget: multiple children.
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

///  Runtime Widget: stratified to mirror spec Widget hierarchy.
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

//  ── Sub-enum impls ──────────────────────────────────────────────

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

//  ── RuntimeWidget delegation ────────────────────────────────────

impl RuntimeWidget {
    ///  Extract the ghost model.
    pub open spec fn model(&self) -> Widget<RationalModel> {
        match self {
            RuntimeWidget::Leaf(l) => Widget::Leaf(l.model()),
            RuntimeWidget::Wrapper(w) => Widget::Wrapper(w.model()),
            RuntimeWidget::Container(c) => Widget::Container(c.model()),
        }
    }

    ///  Shallow well-formedness: direct fields match model, no recursive child check.
    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeWidget::Leaf(l) => l.wf_shallow(),
            RuntimeWidget::Wrapper(w) => w.wf_shallow(),
            RuntimeWidget::Container(c) => c.wf_shallow(),
        }
    }

    ///  Full well-formedness at a given fuel depth.
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

    ///  Whether all Rational fields in this widget's model are in normalized (canonical) form.
    ///  When true and wf_shallow holds, comparing rational fields via eqv implies structural equality.
    pub open spec fn model_normalized(&self, fuel: nat) -> bool
        decreases fuel,
    {
        if fuel == 0 {
            false
        } else {
            &&& match self {
                RuntimeWidget::Leaf(l) => match l {
                    RuntimeLeafWidget::Leaf { size, .. } =>
                        size.width@.normalized_spec() && size.height@.normalized_spec(),
                    RuntimeLeafWidget::TextInput { preferred_size, .. } =>
                        preferred_size.width@.normalized_spec() && preferred_size.height@.normalized_spec(),
                },
                RuntimeWidget::Wrapper(w) => match w {
                    RuntimeWrapperWidget::Margin { margin, child, .. } =>
                        margin.top@.normalized_spec() && margin.right@.normalized_spec()
                        && margin.bottom@.normalized_spec() && margin.left@.normalized_spec()
                        && child.model_normalized((fuel - 1) as nat),
                    RuntimeWrapperWidget::Conditional { child, .. } =>
                        child.model_normalized((fuel - 1) as nat),
                    RuntimeWrapperWidget::SizedBox { inner_limits, child, .. } =>
                        inner_limits.min.width@.normalized_spec() && inner_limits.min.height@.normalized_spec()
                        && inner_limits.max.width@.normalized_spec() && inner_limits.max.height@.normalized_spec()
                        && child.model_normalized((fuel - 1) as nat),
                    RuntimeWrapperWidget::AspectRatio { ratio, child, .. } =>
                        ratio@.normalized_spec() && child.model_normalized((fuel - 1) as nat),
                    RuntimeWrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child, .. } =>
                        viewport.width@.normalized_spec() && viewport.height@.normalized_spec()
                        && scroll_x@.normalized_spec() && scroll_y@.normalized_spec()
                        && child.model_normalized((fuel - 1) as nat),
                },
                RuntimeWidget::Container(c) => match c {
                    RuntimeContainerWidget::Column { padding, spacing, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && spacing@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat),
                    RuntimeContainerWidget::Row { padding, spacing, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && spacing@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat),
                    RuntimeContainerWidget::Stack { padding, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat),
                    RuntimeContainerWidget::Wrap { padding, h_spacing, v_spacing, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && h_spacing@.normalized_spec() && v_spacing@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat),
                    RuntimeContainerWidget::Flex { padding, spacing, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && spacing@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==> {
                            &&& (#[trigger] children@[i]).weight@.normalized_spec()
                            &&& children@[i].child.model_normalized((fuel - 1) as nat)
                        },
                    RuntimeContainerWidget::Grid { padding, h_spacing, v_spacing, col_widths, row_heights, children, .. } => {
                        &&& padding.top@.normalized_spec() && padding.right@.normalized_spec()
                            && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        &&& h_spacing@.normalized_spec() && v_spacing@.normalized_spec()
                        &&& forall|i: int| 0 <= i < col_widths@.len() ==>
                            col_widths@[i].width@.normalized_spec() && col_widths@[i].height@.normalized_spec()
                        &&& forall|i: int| 0 <= i < row_heights@.len() ==>
                            row_heights@[i].width@.normalized_spec() && row_heights@[i].height@.normalized_spec()
                        &&& forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat)
                    },
                    RuntimeContainerWidget::Absolute { padding, children, .. } =>
                        padding.top@.normalized_spec() && padding.right@.normalized_spec()
                        && padding.bottom@.normalized_spec() && padding.left@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==> {
                            &&& (#[trigger] children@[i]).x@.normalized_spec()
                            &&& children@[i].y@.normalized_spec()
                            &&& children@[i].child.model_normalized((fuel - 1) as nat)
                        },
                    RuntimeContainerWidget::ListView { spacing, scroll_y, viewport, children, .. } =>
                        spacing@.normalized_spec() && scroll_y@.normalized_spec()
                        && viewport.width@.normalized_spec() && viewport.height@.normalized_spec()
                        && forall|i: int| 0 <= i < children@.len() ==>
                            (#[trigger] children@[i]).model_normalized((fuel - 1) as nat),
                },
            }
        }
    }
}

//  ── Widget shallow comparison ────────────────────────────────────

///  Match-based Alignment comparison (Verus enums lack derived PartialEq).
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

///  Match-based FlexDirection comparison.
fn flex_direction_eq(a: &FlexDirection, b: &FlexDirection) -> (out: bool)
    ensures out ==> *a == *b,
{
    match (a, b) {
        (FlexDirection::Column, FlexDirection::Column) => true,
        (FlexDirection::Row, FlexDirection::Row) => true,
        _ => false,
    }
}

///  Compare two RuntimeTextInputConfigs for structural equality.
///  Compare two Option<usize> values, proving spec equality when equal.
fn option_usize_eq(a: &Option<usize>, b: &Option<usize>) -> (out: bool)
    ensures out ==> match (a, b) {
        (Some(va), Some(vb)) => *va == *vb,
        (None, None) => true,
        _ => false,
    },
{
    match (a, b) {
        (Some(va), Some(vb)) => *va == *vb,
        (None, None) => true,
        _ => false,
    }
}

fn text_input_config_eq(a: &RuntimeTextInputConfig, b: &RuntimeTextInputConfig) -> (out: bool)
    ensures out ==> a@ == b@,
{
    let line_eq = option_usize_eq(&a.line_width, &b.line_width);
    let max_eq = option_usize_eq(&a.max_lines, &b.max_lines);
    let edit_eq = a.editable == b.editable;
    line_eq && max_eq && edit_eq
}

///  Shallow comparison of two widgets: same variant, same parameters, same child count.
///  Does NOT compare children recursively.
///  When true: the two widgets have the same structure and parameters,
///  so given identical child layout results they would produce identical output.
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
                        //  Compare col_widths and row_heights element-wise
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

//  ── Deep widget comparison ──────────────────────────────────────

///  Compare two Vec<RuntimeWidget> element-wise using deep comparison.
fn vec_widgets_deep_equal(a: &Vec<RuntimeWidget>, b: &Vec<RuntimeWidget>, depth: usize) -> (out: bool)
    requires
        a@.len() == b@.len(),
        depth > 0,
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).wf_spec(depth as nat),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).wf_spec(depth as nat),
    ensures
        (out && forall|i: int| 0 <= i < a@.len() ==> {
            (#[trigger] a@[i]).model_normalized(depth as nat)
            && b@[i].model_normalized(depth as nat)
        }) ==> forall|i: int| 0 <= i < a@.len() ==>
            (#[trigger] a@[i]).model() === b@[i].model(),
    decreases depth, 1nat,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.len() == b@.len(),
            depth > 0,
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).wf_spec(depth as nat),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).wf_spec(depth as nat),
            forall|j: int| 0 <= j < i ==> (
                a@[j].model_normalized(depth as nat) && b@[j].model_normalized(depth as nat)
            ) ==> (#[trigger] a@[j]).model() === b@[j].model(),
        decreases a@.len() - i,
    {
        if !widgets_deep_equal_exec(&a[i], &b[i], depth) {
            return false;
        }
        i = i + 1;
    }
    true
}

///  Compare two Vec<RuntimeFlexItem> element-wise: weights + child widgets.
fn vec_flex_deep_equal(a: &Vec<RuntimeFlexItem>, b: &Vec<RuntimeFlexItem>, depth: usize) -> (out: bool)
    requires
        a@.len() == b@.len(),
        depth > 0,
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).weight.wf_spec(),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).weight.wf_spec(),
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).child.wf_spec(depth as nat),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).child.wf_spec(depth as nat),
    ensures
        (out && forall|i: int| 0 <= i < a@.len() ==> {
            &&& (#[trigger] a@[i]).weight@.normalized_spec()
            &&& b@[i].weight@.normalized_spec()
            &&& a@[i].child.model_normalized(depth as nat)
            &&& b@[i].child.model_normalized(depth as nat)
        }) ==> forall|i: int| 0 <= i < a@.len() ==>
            (#[trigger] a@[i]).model() === b@[i].model(),
    decreases depth, 1nat,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.len() == b@.len(),
            depth > 0,
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).weight.wf_spec(),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).weight.wf_spec(),
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).child.wf_spec(depth as nat),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).child.wf_spec(depth as nat),
            forall|j: int| 0 <= j < i ==> (
                a@[j].weight@.normalized_spec() && b@[j].weight@.normalized_spec()
                && a@[j].child.model_normalized(depth as nat)
                && b@[j].child.model_normalized(depth as nat)
            ) ==> (#[trigger] a@[j]).model() === b@[j].model(),
        decreases a@.len() - i,
    {
        if !a[i].weight.eq(&b[i].weight) {
            return false;
        }
        if !widgets_deep_equal_exec(&a[i].child, &b[i].child, depth) {
            return false;
        }
        proof {
            if a@[i as int].weight@.normalized_spec()
                && b@[i as int].weight@.normalized_spec()
                && a@[i as int].child.model_normalized(depth as nat)
                && b@[i as int].child.model_normalized(depth as nat)
            {
                Rational::lemma_normalized_eqv_implies_equal(
                    a@[i as int].weight@, b@[i as int].weight@,
                );
                //  child model equality follows from widgets_deep_equal_exec ensures
                assert(a@[i as int].model() === b@[i as int].model());
            }
        }
        i = i + 1;
    }
    true
}

///  Compare two Vec<RuntimeAbsoluteChild> element-wise: offsets + child widgets.
fn vec_absolute_deep_equal(a: &Vec<RuntimeAbsoluteChild>, b: &Vec<RuntimeAbsoluteChild>, depth: usize) -> (out: bool)
    requires
        a@.len() == b@.len(),
        depth > 0,
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).x.wf_spec(),
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).y.wf_spec(),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).x.wf_spec(),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).y.wf_spec(),
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] a@[i]).child.wf_spec(depth as nat),
        forall|i: int| 0 <= i < b@.len() ==> (#[trigger] b@[i]).child.wf_spec(depth as nat),
    ensures
        (out && forall|i: int| 0 <= i < a@.len() ==> {
            &&& (#[trigger] a@[i]).x@.normalized_spec()
            &&& a@[i].y@.normalized_spec()
            &&& b@[i].x@.normalized_spec()
            &&& b@[i].y@.normalized_spec()
            &&& a@[i].child.model_normalized(depth as nat)
            &&& b@[i].child.model_normalized(depth as nat)
        }) ==> forall|i: int| 0 <= i < a@.len() ==>
            (#[trigger] a@[i]).model() === b@[i].model(),
    decreases depth, 1nat,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.len() == b@.len(),
            depth > 0,
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).x.wf_spec(),
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).y.wf_spec(),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).x.wf_spec(),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).y.wf_spec(),
            forall|j: int| 0 <= j < a@.len() ==> (#[trigger] a@[j]).child.wf_spec(depth as nat),
            forall|j: int| 0 <= j < b@.len() ==> (#[trigger] b@[j]).child.wf_spec(depth as nat),
            forall|j: int| 0 <= j < i ==> (
                a@[j].x@.normalized_spec() && a@[j].y@.normalized_spec()
                && b@[j].x@.normalized_spec() && b@[j].y@.normalized_spec()
                && a@[j].child.model_normalized(depth as nat)
                && b@[j].child.model_normalized(depth as nat)
            ) ==> (#[trigger] a@[j]).model() === b@[j].model(),
        decreases a@.len() - i,
    {
        if !a[i].x.eq(&b[i].x) || !a[i].y.eq(&b[i].y) {
            return false;
        }
        if !widgets_deep_equal_exec(&a[i].child, &b[i].child, depth) {
            return false;
        }
        proof {
            if a@[i as int].x@.normalized_spec()
                && a@[i as int].y@.normalized_spec()
                && b@[i as int].x@.normalized_spec()
                && b@[i as int].y@.normalized_spec()
                && a@[i as int].child.model_normalized(depth as nat)
                && b@[i as int].child.model_normalized(depth as nat)
            {
                Rational::lemma_normalized_eqv_implies_equal(
                    a@[i as int].x@, b@[i as int].x@,
                );
                Rational::lemma_normalized_eqv_implies_equal(
                    a@[i as int].y@, b@[i as int].y@,
                );
                assert(a@[i as int].model() === b@[i as int].model());
            }
        }
        i = i + 1;
    }
    true
}

///  Deep comparison of two widgets: same variant, same parameters, and
///  recursively equal children. Returns false conservatively when depth
///  is insufficient (non-leaf widgets need depth >= 2).
///  When true and both sides are model_normalized, the models are structurally equal.
pub fn widgets_deep_equal_exec(a: &RuntimeWidget, b: &RuntimeWidget, depth: usize) -> (out: bool)
    requires
        depth > 0,
        a.wf_spec(depth as nat),
        b.wf_spec(depth as nat),
    ensures
        (out && a.model_normalized(depth as nat) && b.model_normalized(depth as nat))
            ==> a.model() === b.model(),
    decreases depth, 0nat,
{
    //  Check shallow equality first (parameters + variant match + child count)
    if !widgets_shallow_equal_exec(a, b) {
        return false;
    }

    //  Parameters match. Now re-compare fields for proof evidence and recursively compare children.
    match (a, b) {
        //  ── Leaf variants ──────────────────────────────────────────
        (RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf { size: sa, .. }),
         RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf { size: sb, .. })) => {
            let size_eq = sa.eq_exec(sb);
            if !size_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(sa.width@, sb.width@);
                    Rational::lemma_normalized_eqv_implies_equal(sa.height@, sb.height@);
                    assert(sa@ == sb@);
                }
            }
            true
        },
        (RuntimeWidget::Leaf(RuntimeLeafWidget::TextInput { preferred_size: sa, text_input_id: ia, config: ca, .. }),
         RuntimeWidget::Leaf(RuntimeLeafWidget::TextInput { preferred_size: sb, text_input_id: ib, config: cb, .. })) => {
            let size_eq = sa.eq_exec(sb);
            if !size_eq { return false; }
            if *ia != *ib { return false; }
            let cfg_eq = text_input_config_eq(ca, cb);
            if !cfg_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(sa.width@, sb.width@);
                    Rational::lemma_normalized_eqv_implies_equal(sa.height@, sb.height@);
                    assert(sa@ == sb@);
                }
            }
            true
        },

        //  ── Wrapper variants ───────────────────────────────────────
        (RuntimeWidget::Wrapper(RuntimeWrapperWidget::Margin { margin: ma, child: ca, .. }),
         RuntimeWidget::Wrapper(RuntimeWrapperWidget::Margin { margin: mb, child: cb, .. })) => {
            if depth <= 1 { return false; }
            let pad_eq = ma.eq_exec(mb);
            if !pad_eq { return false; }
            let child_eq = widgets_deep_equal_exec(ca, cb, depth - 1);
            if !child_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(ma.top@, mb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(ma.right@, mb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(ma.bottom@, mb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(ma.left@, mb.left@);
                    assert(ma@ == mb@);
                }
            }
            true
        },
        (RuntimeWidget::Wrapper(RuntimeWrapperWidget::Conditional { visible: va, child: ca, .. }),
         RuntimeWidget::Wrapper(RuntimeWrapperWidget::Conditional { visible: vb, child: cb, .. })) => {
            if depth <= 1 { return false; }
            if *va != *vb { return false; }
            let child_eq = widgets_deep_equal_exec(ca, cb, depth - 1);
            if !child_eq { return false; }
            true
        },
        (RuntimeWidget::Wrapper(RuntimeWrapperWidget::SizedBox { inner_limits: la, child: ca, .. }),
         RuntimeWidget::Wrapper(RuntimeWrapperWidget::SizedBox { inner_limits: lb, child: cb, .. })) => {
            if depth <= 1 { return false; }
            let lim_eq = la.eq_exec(lb);
            if !lim_eq { return false; }
            let child_eq = widgets_deep_equal_exec(ca, cb, depth - 1);
            if !child_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(la.min.width@, lb.min.width@);
                    Rational::lemma_normalized_eqv_implies_equal(la.min.height@, lb.min.height@);
                    Rational::lemma_normalized_eqv_implies_equal(la.max.width@, lb.max.width@);
                    Rational::lemma_normalized_eqv_implies_equal(la.max.height@, lb.max.height@);
                    assert(la@ == lb@);
                }
            }
            true
        },
        (RuntimeWidget::Wrapper(RuntimeWrapperWidget::AspectRatio { ratio: ra, child: ca, .. }),
         RuntimeWidget::Wrapper(RuntimeWrapperWidget::AspectRatio { ratio: rb, child: cb, .. })) => {
            if depth <= 1 { return false; }
            let ratio_eq = ra.eq(rb);
            if !ratio_eq { return false; }
            let child_eq = widgets_deep_equal_exec(ca, cb, depth - 1);
            if !child_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(ra@, rb@);
                }
            }
            true
        },
        (RuntimeWidget::Wrapper(RuntimeWrapperWidget::ScrollView { viewport: va, scroll_x: sxa, scroll_y: sya, child: ca, .. }),
         RuntimeWidget::Wrapper(RuntimeWrapperWidget::ScrollView { viewport: vb, scroll_x: sxb, scroll_y: syb, child: cb, .. })) => {
            if depth <= 1 { return false; }
            let vp_eq = va.eq_exec(vb);
            if !vp_eq { return false; }
            let sx_eq = sxa.eq(sxb);
            if !sx_eq { return false; }
            let sy_eq = sya.eq(syb);
            if !sy_eq { return false; }
            let child_eq = widgets_deep_equal_exec(ca, cb, depth - 1);
            if !child_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(va.width@, vb.width@);
                    Rational::lemma_normalized_eqv_implies_equal(va.height@, vb.height@);
                    Rational::lemma_normalized_eqv_implies_equal(sxa@, sxb@);
                    Rational::lemma_normalized_eqv_implies_equal(sya@, syb@);
                    assert(va@ == vb@);
                }
            }
            true
        },

        //  ── Container variants ─────────────────────────────────────
        (RuntimeWidget::Container(RuntimeContainerWidget::Column {
            padding: pa, spacing: sa, alignment: aa, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Column {
            padding: pb, spacing: sb, alignment: ab, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let sp_eq = sa.eq(sb);
            if !sp_eq { return false; }
            let al_eq = alignment_eq(aa, ab);
            if !al_eq { return false; }
            if ca.len() != cb.len() { return false; }
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    Rational::lemma_normalized_eqv_implies_equal(sa@, sb@);
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Row {
            padding: pa, spacing: sa, alignment: aa, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Row {
            padding: pb, spacing: sb, alignment: ab, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let sp_eq = sa.eq(sb);
            if !sp_eq { return false; }
            let al_eq = alignment_eq(aa, ab);
            if !al_eq { return false; }
            if ca.len() != cb.len() { return false; }
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    Rational::lemma_normalized_eqv_implies_equal(sa@, sb@);
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Stack {
            padding: pa, h_align: ha, v_align: va, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Stack {
            padding: pb, h_align: hb, v_align: vb, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let ha_eq = alignment_eq(ha, hb);
            if !ha_eq { return false; }
            let va_eq = alignment_eq(va, vb);
            if !va_eq { return false; }
            if ca.len() != cb.len() { return false; }
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Wrap {
            padding: pa, h_spacing: hsa, v_spacing: vsa, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Wrap {
            padding: pb, h_spacing: hsb, v_spacing: vsb, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let hs_eq = hsa.eq(hsb);
            if !hs_eq { return false; }
            let vs_eq = vsa.eq(vsb);
            if !vs_eq { return false; }
            if ca.len() != cb.len() { return false; }
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    Rational::lemma_normalized_eqv_implies_equal(hsa@, hsb@);
                    Rational::lemma_normalized_eqv_implies_equal(vsa@, vsb@);
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Flex {
            padding: pa, spacing: sa, alignment: aa, direction: da, children: fa, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Flex {
            padding: pb, spacing: sb, alignment: ab, direction: db, children: fb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let sp_eq = sa.eq(sb);
            if !sp_eq { return false; }
            let al_eq = alignment_eq(aa, ab);
            if !al_eq { return false; }
            let dir_eq = flex_direction_eq(da, db);
            if !dir_eq { return false; }
            if fa.len() != fb.len() { return false; }
            let children_eq = vec_flex_deep_equal(fa, fb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    Rational::lemma_normalized_eqv_implies_equal(sa@, sb@);
                    let n = fa@.len() as nat;
                    assert(Seq::new(n, |i: int| fa@[i].model()) =~=
                           Seq::new(n, |i: int| fb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Grid {
            padding: pa, h_spacing: hsa, v_spacing: vsa,
            h_align: ha, v_align: va,
            col_widths: cwa, row_heights: rha, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Grid {
            padding: pb, h_spacing: hsb, v_spacing: vsb,
            h_align: hb, v_align: vb,
            col_widths: cwb, row_heights: rhb, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            let hs_eq = hsa.eq(hsb);
            if !hs_eq { return false; }
            let vs_eq = vsa.eq(vsb);
            if !vs_eq { return false; }
            let ha_eq = alignment_eq(ha, hb);
            if !ha_eq { return false; }
            let va_eq = alignment_eq(va, vb);
            if !va_eq { return false; }
            if cwa.len() != cwb.len() { return false; }
            if rha.len() != rhb.len() { return false; }
            if ca.len() != cb.len() { return false; }
            //  Capture normalization state as ghost booleans (avoids unfolding in loop invariants)
            let ghost cwa_norm: bool = forall|j: int| 0 <= j < cwa@.len() ==>
                cwa@[j].width@.normalized_spec() && cwa@[j].height@.normalized_spec();
            let ghost cwb_norm: bool = forall|j: int| 0 <= j < cwb@.len() ==>
                cwb@[j].width@.normalized_spec() && cwb@[j].height@.normalized_spec();
            let ghost rha_norm: bool = forall|j: int| 0 <= j < rha@.len() ==>
                rha@[j].width@.normalized_spec() && rha@[j].height@.normalized_spec();
            let ghost rhb_norm: bool = forall|j: int| 0 <= j < rhb@.len() ==>
                rhb@[j].width@.normalized_spec() && rhb@[j].height@.normalized_spec();
            //  Compare col_widths element-wise
            let mut ci: usize = 0;
            while ci < cwa.len()
                invariant
                    0 <= ci <= cwa@.len(),
                    cwa@.len() == cwb@.len(),
                    forall|j: int| 0 <= j < cwa@.len() ==> cwa@[j].wf_spec(),
                    forall|j: int| 0 <= j < cwb@.len() ==> cwb@[j].wf_spec(),
                    forall|j: int| 0 <= j < ci ==> (
                        cwa@[j].width@.normalized_spec() && cwa@[j].height@.normalized_spec()
                        && cwb@[j].width@.normalized_spec() && cwb@[j].height@.normalized_spec()
                    ) ==> cwa@[j]@ == cwb@[j]@,
                    cwa_norm ==> forall|j: int| 0 <= j < cwa@.len() ==>
                        cwa@[j].width@.normalized_spec() && cwa@[j].height@.normalized_spec(),
                    cwb_norm ==> forall|j: int| 0 <= j < cwb@.len() ==>
                        cwb@[j].width@.normalized_spec() && cwb@[j].height@.normalized_spec(),
                decreases cwa@.len() - ci,
            {
                if !cwa[ci].eq_exec(&cwb[ci]) { return false; }
                proof {
                    if cwa@[ci as int].width@.normalized_spec() && cwa@[ci as int].height@.normalized_spec()
                        && cwb@[ci as int].width@.normalized_spec() && cwb@[ci as int].height@.normalized_spec()
                    {
                        Rational::lemma_normalized_eqv_implies_equal(
                            cwa@[ci as int].width@, cwb@[ci as int].width@,
                        );
                        Rational::lemma_normalized_eqv_implies_equal(
                            cwa@[ci as int].height@, cwb@[ci as int].height@,
                        );
                    }
                }
                ci = ci + 1;
            }
            //  Compare row_heights element-wise
            let mut ri: usize = 0;
            while ri < rha.len()
                invariant
                    0 <= ri <= rha@.len(),
                    rha@.len() == rhb@.len(),
                    forall|j: int| 0 <= j < rha@.len() ==> rha@[j].wf_spec(),
                    forall|j: int| 0 <= j < rhb@.len() ==> rhb@[j].wf_spec(),
                    forall|j: int| 0 <= j < ri ==> (
                        rha@[j].width@.normalized_spec() && rha@[j].height@.normalized_spec()
                        && rhb@[j].width@.normalized_spec() && rhb@[j].height@.normalized_spec()
                    ) ==> rha@[j]@ == rhb@[j]@,
                    rha_norm ==> forall|j: int| 0 <= j < rha@.len() ==>
                        rha@[j].width@.normalized_spec() && rha@[j].height@.normalized_spec(),
                    rhb_norm ==> forall|j: int| 0 <= j < rhb@.len() ==>
                        rhb@[j].width@.normalized_spec() && rhb@[j].height@.normalized_spec(),
                decreases rha@.len() - ri,
            {
                if !rha[ri].eq_exec(&rhb[ri]) { return false; }
                proof {
                    if rha@[ri as int].width@.normalized_spec() && rha@[ri as int].height@.normalized_spec()
                        && rhb@[ri as int].width@.normalized_spec() && rhb@[ri as int].height@.normalized_spec()
                    {
                        Rational::lemma_normalized_eqv_implies_equal(
                            rha@[ri as int].width@, rhb@[ri as int].width@,
                        );
                        Rational::lemma_normalized_eqv_implies_equal(
                            rha@[ri as int].height@, rhb@[ri as int].height@,
                        );
                    }
                }
                ri = ri + 1;
            }
            //  Compare children
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    //  Unfold model_normalized for Grid: establishes normalization for all fields
                    //  a.model_normalized(depth) for Grid gives us:
                    //    pa normalized, hsa/vsa normalized, col_widths normalized, row_heights normalized,
                    //    children model_normalized at depth-1
                    //  Similarly for b.
                    assert(forall|j: int| 0 <= j < cwa@.len() ==>
                        cwa@[j].width@.normalized_spec() && cwa@[j].height@.normalized_spec());
                    assert(forall|j: int| 0 <= j < cwb@.len() ==>
                        cwb@[j].width@.normalized_spec() && cwb@[j].height@.normalized_spec());
                    assert(forall|j: int| 0 <= j < rha@.len() ==>
                        rha@[j].width@.normalized_spec() && rha@[j].height@.normalized_spec());
                    assert(forall|j: int| 0 <= j < rhb@.len() ==>
                        rhb@[j].width@.normalized_spec() && rhb@[j].height@.normalized_spec());
                    assert(forall|j: int| 0 <= j < ca@.len() ==>
                        (#[trigger] ca@[j]).model_normalized((depth - 1) as nat));
                    assert(forall|j: int| 0 <= j < cb@.len() ==>
                        (#[trigger] cb@[j]).model_normalized((depth - 1) as nat));

                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    Rational::lemma_normalized_eqv_implies_equal(hsa@, hsb@);
                    Rational::lemma_normalized_eqv_implies_equal(vsa@, vsb@);
                    //  col_widths extensional equality
                    assert forall|j: int| 0 <= j < cwa@.len() implies
                        cwa@[j]@ == cwb@[j]@
                    by {
                        assert(cwa@[j].width@.normalized_spec() && cwa@[j].height@.normalized_spec());
                        assert(cwb@[j].width@.normalized_spec() && cwb@[j].height@.normalized_spec());
                    }
                    let nc = cwa@.len() as nat;
                    assert(Seq::new(nc, |i: int| cwa@[i]@) =~=
                           Seq::new(nc, |i: int| cwb@[i]@));
                    //  row_heights extensional equality
                    assert forall|j: int| 0 <= j < rha@.len() implies
                        rha@[j]@ == rhb@[j]@
                    by {
                        assert(rha@[j].width@.normalized_spec() && rha@[j].height@.normalized_spec());
                        assert(rhb@[j].width@.normalized_spec() && rhb@[j].height@.normalized_spec());
                    }
                    let nr = rha@.len() as nat;
                    assert(Seq::new(nr, |i: int| rha@[i]@) =~=
                           Seq::new(nr, |i: int| rhb@[i]@));
                    //  children extensional equality
                    assert forall|j: int| 0 <= j < ca@.len() implies
                        ca@[j].model() === cb@[j].model()
                    by {
                        assert(ca@[j].model_normalized((depth - 1) as nat));
                        assert(cb@[j].model_normalized((depth - 1) as nat));
                    }
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::Absolute {
            padding: pa, children: aa, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::Absolute {
            padding: pb, children: ab, ..
        })) => {
            if depth <= 1 { return false; }
            let pad_eq = pa.eq_exec(pb);
            if !pad_eq { return false; }
            if aa.len() != ab.len() { return false; }
            let children_eq = vec_absolute_deep_equal(aa, ab, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(pa.top@, pb.top@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.right@, pb.right@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.bottom@, pb.bottom@);
                    Rational::lemma_normalized_eqv_implies_equal(pa.left@, pb.left@);
                    assert(pa@ == pb@);
                    let n = aa@.len() as nat;
                    assert(Seq::new(n, |i: int| aa@[i].model()) =~=
                           Seq::new(n, |i: int| ab@[i].model()));
                }
            }
            true
        },
        (RuntimeWidget::Container(RuntimeContainerWidget::ListView {
            spacing: sa, scroll_y: sya, viewport: va, children: ca, ..
        }),
         RuntimeWidget::Container(RuntimeContainerWidget::ListView {
            spacing: sb, scroll_y: syb, viewport: vb, children: cb, ..
        })) => {
            if depth <= 1 { return false; }
            let sp_eq = sa.eq(sb);
            if !sp_eq { return false; }
            let sy_eq = sya.eq(syb);
            if !sy_eq { return false; }
            let vp_eq = va.eq_exec(vb);
            if !vp_eq { return false; }
            if ca.len() != cb.len() { return false; }
            let children_eq = vec_widgets_deep_equal(ca, cb, depth - 1);
            if !children_eq { return false; }
            proof {
                if a.model_normalized(depth as nat) && b.model_normalized(depth as nat) {
                    Rational::lemma_normalized_eqv_implies_equal(sa@, sb@);
                    Rational::lemma_normalized_eqv_implies_equal(sya@, syb@);
                    Rational::lemma_normalized_eqv_implies_equal(va.width@, vb.width@);
                    Rational::lemma_normalized_eqv_implies_equal(va.height@, vb.height@);
                    assert(va@ == vb@);
                    let n = ca@.len() as nat;
                    assert(Seq::new(n, |i: int| ca@[i].model()) =~=
                           Seq::new(n, |i: int| cb@[i].model()));
                }
            }
            true
        },
        _ => false,
    }
}

//  ── Conditional widget helper ────────────────────────────────────

///  Layout a conditional widget: visible child or zero-sized leaf.
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

//  ── Flex widget helper ──────────────────────────────────────────

///  Layout a flex widget: each child gets per-weight limits.
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

    //  Compute weights and total_weight
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

    //  Compute total_spacing
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

    //  Recursively layout each child with per-weight limits, collecting child nodes + cross sizes
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

            //  Prove flex_column_layout_exec preconditions
            proof {
                assert(Seq::new(weights@.len() as nat, |i: int| weights@[i]@)
                    =~= spec_weights);
                assert forall|j: int| 0 <= j < cross_sizes@.len() implies
                    (#[trigger] cross_sizes@[j]).wf_spec()
                by {}
            }
            let layout_result = flex_column_layout_exec(
                limits, padding, spacing, alignment, &weights, &cross_sizes);

            //  Merge — layout_result.children@.len() == n from flex_column_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            //  Connect merged result to spec layout_widget
            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_column_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                //  1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                //  2. Cross sizes view matches what layout_flex_column_body computes
                let cross_view: Seq<RationalModel> =
                    Seq::new(cross_sizes@.len() as nat, |i: int| cross_sizes@[i]@);
                let spec_cross: Seq<RationalModel> =
                    Seq::new(spec_cn.len(), |i: int| spec_cn[i].size.width);
                assert(cross_view =~= spec_cross) by {
                    assert(cross_view.len() == spec_cross.len());
                    assert forall|j: int| 0 <= j < cross_view.len() as int implies
                        cross_view[j] == spec_cross[j]
                    by {
                        //  cross_sizes@[j]@ == child_nodes@[j]@.size.width == cn_models[j].size.width == spec_cn[j].size.width
                    }
                }

                //  3. Weights from spec_fi match spec_weights
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

                //  4. Bridge: layout_widget uses flex_linear_widget_child_nodes dispatch
                assert(spec_cn === flex_linear_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, Axis::Vertical, (fuel - 1) as nat));

                //  5. merged@ == layout_flex_column_body(...)
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

            //  Merge — layout_result.children@.len() == n from flex_row_layout_exec postcondition
            let ghost cn_models: Seq<Node<RationalModel>> =
                Seq::new(n as nat, |j: int| child_nodes@[j]@);
            let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

            proof {
                let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
                let spec_cn = flex_row_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, (fuel - 1) as nat);

                //  1. cn_models =~= spec_cn
                assert(cn_models.len() == spec_cn.len());
                assert forall|j: int| 0 <= j < cn_models.len() as int implies
                    cn_models[j] == spec_cn[j]
                by {
                    let fi_j = spec_fi[j];
                    assert(fi_j == children@[j].model());
                    assert(fi_j.child == children@[j].child.model());
                }
                assert(cn_models =~= spec_cn);

                //  2. Cross sizes view matches
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

                //  3. Weights from spec_fi match
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

                //  4. Bridge: layout_widget uses flex_linear_widget_child_nodes dispatch
                assert(spec_cn === flex_linear_widget_child_nodes(
                    inner_spec, spec_fi, spec_weights, total_weight@,
                    avail_spec, Axis::Horizontal, (fuel - 1) as nat));

                //  5. merged@ == layout_flex_row_body(...)
                assert(merged@ == layout_flex_row_body::<RationalModel>(
                    limits@, padding@, spacing@, *alignment, spec_weights_fi, spec_cn));
            }

            merged
        },
    }
}

//  ── Layout widget exec ───────────────────────────────────────────

///  Recursively lay out a RuntimeWidget tree.
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
        //  Unreachable: wf_spec(0) is false
        let z1 = RuntimeRational::from_int(0);
        let z2 = RuntimeRational::from_int(0);
        RuntimeNode::leaf_exec(z1, z2, RuntimeSize::zero_exec())
    } else {
        //  Fuel bridge: one proof for all variants
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

///  Layout with verified children-within-bounds guarantee.
///  Wraps `layout_widget_exec` and calls `lemma_layout_widget_cwb` in a proof block
///  to establish that all children are positioned within the parent's bounds.
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

///  Which layout strategy to use.
pub enum ContainerKind {
    Linear(Axis),
    Stack,
    Wrap,
}

///  Shared container layout: recursively compute children, call layout exec, merge.
fn layout_container_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing1: &RuntimeRational,  //  spacing (col/row), h_spacing (wrap), unused (stack)
    align1: &Alignment,          //  alignment (row), h_align (stack), unused (col/wrap)
    align2: &Alignment,          //  alignment (col), v_align (stack), unused (row/wrap)
    spacing2: &RuntimeRational,  //  v_spacing (wrap), unused (col/row/stack)
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

    //  Ghost: spec-level children sequence
    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |j: int| children@[j].model());

    //  1. Recursively compute child nodes
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_wc.len() == n as nat,
            //  Pointwise Seq::new unfolding (ghost let not available in loop)
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

    //  Assert child_sizes wf for layout exec preconditions
    proof {
        assert forall|j: int| 0 <= j < child_sizes@.len() implies
            (#[trigger] child_sizes@[j]).wf_spec()
        by {
            //  From loop invariant: child_sizes@[j].wf_spec() for j < i == n
        }
    }

    //  2. Call the appropriate layout exec
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

    //  Prove layout_result has n children (needed for merge precondition)
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

    //  3. Merge positions from layout_result with child_nodes
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);

    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    //  4. Connect to spec
    proof {
        let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
        let spec_cn = widget_child_nodes(inner_spec, spec_wc, (fuel - 1) as nat);

        //  Show cn_models == spec_cn via extensional equality
        assert(cn_models.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < cn_models.len() as int implies
            cn_models[j] == spec_cn[j]
        by {
            //  cn_models[j] = child_nodes@[j]@ = layout_widget(inner@, spec_wc[j], fuel-1)
            //  spec_cn[j] = layout_widget(inner_spec, spec_wc[j], fuel-1)
            //  inner@ == inner_spec, so they're equal
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

//  ── Merge layout exec ────────────────────────────────────────────

///  Merge positions from a layout result with recursively computed child nodes.
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
            //  Pointwise merge_layout unfolding (ghost let not available in loop)
            forall|j: int| 0 <= j < n ==>
                (#[trigger] merged_model.children[j]) == (Node::<RationalModel> {
                    x: layout_result@.children[j].x,
                    y: layout_result@.children[j].y,
                    size: spec_cn[j].size,
                    children: spec_cn[j].children,
                }),
            //  Elements [i..n) still original
            forall|j: int| i as int <= j < n as int ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == spec_cn[j]
            },
            //  Merged elements match model
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] merged_children@[j]).wf_shallow()
                &&& merged_children@[j]@ == merged_model.children[j]
            },
        decreases n - i,
    {
        let x = copy_rational(&layout_result.children[i].x);
        let y = copy_rational(&layout_result.children[i].y);

        //  Capture facts about child_nodes[i] before the swap
        proof {
            assert(child_nodes@[i as int].wf_spec());
            assert(child_nodes@[i as int]@ == spec_cn[i as int]);
        }

        //  Swap child_nodes[i] with a dummy to take ownership
        let mut swap_val = RuntimeNode::leaf_exec(
            RuntimeRational::from_int(0),
            RuntimeRational::from_int(0),
            RuntimeSize::zero_exec(),
        );
        child_nodes.set_and_swap(i, &mut swap_val);
        let cn = swap_val;

        //  Construct ghost model directly from components
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
            //  child_model == merged_model.children[i] from pointwise invariant
            assert(child_model == merged_model.children[i as int]);
            //  wf_shallow: fields match model
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

//  ── Widget normalization ─────────────────────────────────────────

///  Normalize a Vec<RuntimeFlexItem> using set_and_swap.
fn normalize_flex_vec_exec(mut items: Vec<RuntimeFlexItem>, fuel: usize) -> (out: Vec<RuntimeFlexItem>)
    requires
        items@.len() > 0 ==> fuel > 0,
        forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).weight.wf_spec(),
        forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).child.wf_spec(fuel as nat),
    ensures
        out@.len() == items@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).weight.wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).weight@.normalized_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).child.wf_spec(fuel as nat),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).child.model_normalized(fuel as nat),
        //  Weight eqv preservation: each normalized weight is eqv to the original
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).weight@.eqv_spec(items@[i].weight@),
    decreases fuel, 2nat,
{
    let ghost orig = items@;
    let n = items.len();
    let mut result: Vec<RuntimeFlexItem> = Vec::new();
    let dw = RuntimeRational::from_int(0);
    let mut dummy = RuntimeFlexItem {
        weight: dw,
        child: make_dummy_widget(),
    };
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, n == orig.len(), result@.len() == i as int, n > 0 ==> fuel > 0,
            forall|j: int| i <= j < n ==> (#[trigger] items@[j]).weight.wf_spec(),
            forall|j: int| i <= j < n ==> (#[trigger] items@[j]).child.wf_spec(fuel as nat),
            //  Items not yet processed retain original weight models
            forall|j: int| i <= j < n ==> items@[j].weight@ == orig[j].weight@,
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).weight.wf_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).weight@.normalized_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).child.wf_spec(fuel as nat),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).child.model_normalized(fuel as nat),
            //  Weight eqv tracking
            forall|j: int| 0 <= j < i ==>
                (#[trigger] result@[j]).weight@.eqv_spec(orig[j].weight@),
            items@.len() == n,
        decreases n - i,
    {
        items.set_and_swap(i, &mut dummy);
        let wn = dummy.weight.normalize();
        let cn = normalize_widget_exec(dummy.child, fuel);
        proof {
            //  wn@ eqv dummy.weight@ == orig[i].weight@ (from set_and_swap + invariant)
            //  normalize ensures: wn@.eqv_spec(dummy.weight@)
            //  dummy.weight@ == items@[i].weight@ (before swap) == orig[i].weight@
        }
        result.push(RuntimeFlexItem { weight: wn, child: cn });
        dummy = RuntimeFlexItem { weight: RuntimeRational::from_int(0), child: make_dummy_widget() };
        i = i + 1;
    }
    result
}

///  Normalize a Vec<RuntimeAbsoluteChild> using set_and_swap.
fn normalize_absolute_vec_exec(mut items: Vec<RuntimeAbsoluteChild>, fuel: usize) -> (out: Vec<RuntimeAbsoluteChild>)
    requires
        items@.len() > 0 ==> fuel > 0,
        forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).x.wf_spec(),
        forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).y.wf_spec(),
        forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).child.wf_spec(fuel as nat),
    ensures
        out@.len() == items@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).x.wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).x@.normalized_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).y.wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).y@.normalized_spec(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).child.wf_spec(fuel as nat),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).child.model_normalized(fuel as nat),
    decreases fuel, 2nat,
{
    let n = items.len();
    let mut result: Vec<RuntimeAbsoluteChild> = Vec::new();
    let mut dummy = RuntimeAbsoluteChild {
        x: RuntimeRational::from_int(0),
        y: RuntimeRational::from_int(0),
        child: make_dummy_widget(),
    };
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, n == items@.len(), result@.len() == i as int, n > 0 ==> fuel > 0,
            forall|j: int| i <= j < n ==> (#[trigger] items@[j]).x.wf_spec(),
            forall|j: int| i <= j < n ==> (#[trigger] items@[j]).y.wf_spec(),
            forall|j: int| i <= j < n ==> (#[trigger] items@[j]).child.wf_spec(fuel as nat),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).x.wf_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).x@.normalized_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).y.wf_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).y@.normalized_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).child.wf_spec(fuel as nat),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).child.model_normalized(fuel as nat),
            items@.len() == n,
        decreases n - i,
    {
        items.set_and_swap(i, &mut dummy);
        let xn = dummy.x.normalize();
        let yn = dummy.y.normalize();
        let cn = normalize_widget_exec(dummy.child, fuel);
        result.push(RuntimeAbsoluteChild { x: xn, y: yn, child: cn });
        dummy = RuntimeAbsoluteChild {
            x: RuntimeRational::from_int(0), y: RuntimeRational::from_int(0),
            child: make_dummy_widget(),
        };
        i = i + 1;
    }
    result
}

///  Normalize a Vec<RuntimeSize> (for Grid col_widths/row_heights).
fn normalize_size_vec_exec(mut sizes: Vec<RuntimeSize>) -> (out: Vec<RuntimeSize>)
    requires
        forall|i: int| 0 <= i < sizes@.len() ==> (#[trigger] sizes@[i]).wf_spec(),
    ensures
        out@.len() == sizes@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==> {
            (#[trigger] out@[i]).width@.normalized_spec()
            && out@[i].height@.normalized_spec()
        },
{
    let n = sizes.len();
    let mut result: Vec<RuntimeSize> = Vec::new();
    let mut dummy = RuntimeSize::zero_exec();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, n == sizes@.len(), result@.len() == i as int,
            forall|j: int| i <= j < n ==> (#[trigger] sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < i ==> {
                (#[trigger] result@[j]).width@.normalized_spec()
                && result@[j].height@.normalized_spec()
            },
            sizes@.len() == n,
        decreases n - i,
    {
        sizes.set_and_swap(i, &mut dummy);
        let sn = dummy.normalize_exec();
        result.push(sn);
        dummy = RuntimeSize::zero_exec();
        i = i + 1;
    }
    result
}

///  Create a dummy RuntimeWidget for set_and_swap operations.
fn make_dummy_widget() -> (out: RuntimeWidget)
{
    let s = RuntimeSize::zero_exec();
    RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf {
        size: s,
        model: Ghost(LeafWidget::Leaf { size: Size::zero_size() }),
    })
}

///  Normalize all RuntimeRational fields in a Vec of widgets using set_and_swap.
fn normalize_widget_vec_exec(mut widgets: Vec<RuntimeWidget>, fuel: usize) -> (out: Vec<RuntimeWidget>)
    requires
        widgets@.len() > 0 ==> fuel > 0,
        forall|i: int| 0 <= i < widgets@.len() ==>
            (#[trigger] widgets@[i]).wf_spec(fuel as nat),
    ensures
        out@.len() == widgets@.len(),
        forall|i: int| 0 <= i < out@.len() ==> {
            &&& (#[trigger] out@[i]).wf_spec(fuel as nat)
            &&& out@[i].model_normalized(fuel as nat)
        },
    decreases fuel, 2nat,
{
    let ghost orig = widgets@;
    let n = widgets.len();
    let mut result: Vec<RuntimeWidget> = Vec::new();
    let mut dummy = make_dummy_widget();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == orig.len(),
            widgets@.len() == n,
            result@.len() == i as int,
            n > 0 ==> fuel > 0,
            forall|j: int| i <= j < n ==>
                (#[trigger] widgets@[j]).wf_spec(fuel as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] result@[j]).wf_spec(fuel as nat)
                &&& result@[j].model_normalized(fuel as nat)
            },
        decreases n - i,
    {
        widgets.set_and_swap(i, &mut dummy);
        let normalized = normalize_widget_exec(dummy, fuel);
        result.push(normalized);
        dummy = make_dummy_widget();
        i = i + 1;
    }
    result
}

///  Normalize all RuntimeRational fields in a widget tree.
///  Produces a widget with `model_normalized(fuel)` — all rational Ghost models
///  are in canonical (normalized) form.
pub fn normalize_widget_exec(widget: RuntimeWidget, fuel: usize) -> (out: RuntimeWidget)
    requires
        fuel > 0,
        widget.wf_spec(fuel as nat),
    ensures
        out.wf_spec(fuel as nat),
        out.model_normalized(fuel as nat),
    decreases fuel, 1nat,
{
    match widget {
        RuntimeWidget::Leaf(leaf) => normalize_leaf_exec(leaf, Ghost(fuel as nat)),
        RuntimeWidget::Wrapper(wrapper) => normalize_wrapper_exec(wrapper, fuel),
        RuntimeWidget::Container(container) => normalize_container_exec(container, fuel),
    }
}

///  Normalize a leaf widget's rational fields.
fn normalize_leaf_exec(leaf: RuntimeLeafWidget, fuel: Ghost<nat>) -> (out: RuntimeWidget)
    requires leaf.wf_shallow(), fuel@ > 0,
    ensures out.wf_spec(fuel@), out.model_normalized(fuel@),
{
    match leaf {
            RuntimeLeafWidget::Leaf { size, .. } => {
                let sn = size.normalize_exec();
                RuntimeWidget::Leaf(RuntimeLeafWidget::Leaf {
                    size: sn,
                    model: Ghost(LeafWidget::Leaf { size: sn@ }),
                })
            },
            RuntimeLeafWidget::TextInput { preferred_size, text_input_id, config, .. } => {
                let psn = preferred_size.normalize_exec();
                RuntimeWidget::Leaf(RuntimeLeafWidget::TextInput {
                    preferred_size: psn,
                    text_input_id,
                    config,
                    model: Ghost(LeafWidget::TextInput {
                        preferred_size: psn@,
                        text_input_id: text_input_id as nat,
                        config: config@,
                    }),
                })
            },
    }
}

///  Normalize a wrapper widget's rational fields.
fn normalize_wrapper_exec(wrapper: RuntimeWrapperWidget, fuel: usize) -> (out: RuntimeWidget)
    requires fuel > 0, RuntimeWidget::Wrapper(wrapper).wf_spec(fuel as nat),
    ensures out.wf_spec(fuel as nat), out.model_normalized(fuel as nat),
    decreases fuel, 0nat,
{
    match wrapper {
            RuntimeWrapperWidget::Margin { margin, child, .. } => {
                assert(child.wf_spec((fuel - 1) as nat)); //  from widget.wf_spec(fuel) unfolding
                let mn = margin.normalize_exec();
                let cn = normalize_widget_exec(*child, fuel - 1);
                RuntimeWidget::Wrapper(RuntimeWrapperWidget::Margin {
                    margin: mn,
                    child: Box::new(cn),
                    model: Ghost(WrapperWidget::Margin {
                        margin: mn@,
                        child: Box::new(cn.model()),
                    }),
                })
            },
            RuntimeWrapperWidget::Conditional { visible, child, .. } => {
                assert(child.wf_spec((fuel - 1) as nat));
                let cn = normalize_widget_exec(*child, fuel - 1);
                RuntimeWidget::Wrapper(RuntimeWrapperWidget::Conditional {
                    visible,
                    child: Box::new(cn),
                    model: Ghost(WrapperWidget::Conditional {
                        visible,
                        child: Box::new(cn.model()),
                    }),
                })
            },
            RuntimeWrapperWidget::SizedBox { inner_limits, child, .. } => {
                assert(child.wf_spec((fuel - 1) as nat));
                let ln = inner_limits.normalize_exec();
                let cn = normalize_widget_exec(*child, fuel - 1);
                RuntimeWidget::Wrapper(RuntimeWrapperWidget::SizedBox {
                    inner_limits: ln,
                    child: Box::new(cn),
                    model: Ghost(WrapperWidget::SizedBox {
                        inner_limits: ln@,
                        child: Box::new(cn.model()),
                    }),
                })
            },
            RuntimeWrapperWidget::AspectRatio { ratio, child, .. } => {
                assert(child.wf_spec((fuel - 1) as nat));
                let rn = ratio.normalize();
                let cn = normalize_widget_exec(*child, fuel - 1);
                RuntimeWidget::Wrapper(RuntimeWrapperWidget::AspectRatio {
                    ratio: rn,
                    child: Box::new(cn),
                    model: Ghost(WrapperWidget::AspectRatio {
                        ratio: rn@,
                        child: Box::new(cn.model()),
                    }),
                })
            },
            RuntimeWrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child, .. } => {
                assert(child.wf_spec((fuel - 1) as nat));
                let vn = viewport.normalize_exec();
                let sxn = scroll_x.normalize();
                let syn = scroll_y.normalize();
                let cn = normalize_widget_exec(*child, fuel - 1);
                RuntimeWidget::Wrapper(RuntimeWrapperWidget::ScrollView {
                    viewport: vn,
                    scroll_x: sxn,
                    scroll_y: syn,
                    child: Box::new(cn),
                    model: Ghost(WrapperWidget::ScrollView {
                        viewport: vn@,
                        scroll_x: sxn@,
                        scroll_y: syn@,
                        child: Box::new(cn.model()),
                    }),
                })
            },
    }
}

///  Normalize a container widget's rational fields.
fn normalize_container_exec(container: RuntimeContainerWidget, fuel: usize) -> (out: RuntimeWidget)
    requires fuel > 0, RuntimeWidget::Container(container).wf_spec(fuel as nat),
    ensures out.wf_spec(fuel as nat), out.model_normalized(fuel as nat),
    decreases fuel, 0nat,
{
    match container {
            RuntimeContainerWidget::Column { padding, spacing, alignment, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let sn = spacing.normalize();
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Column {
                    padding: pn, spacing: sn, alignment, children: cn,
                    model: Ghost(ContainerWidget::Column {
                        padding: pn@, spacing: sn@, alignment,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Row { padding, spacing, alignment, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let sn = spacing.normalize();
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Row {
                    padding: pn, spacing: sn, alignment, children: cn,
                    model: Ghost(ContainerWidget::Row {
                        padding: pn@, spacing: sn@, alignment,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Stack { padding, h_align, v_align, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Stack {
                    padding: pn, h_align, v_align, children: cn,
                    model: Ghost(ContainerWidget::Stack {
                        padding: pn@, h_align, v_align,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Wrap { padding, h_spacing, v_spacing, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let hsn = h_spacing.normalize();
                let vsn = v_spacing.normalize();
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Wrap {
                    padding: pn, h_spacing: hsn, v_spacing: vsn, children: cn,
                    model: Ghost(ContainerWidget::Wrap {
                        padding: pn@, h_spacing: hsn@, v_spacing: vsn@,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::ListView { spacing, scroll_y, viewport, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let sn = spacing.normalize();
                let syn = scroll_y.normalize();
                let vn = viewport.normalize_exec();
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::ListView {
                    spacing: sn, scroll_y: syn, viewport: vn, children: cn,
                    model: Ghost(ContainerWidget::ListView {
                        spacing: sn@, scroll_y: syn@, viewport: vn@,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Flex { padding, spacing, alignment, direction, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].child.wf_spec((fuel - 1) as nat)); }
                //  Capture original weights before normalization
                let ghost orig_weights = Seq::new(children@.len() as nat, |i: int| children@[i].weight@);
                let pn = padding.normalize_exec();
                let sn = spacing.normalize();
                let cn = normalize_flex_vec_exec(children, fuel - 1);
                //  sum_weights of normalized weights is eqv to original sum
                //  (each weight eqv-preserves through normalize, and add is congruent)
                //  This ensures the nonzero sum condition carries over.
                let ghost new_weights = Seq::new(cn@.len() as nat, |i: int| cn@[i].weight@);
                proof {
                    if cn@.len() > 0 {
                        //  The original wf_spec guarantees !sum_weights(orig, n).eqv(0)
                        //  normalized weights are eqv to original weights
                        //  sum_weights is congruent → new sum eqv to old sum
                        //  So new sum is also not eqv to 0.
                        //  Z3 needs help: assert the nonzero sum for normalized weights
                        assert(!sum_weights::<RationalModel>(
                            orig_weights, orig_weights.len() as nat,
                        ).eqv_spec(RationalModel::from_int_spec(0)));
                        //  The normalized weights are eqv to original (from normalize ensures)
                        //  sum_weights congruence: proved in congruence_proofs
                        //  For now, help Z3 with the conclusion:
                        //  cn@[i].weight@ eqv orig_weights[i] (from vec helper ensures)
                        //  sum_weights congruence + original nonzero → normalized nonzero
                        crate::layout::congruence_proofs::lemma_sum_weights_congruence(
                            new_weights, orig_weights, new_weights.len() as nat);
                        //  new_sum eqv orig_sum. orig_sum not eqv 0.
                        //  If new_sum eqv 0, then orig_sum eqv new_sum eqv 0 → contradiction.
                        RationalModel::lemma_eqv_symmetric(
                            sum_weights::<RationalModel>(new_weights, new_weights.len() as nat),
                            sum_weights::<RationalModel>(orig_weights, orig_weights.len() as nat));
                        if sum_weights::<RationalModel>(new_weights, new_weights.len() as nat)
                            .eqv_spec(RationalModel::from_int_spec(0))
                        {
                            RationalModel::lemma_eqv_transitive(
                                sum_weights::<RationalModel>(orig_weights, orig_weights.len() as nat),
                                sum_weights::<RationalModel>(new_weights, new_weights.len() as nat),
                                RationalModel::from_int_spec(0));
                            assert(false);
                        }
                    }
                }
                RuntimeWidget::Container(RuntimeContainerWidget::Flex {
                    padding: pn, spacing: sn, alignment, direction, children: cn,
                    model: Ghost(ContainerWidget::Flex {
                        padding: pn@, spacing: sn@, alignment, direction,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                                           col_widths, row_heights, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let hsn = h_spacing.normalize();
                let vsn = v_spacing.normalize();
                let cwn = normalize_size_vec_exec(col_widths);
                let rhn = normalize_size_vec_exec(row_heights);
                let cn = normalize_widget_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Grid {
                    padding: pn, h_spacing: hsn, v_spacing: vsn, h_align, v_align,
                    col_widths: cwn, row_heights: rhn, children: cn,
                    model: Ghost(ContainerWidget::Grid {
                        padding: pn@, h_spacing: hsn@, v_spacing: vsn@, h_align, v_align,
                        col_widths: Seq::new(cwn@.len() as nat, |i: int| cwn@[i]@),
                        row_heights: Seq::new(rhn@.len() as nat, |i: int| rhn@[i]@),
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
            RuntimeContainerWidget::Absolute { padding, children, .. } => {
                assert(forall|i: int| 0 <= i < children@.len() ==> (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat));
                if children.len() > 0 { assert(children@[0].child.wf_spec((fuel - 1) as nat)); }
                let pn = padding.normalize_exec();
                let cn = normalize_absolute_vec_exec(children, fuel - 1);
                RuntimeWidget::Container(RuntimeContainerWidget::Absolute {
                    padding: pn, children: cn,
                    model: Ghost(ContainerWidget::Absolute {
                        padding: pn@,
                        children: Seq::new(cn@.len() as nat, |i: int| cn@[i].model()),
                    }),
                })
            },
    }
}

} //  verus!
