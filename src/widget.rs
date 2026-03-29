use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::Alignment;
use crate::layout::*;
use crate::layout::stack::*;
use crate::layout::flex::*;
use crate::layout::grid::*;
use crate::layout::wrap::*;
use crate::layout::absolute::*;
use crate::layout::listview::*;
use crate::text_input::TextInputConfig;

verus! {

///  Flex layout direction.
pub enum FlexDirection {
    Column,
    Row,
}

impl FlexDirection {
    ///  Convert flex direction to layout axis.
    pub open spec fn axis(self) -> Axis {
        match self {
            FlexDirection::Column => Axis::Vertical,
            FlexDirection::Row => Axis::Horizontal,
        }
    }
}

///  A flex child with a weight.
#[verifier::reject_recursive_types(T)]
pub struct FlexItem<T: OrderedRing> {
    pub weight: T,
    pub child: Widget<T>,
}

///  An absolutely-positioned child with explicit (x, y) offset.
#[verifier::reject_recursive_types(T)]
pub struct AbsoluteChild<T: OrderedRing> {
    pub x: T,
    pub y: T,
    pub child: Widget<T>,
}

///  Leaf widgets: no children, size determined by content or configuration.
#[verifier::reject_recursive_types(T)]
pub enum LeafWidget<T: OrderedRing> {
    Leaf { size: Size<T> },
    TextInput { preferred_size: Size<T>, text_input_id: nat, config: TextInputConfig },
}

///  Wrapper widgets: exactly one child, modified layout constraints.
#[verifier::reject_recursive_types(T)]
pub enum WrapperWidget<T: OrderedRing> {
    Margin { margin: Padding<T>, child: Box<Widget<T>> },
    Conditional { visible: bool, child: Box<Widget<T>> },
    SizedBox { inner_limits: Limits<T>, child: Box<Widget<T>> },
    AspectRatio { ratio: T, child: Box<Widget<T>> },
    ScrollView { viewport: Size<T>, scroll_x: T, scroll_y: T, child: Box<Widget<T>> },
}

///  Container widgets: multiple children with layout strategy.
#[allow(inconsistent_fields)]
#[verifier::reject_recursive_types(T)]
pub enum ContainerWidget<T: OrderedRing> {
    Column { padding: Padding<T>, spacing: T, alignment: Alignment, children: Seq<Widget<T>> },
    Row { padding: Padding<T>, spacing: T, alignment: Alignment, children: Seq<Widget<T>> },
    Stack { padding: Padding<T>, h_align: Alignment, v_align: Alignment, children: Seq<Widget<T>> },
    Wrap { padding: Padding<T>, h_spacing: T, v_spacing: T, children: Seq<Widget<T>> },
    Flex { padding: Padding<T>, spacing: T, alignment: Alignment, direction: FlexDirection, children: Seq<FlexItem<T>> },
    Grid { padding: Padding<T>, h_spacing: T, v_spacing: T, h_align: Alignment, v_align: Alignment,
           col_widths: Seq<Size<T>>, row_heights: Seq<Size<T>>, children: Seq<Widget<T>> },
    Absolute { padding: Padding<T>, children: Seq<AbsoluteChild<T>> },
    ListView { spacing: T, scroll_y: T, viewport: Size<T>, children: Seq<Widget<T>> },
}

///  A composable layout widget that can nest heterogeneous layout strategies.
///  Split into Leaf/Wrapper/Container sub-enums for efficient dispatch.
#[verifier::reject_recursive_types(T)]
pub enum Widget<T: OrderedRing> {
    Leaf(LeafWidget<T>),
    Wrapper(WrapperWidget<T>),
    Container(ContainerWidget<T>),
}

//  ── Convenience constructors ──────────────────────────────────────

///  Center a single child (stack with center alignment, no padding).
pub open spec fn center_widget<T: OrderedRing>(child: Widget<T>) -> Widget<T> {
    Widget::Container(ContainerWidget::Stack {
        padding: Padding { top: T::zero(), right: T::zero(), bottom: T::zero(), left: T::zero() },
        h_align: Alignment::Center,
        v_align: Alignment::Center,
        children: Seq::empty().push(child),
    })
}

///  Align a single child with explicit h/v alignment (stack wrapper).
pub open spec fn align_widget<T: OrderedRing>(h: Alignment, v: Alignment, child: Widget<T>) -> Widget<T> {
    Widget::Container(ContainerWidget::Stack {
        padding: Padding { top: T::zero(), right: T::zero(), bottom: T::zero(), left: T::zero() },
        h_align: h,
        v_align: v,
        children: Seq::empty().push(child),
    })
}

//  ── Variant body helpers ───────────────────────────────────────────
//  Extracted from layout_widget to enable shallow unfolding in proofs.

///  Column layout body: given pre-computed child nodes, run column_layout and merge.
pub open spec fn layout_column_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = column_layout(limits, padding, spacing, alignment, child_sizes);
    merge_layout(layout, child_nodes)
}

///  Row layout body.
pub open spec fn layout_row_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = row_layout(limits, padding, spacing, alignment, child_sizes);
    merge_layout(layout, child_nodes)
}

///  Unified linear layout body: axis-parameterized column/row.
pub open spec fn layout_linear_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    child_nodes: Seq<Node<T>>,
    axis: Axis,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = linear_layout(limits, padding, spacing, alignment, child_sizes, axis);
    merge_layout(layout, child_nodes)
}

///  Stack layout body.
pub open spec fn layout_stack_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_align: Alignment,
    v_align: Alignment,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = stack_layout(limits, padding, h_align, v_align, child_sizes);
    merge_layout(layout, child_nodes)
}

///  Wrap layout body.
pub open spec fn layout_wrap_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let layout = wrap_layout(limits, padding, h_spacing, v_spacing, child_sizes);
    merge_layout(layout, child_nodes)
}

///  Flex column layout body: given pre-computed child nodes, run flex_column_layout and merge.
///  Cross-axis = width for column direction.
pub open spec fn layout_flex_column_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_cross_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size.width);
    let layout = flex_column_layout(limits, padding, spacing, alignment, weights, child_cross_sizes);
    merge_layout(layout, child_nodes)
}

///  Flex row layout body. Cross-axis = height for row direction.
pub open spec fn layout_flex_row_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let child_cross_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size.height);
    let layout = flex_row_layout(limits, padding, spacing, alignment, weights, child_cross_sizes);
    merge_layout(layout, child_nodes)
}

///  Flex linear layout body (axis-parameterized): dispatches to column/row body based on axis.
pub open spec fn layout_flex_linear_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    weights: Seq<T>,
    child_nodes: Seq<Node<T>>,
    axis: Axis,
) -> Node<T> {
    match axis {
        Axis::Vertical => layout_flex_column_body(limits, padding, spacing, alignment, weights, child_nodes),
        Axis::Horizontal => layout_flex_row_body(limits, padding, spacing, alignment, weights, child_nodes),
    }
}

///  Grid layout body: given pre-computed child nodes (flat, row-major), run grid_layout and merge.
pub open spec fn layout_grid_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    h_align: Alignment,
    v_align: Alignment,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    let num_cols = col_widths.len();
    let num_rows = row_heights.len();
    let child_sizes_2d = Seq::new(num_rows, |r: int|
        Seq::new(num_cols, |c: int|
            child_nodes[(r * num_cols as int + c)].size
        )
    );
    let layout = grid_layout(limits, padding, h_spacing, v_spacing, h_align, v_align,
        col_widths, row_heights, child_sizes_2d);
    merge_layout(layout, child_nodes)
}

///  Absolute layout body: given pre-computed child nodes and offsets, run absolute_layout.
///  No merge needed — absolute_layout positions children directly at their offsets.
pub open spec fn layout_absolute_body<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    child_nodes: Seq<Node<T>>,
    child_offsets: Seq<(T, T)>,
) -> Node<T> {
    let child_sizes = Seq::new(child_nodes.len(), |i: int| child_nodes[i].size);
    let child_data = Seq::new(child_nodes.len(), |i: int|
        (child_offsets[i].0, child_offsets[i].1, child_nodes[i].size));
    let layout = absolute_layout(limits, padding, child_data);
    merge_layout(layout, child_nodes)
}

///  Compute child nodes from children widgets at a given fuel.
pub open spec fn widget_child_nodes<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 2nat,
{
    Seq::new(children.len(), |i: int| layout_widget(inner_limits, children[i], fuel))
}

///  Compute child nodes for a flex column: each child gets per-weight limits.
pub open spec fn flex_column_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_height: T,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 2nat,
{
    Seq::new(children.len(), |i: int| {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_height);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(inner.max.width, main_alloc),
        };
        layout_widget(child_lim, children[i].child, fuel)
    })
}

///  Compute child nodes for a flex row: each child gets per-weight limits.
pub open spec fn flex_row_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_width: T,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 2nat,
{
    Seq::new(children.len(), |i: int| {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_width);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(main_alloc, inner.max.height),
        };
        layout_widget(child_lim, children[i].child, fuel)
    })
}

///  Compute child nodes for a flex linear layout (axis-parameterized).
///  Dispatches to column/row widget child nodes based on axis.
pub open spec fn flex_linear_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_main: T,
    axis: Axis,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 3nat,
{
    match axis {
        Axis::Vertical => flex_column_widget_child_nodes(
            inner, children, weights, total_weight, available_main, fuel,
        ),
        Axis::Horizontal => flex_row_widget_child_nodes(
            inner, children, weights, total_weight, available_main, fuel,
        ),
    }
}

///  Compute child nodes for a grid: each child gets cell-sized limits.
pub open spec fn grid_widget_child_nodes<T: OrderedField>(
    inner: Limits<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    children: Seq<Widget<T>>,
    num_cols: nat,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 2nat,
{
    Seq::new(children.len(), |i: int| {
        let r = i / num_cols as int;
        let c = i % num_cols as int;
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(col_widths[c].width, row_heights[r].height),
        };
        layout_widget(child_lim, children[i], fuel)
    })
}

///  Compute child nodes for absolute layout: each child uses the same inner limits.
pub open spec fn absolute_widget_child_nodes<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<AbsoluteChild<T>>,
    fuel: nat,
) -> Seq<Node<T>>
    decreases fuel, 2nat,
{
    Seq::new(children.len(), |i: int| layout_widget(inner_limits, children[i].child, fuel))
}

//  ── Main layout function ───────────────────────────────────────────

///  Recursively lay out a widget tree, producing a positioned Node tree.
///
///  Uses fuel-based recursion (fuel must exceed tree depth).
pub open spec fn layout_widget<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
) -> Node<T>
    decreases fuel, 1nat,
{
    if fuel == 0 {
        Node {
            x: T::zero(),
            y: T::zero(),
            size: Size::new(T::zero(), T::zero()),
            children: Seq::empty(),
        }
    } else {
        match widget {
            Widget::Leaf(leaf) => layout_leaf(limits, leaf),
            Widget::Wrapper(wrapper) => layout_wrapper(limits, wrapper, fuel),
            Widget::Container(container) => layout_container(limits, container, fuel),
        }
    }
}

///  Lay out a leaf widget (no children).
pub open spec fn layout_leaf<T: OrderedField>(
    limits: Limits<T>,
    leaf: LeafWidget<T>,
) -> Node<T> {
    match leaf {
        LeafWidget::Leaf { size } => {
            Node {
                x: T::zero(),
                y: T::zero(),
                size: limits.resolve(size),
                children: Seq::empty(),
            }
        },
        LeafWidget::TextInput { preferred_size, .. } => {
            Node {
                x: T::zero(),
                y: T::zero(),
                size: limits.resolve(preferred_size),
                children: Seq::empty(),
            }
        },
    }
}

///  Lay out a wrapper widget (single child).
pub open spec fn layout_wrapper<T: OrderedField>(
    limits: Limits<T>,
    wrapper: WrapperWidget<T>,
    fuel: nat,
) -> Node<T>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Node { x: T::zero(), y: T::zero(), size: Size::new(T::zero(), T::zero()), children: Seq::empty() }
    } else {
        match wrapper {
            WrapperWidget::Margin { margin, child } => {
                let inner = limits.shrink(margin.horizontal(), margin.vertical());
                let child_node = layout_widget(inner, *child, (fuel - 1) as nat);
                let total_w = margin.horizontal().add(child_node.size.width);
                let total_h = margin.vertical().add(child_node.size.height);
                let parent_size = limits.resolve(Size::new(total_w, total_h));
                Node {
                    x: T::zero(),
                    y: T::zero(),
                    size: parent_size,
                    children: Seq::empty().push(Node {
                        x: margin.left,
                        y: margin.top,
                        size: child_node.size,
                        children: child_node.children,
                    }),
                }
            },
            WrapperWidget::Conditional { visible, child } => {
                if visible {
                    let child_node = layout_widget(limits, *child, (fuel - 1) as nat);
                    Node {
                        x: T::zero(),
                        y: T::zero(),
                        size: limits.resolve(child_node.size),
                        children: child_node.children,
                    }
                } else {
                    Node {
                        x: T::zero(),
                        y: T::zero(),
                        size: limits.resolve(Size::zero_size()),
                        children: Seq::empty(),
                    }
                }
            },
            WrapperWidget::SizedBox { inner_limits, child } => {
                let effective = limits.intersect(inner_limits);
                let child_node = layout_widget(effective, *child, (fuel - 1) as nat);
                Node {
                    x: T::zero(),
                    y: T::zero(),
                    size: limits.resolve(child_node.size),
                    children: Seq::empty().push(Node {
                        x: T::zero(),
                        y: T::zero(),
                        size: child_node.size,
                        children: child_node.children,
                    }),
                }
            },
            WrapperWidget::AspectRatio { ratio, child } => {
                let w1 = limits.max.width;
                let h1 = w1.div(ratio);
                let child_node = if h1.le(limits.max.height) {
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w1, h1),
                    };
                    layout_widget(eff, *child, (fuel - 1) as nat)
                } else {
                    let h2 = limits.max.height;
                    let w2 = h2.mul(ratio);
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w2, h2),
                    };
                    layout_widget(eff, *child, (fuel - 1) as nat)
                };
                Node {
                    x: T::zero(),
                    y: T::zero(),
                    size: limits.resolve(child_node.size),
                    children: Seq::empty().push(Node {
                        x: T::zero(),
                        y: T::zero(),
                        size: child_node.size,
                        children: child_node.children,
                    }),
                }
            },
            WrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child } => {
                let child_limits = Limits {
                    min: Size::zero_size(),
                    max: viewport,
                };
                let child_node = layout_widget(child_limits, *child, (fuel - 1) as nat);
                Node {
                    x: T::zero(),
                    y: T::zero(),
                    size: limits.resolve(viewport),
                    children: Seq::empty().push(Node {
                        x: scroll_x.neg(),
                        y: scroll_y.neg(),
                        size: child_node.size,
                        children: child_node.children,
                    }),
                }
            },
        }
    }
}

///  Lay out a container widget (multiple children).
pub open spec fn layout_container<T: OrderedField>(
    limits: Limits<T>,
    container: ContainerWidget<T>,
    fuel: nat,
) -> Node<T>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Node { x: T::zero(), y: T::zero(), size: Size::new(T::zero(), T::zero()), children: Seq::empty() }
    } else {
        match container {
            ContainerWidget::Column { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_linear_body(limits, padding, spacing, alignment, cn, Axis::Vertical)
            },
            ContainerWidget::Row { padding, spacing, alignment, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_linear_body(limits, padding, spacing, alignment, cn, Axis::Horizontal)
            },
            ContainerWidget::Stack { padding, h_align, v_align, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_stack_body(limits, padding, h_align, v_align, cn)
            },
            ContainerWidget::Wrap { padding, h_spacing, v_spacing, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                layout_wrap_body(limits, padding, h_spacing, v_spacing, cn)
            },
            ContainerWidget::Flex { padding, spacing, alignment, direction, children } => {
                let axis = direction.axis();
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let weights = Seq::new(children.len(), |i: int| children[i].weight);
                let total_weight = sum_weights(weights, weights.len() as nat);
                let total_spacing = if children.len() > 0 {
                    repeated_add(spacing, (children.len() - 1) as nat)
                } else { T::zero() };
                let available_main = inner.max.main_dim(axis).sub(total_spacing);
                let cn = flex_linear_widget_child_nodes(
                    inner, children, weights, total_weight,
                    available_main, axis, (fuel - 1) as nat,
                );
                layout_flex_linear_body(
                    limits, padding, spacing, alignment, weights, cn, axis,
                )
            },
            ContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                           col_widths, row_heights, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = grid_widget_child_nodes(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), (fuel - 1) as nat,
                );
                layout_grid_body(
                    limits, padding, h_spacing, v_spacing, h_align, v_align,
                    col_widths, row_heights, cn,
                )
            },
            ContainerWidget::Absolute { padding, children } => {
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
                let offsets = Seq::new(children.len(), |i: int|
                    (children[i].x, children[i].y));
                layout_absolute_body(limits, padding, cn, offsets)
            },
            ContainerWidget::ListView { spacing, scroll_y, viewport, children } => {
                let child_limits = Limits {
                    min: Size::zero_size(),
                    max: Size::new(viewport.width, viewport.height),
                };
                let child_sizes = crate::measure::measure_children(
                    child_limits, children, (fuel - 1) as nat);
                let first = listview_first_visible(child_sizes, spacing, scroll_y);
                let end = listview_end_visible(child_sizes, spacing, scroll_y, viewport.height);
                let cn = listview_widget_child_nodes(
                    child_limits, children, first, end, (fuel - 1) as nat,
                );
                layout_listview_body(limits, child_sizes, spacing, scroll_y, viewport, cn, first)
            },
        }
    }
}

///  Merge positions from a layout result with recursively-computed child Nodes.
pub open spec fn merge_layout<T: OrderedRing>(
    layout: Node<T>,
    child_nodes: Seq<Node<T>>,
) -> Node<T> {
    Node {
        x: layout.x,
        y: layout.y,
        size: layout.size,
        children: Seq::new(child_nodes.len(), |i: int| Node {
            x: layout.children[i].x,
            y: layout.children[i].y,
            size: child_nodes[i].size,
            children: child_nodes[i].children,
        }),
    }
}

//  ── Widget depth and canonical entry point ─────────────────────────

///  Extract the children sequence from any Widget variant.
pub open spec fn get_children<T: OrderedRing>(widget: Widget<T>) -> Seq<Widget<T>> {
    match widget {
        Widget::Leaf(_) => Seq::empty(),
        Widget::Wrapper(wrapper) => match wrapper {
            WrapperWidget::Margin { child, .. } => Seq::empty().push(*child),
            WrapperWidget::Conditional { child, .. } => Seq::empty().push(*child),
            WrapperWidget::SizedBox { child, .. } => Seq::empty().push(*child),
            WrapperWidget::AspectRatio { child, .. } => Seq::empty().push(*child),
            WrapperWidget::ScrollView { child, .. } => Seq::empty().push(*child),
        },
        Widget::Container(container) => match container {
            ContainerWidget::Column { children, .. } => children,
            ContainerWidget::Row { children, .. } => children,
            ContainerWidget::Stack { children, .. } => children,
            ContainerWidget::Wrap { children, .. } => children,
            ContainerWidget::Flex { children, .. } =>
                Seq::new(children.len(), |i: int| children[i].child),
            ContainerWidget::Grid { children, .. } => children,
            ContainerWidget::Absolute { children, .. } =>
                Seq::new(children.len(), |i: int| children[i].child),
            ContainerWidget::ListView { children, .. } => children,
        },
    }
}

///  Max widget_depth across children[0..count].
pub open spec fn max_child_widget_depth<T: OrderedRing>(
    children: Seq<Widget<T>>,
    fuel: nat,
    count: nat,
) -> nat
    decreases fuel, count,
{
    if count == 0 {
        0
    } else {
        let prev = max_child_widget_depth(children, fuel, (count - 1) as nat);
        let cur = widget_depth(children[(count - 1) as int], fuel);
        if cur >= prev { cur } else { prev }
    }
}

///  Compute the depth of a widget tree (fuel-bounded).
pub open spec fn widget_depth<T: OrderedRing>(widget: Widget<T>, fuel: nat) -> nat
    decreases fuel, 0nat,
{
    if fuel == 0 {
        0
    } else {
        let children = get_children(widget);
        if children.len() == 0 {
            0
        } else {
            1 + max_child_widget_depth(children, (fuel - 1) as nat, children.len())
        }
    }
}

///  Canonical entry point: lay out a widget with sufficient fuel.
pub open spec fn layout_widget_full<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel_bound: nat,
) -> Node<T> {
    layout_widget(limits, widget, widget_depth(widget, fuel_bound) + 1)
}

//  ── Fuel convergence ───────────────────────────────────────────────

///  Whether the widget tree has converged at the given fuel level.
///
///  A leaf always converges (at fuel >= 1). A container converges when
///  all its children have converged at fuel-1.
pub open spec fn widget_converged<T: OrderedRing>(widget: Widget<T>, fuel: nat) -> bool
    decreases fuel,
{
    if fuel == 0 {
        false
    } else {
        let children = get_children(widget);
        if children.len() == 0 {
            true
        } else {
            forall|i: int| 0 <= i < children.len() ==>
                widget_converged(children[i], (fuel - 1) as nat)
        }
    }
}

///  Extra fuel doesn't change child_nodes when children have converged.
proof fn lemma_child_nodes_fuel_monotone<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel),
    ensures
        widget_child_nodes(inner_limits, children, fuel)
            == widget_child_nodes(inner_limits, children, fuel + 1),
    decreases fuel, 1nat,
{
    assert forall|i: int| 0 <= i < children.len() implies
        layout_widget(inner_limits, children[i], fuel)
        == layout_widget(inner_limits, children[i], fuel + 1)
    by {
        lemma_layout_widget_fuel_monotone(inner_limits, children[i], fuel);
    }
    assert(widget_child_nodes(inner_limits, children, fuel)
        =~= widget_child_nodes(inner_limits, children, fuel + 1));
}

///  Flex column child nodes are fuel-monotone.
proof fn lemma_flex_column_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_height: T,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel)
            == flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel + 1),
    decreases fuel, 1nat,
{
    let ghost old_cn = flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel);
    let ghost new_cn = flex_column_widget_child_nodes(inner, children, weights, total_weight, available_height, fuel + 1);
    assert forall|i: int| 0 <= i < children.len() implies
        #[trigger] old_cn[i] == #[trigger] new_cn[i]
    by {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_height);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(inner.max.width, main_alloc),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i].child, fuel);
    }
    assert(old_cn =~= new_cn);
}

///  Flex row child nodes are fuel-monotone.
proof fn lemma_flex_row_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_width: T,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel)
            == flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel + 1),
    decreases fuel, 1nat,
{
    let ghost old_cn = flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel);
    let ghost new_cn = flex_row_widget_child_nodes(inner, children, weights, total_weight, available_width, fuel + 1);
    assert forall|i: int| 0 <= i < children.len() implies
        #[trigger] old_cn[i] == #[trigger] new_cn[i]
    by {
        let main_alloc = flex_child_main_size(weights[i], total_weight, available_width);
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(main_alloc, inner.max.height),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i].child, fuel);
    }
    assert(old_cn =~= new_cn);
}

///  Flex linear child nodes are fuel-monotone (axis-parameterized).
proof fn lemma_flex_linear_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    children: Seq<FlexItem<T>>,
    weights: Seq<T>,
    total_weight: T,
    available_main: T,
    axis: Axis,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        flex_linear_widget_child_nodes(inner, children, weights, total_weight, available_main, axis, fuel)
            == flex_linear_widget_child_nodes(inner, children, weights, total_weight, available_main, axis, fuel + 1),
    decreases fuel, 2nat,
{
    match axis {
        Axis::Vertical => {
            lemma_flex_column_child_nodes_fuel_monotone(
                inner, children, weights, total_weight, available_main, fuel,
            );
        },
        Axis::Horizontal => {
            lemma_flex_row_child_nodes_fuel_monotone(
                inner, children, weights, total_weight, available_main, fuel,
            );
        },
    }
}

///  Absolute child nodes are fuel-monotone.
proof fn lemma_absolute_child_nodes_fuel_monotone<T: OrderedField>(
    inner_limits: Limits<T>,
    children: Seq<AbsoluteChild<T>>,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i].child, fuel),
    ensures
        absolute_widget_child_nodes(inner_limits, children, fuel)
            == absolute_widget_child_nodes(inner_limits, children, fuel + 1),
    decreases fuel, 1nat,
{
    let ghost old_cn = absolute_widget_child_nodes(inner_limits, children, fuel);
    let ghost new_cn = absolute_widget_child_nodes(inner_limits, children, fuel + 1);
    assert forall|i: int| 0 <= i < children.len() implies
        #[trigger] old_cn[i] == #[trigger] new_cn[i]
    by {
        lemma_layout_widget_fuel_monotone(inner_limits, children[i].child, fuel);
    }
    assert(old_cn =~= new_cn);
}

///  Grid child nodes are fuel-monotone.
proof fn lemma_grid_child_nodes_fuel_monotone<T: OrderedField>(
    inner: Limits<T>,
    col_widths: Seq<Size<T>>,
    row_heights: Seq<Size<T>>,
    children: Seq<Widget<T>>,
    num_cols: nat,
    fuel: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel),
    ensures
        grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel)
            == grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel + 1),
    decreases fuel, 1nat,
{
    //  Prove each child layout is unchanged by extra fuel
    let ghost old_cn = grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel);
    let ghost new_cn = grid_widget_child_nodes(inner, col_widths, row_heights, children, num_cols, fuel + 1);
    assert forall|i: int| 0 <= i < children.len() implies
        #[trigger] old_cn[i] == #[trigger] new_cn[i]
    by {
        let r = i / num_cols as int;
        let c = i % num_cols as int;
        let child_lim = Limits {
            min: inner.min,
            max: Size::new(col_widths[c].width, row_heights[r].height),
        };
        lemma_layout_widget_fuel_monotone(child_lim, children[i], fuel);
    }
    assert(old_cn =~= new_cn);
}

///  Extra fuel doesn't change the result when the widget has converged.
pub proof fn lemma_layout_widget_fuel_monotone<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires
        widget_converged(widget, fuel),
    ensures
        layout_widget(limits, widget, fuel) == layout_widget(limits, widget, fuel + 1),
    decreases fuel, 0nat,
{
    //  widget_converged(widget, fuel) implies fuel >= 1
    assert(fuel >= 1nat);
    match widget {
        Widget::Leaf(_) => {},
        Widget::Wrapper(wrapper) => match wrapper {
            WrapperWidget::Margin { margin, child } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::empty().push(*child));
                assert(widget_converged(*child, (fuel - 1) as nat)) by {
                    assert(gc[0] == *child);
                }
                let inner = limits.shrink(margin.horizontal(), margin.vertical());
                lemma_layout_widget_fuel_monotone(inner, *child, (fuel - 1) as nat);
            },
            WrapperWidget::Conditional { visible, child } => {
                if visible {
                    let gc = get_children(widget);
                    assert(gc =~= Seq::empty().push(*child));
                    assert(widget_converged(*child, (fuel - 1) as nat)) by {
                        assert(gc[0] == *child);
                    }
                    lemma_layout_widget_fuel_monotone(limits, *child, (fuel - 1) as nat);
                } else {
                    //  !visible: no recursion, both fuel levels produce same zero-size leaf
                }
            },
            WrapperWidget::SizedBox { inner_limits, child } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::empty().push(*child));
                assert(widget_converged(*child, (fuel - 1) as nat)) by {
                    assert(gc[0] == *child);
                }
                let effective = limits.intersect(inner_limits);
                lemma_layout_widget_fuel_monotone(effective, *child, (fuel - 1) as nat);
            },
            WrapperWidget::AspectRatio { ratio, child } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::empty().push(*child));
                assert(widget_converged(*child, (fuel - 1) as nat)) by {
                    assert(gc[0] == *child);
                }
                let w1 = limits.max.width;
                let h1 = w1.div(ratio);
                if h1.le(limits.max.height) {
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w1, h1),
                    };
                    lemma_layout_widget_fuel_monotone(eff, *child, (fuel - 1) as nat);
                } else {
                    let h2 = limits.max.height;
                    let w2 = h2.mul(ratio);
                    let eff = Limits {
                        min: limits.min,
                        max: Size::new(w2, h2),
                    };
                    lemma_layout_widget_fuel_monotone(eff, *child, (fuel - 1) as nat);
                }
            },
            WrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::empty().push(*child));
                assert(widget_converged(*child, (fuel - 1) as nat)) by {
                    assert(gc[0] == *child);
                }
                let child_limits = Limits {
                    min: Size::zero_size(),
                    max: viewport,
                };
                lemma_layout_widget_fuel_monotone(child_limits, *child, (fuel - 1) as nat);
            },
        },
        Widget::Container(container) => match container {
            ContainerWidget::Column { padding, spacing, alignment, children } => {
                assert(get_children(widget) =~= children);
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
                }
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                assert(cn =~= widget_child_nodes(inner, children, fuel));
            },
            ContainerWidget::Row { padding, spacing, alignment, children } => {
                assert(get_children(widget) =~= children);
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
                }
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                assert(cn =~= widget_child_nodes(inner, children, fuel));
            },
            ContainerWidget::Stack { padding, h_align, v_align, children } => {
                assert(get_children(widget) =~= children);
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
                }
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                assert(cn =~= widget_child_nodes(inner, children, fuel));
            },
            ContainerWidget::Wrap { padding, h_spacing, v_spacing, children } => {
                assert(get_children(widget) =~= children);
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
                }
                let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
                assert(cn =~= widget_child_nodes(inner, children, fuel));
            },
            ContainerWidget::Flex { padding, spacing, alignment, direction, children } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::new(children.len(), |i: int| children[i].child));
                assert forall|i: int| 0 <= i < children.len() implies
                    widget_converged(#[trigger] children[i].child, (fuel - 1) as nat)
                by {
                    assert(gc[i] == children[i].child);
                }
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                let weights = Seq::new(children.len(), |i: int| children[i].weight);
                let total_weight = sum_weights(weights, weights.len() as nat);
                let total_spacing = if children.len() > 0 {
                    repeated_add(spacing, (children.len() - 1) as nat)
                } else { T::zero() };

                let axis = direction.axis();
                let am = inner.max.main_dim(axis).sub(total_spacing);
                if children.len() > 0 {
                    lemma_flex_linear_child_nodes_fuel_monotone(
                        inner, children, weights, total_weight, am, axis, (fuel - 1) as nat);
                }
                let cn = flex_linear_widget_child_nodes(
                    inner, children, weights, total_weight, am, axis, (fuel - 1) as nat);
                assert(cn =~= flex_linear_widget_child_nodes(
                    inner, children, weights, total_weight, am, axis, fuel));
            },
            ContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align,
                           col_widths, row_heights, children } => {
                assert(get_children(widget) =~= children);
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_grid_child_nodes_fuel_monotone(
                        inner, col_widths, row_heights, children,
                        col_widths.len(), (fuel - 1) as nat);
                }
                let cn = grid_widget_child_nodes(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), (fuel - 1) as nat);
                assert(cn =~= grid_widget_child_nodes(
                    inner, col_widths, row_heights, children,
                    col_widths.len(), fuel));
            },
            ContainerWidget::Absolute { padding, children } => {
                let gc = get_children(widget);
                assert(gc =~= Seq::new(children.len(), |i: int| children[i].child));
                assert forall|i: int| 0 <= i < children.len() implies
                    widget_converged(#[trigger] children[i].child, (fuel - 1) as nat)
                by {
                    assert(gc[i] == children[i].child);
                }
                let inner = limits.shrink(padding.horizontal(), padding.vertical());
                if children.len() > 0 {
                    lemma_absolute_child_nodes_fuel_monotone(inner, children, (fuel - 1) as nat);
                }
                let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
                assert(cn =~= absolute_widget_child_nodes(inner, children, fuel));
            },
            ContainerWidget::ListView { spacing, scroll_y, viewport, children } => {
            let gc = get_children(widget);
            assert(gc =~= children);
            let child_limits = Limits {
                min: Size::zero_size(),
                max: Size::new(viewport.width, viewport.height),
            };
            //  Show measure_children at fuel-1 == measure_children at fuel
            //  (since all children are converged at fuel-1)
            let cs1 = crate::measure::measure_children(child_limits, children, (fuel - 1) as nat);
            let cs2 = crate::measure::measure_children(child_limits, children, fuel);
            assert forall|j: int| 0 <= j < children.len() implies
                crate::measure::measure_widget(child_limits, children[j], (fuel - 1) as nat)
                == crate::measure::measure_widget(child_limits, children[j], fuel)
            by {
                assert(widget_converged(children[j], (fuel - 1) as nat));
                crate::measure::lemma_measure_fuel_monotone(child_limits, children[j], (fuel - 1) as nat);
            };
            assert(cs1 =~= cs2);
            //  With same child_sizes, visible range is the same
            let first = listview_first_visible(cs1, spacing, scroll_y);
            let end = listview_end_visible(cs1, spacing, scroll_y, viewport.height);
            //  Prove bounds on first and end
            crate::layout::listview_proofs::lemma_first_visible_bounded(cs1, spacing, scroll_y);
            crate::layout::listview_proofs::lemma_end_visible_bounded(cs1, spacing, scroll_y, viewport.height);
            let count: nat = if end >= first { (end - first) as nat } else { 0 };
            //  Each visible child is converged at fuel-1, so layout(fuel-1) == layout(fuel)
            assert forall|i: int| 0 <= i < (count as int) implies
                (#[trigger] layout_widget(
                    child_limits, children[(first + i) as int], (fuel - 1) as nat,
                )) == layout_widget(
                    child_limits, children[(first + i) as int], fuel,
                )
            by {
                let ci = (first + i) as int;
                assert(first <= end);
                assert(end <= children.len());
                assert(0 <= ci && ci < children.len() as int);
                assert(widget_converged(children[ci], (fuel - 1) as nat));
                lemma_layout_widget_fuel_monotone(child_limits, children[ci], (fuel - 1) as nat);
            };
            //  The visible child node sequences are equal
            //  listview_widget_child_nodes wraps Seq::new — unfold both sides
            let cn1 = listview_widget_child_nodes(child_limits, children, first, end, (fuel - 1) as nat);
            let cn2 = listview_widget_child_nodes(child_limits, children, first, end, fuel);
            assert(cn1.len() == cn2.len());
            assert forall|i: int| 0 <= i < cn1.len() implies cn1[i] == (#[trigger] cn2[i])
            by {
                assert(cn1[i] == layout_widget(child_limits, children[(first + i) as int], (fuel - 1) as nat));
                assert(cn2[i] == layout_widget(child_limits, children[(first + i) as int], fuel));
                let ci = (first + i) as int;
                assert(0 <= ci && ci < children.len() as int);
                assert(widget_converged(children[ci], (fuel - 1) as nat));
                lemma_layout_widget_fuel_monotone(child_limits, children[ci], (fuel - 1) as nat);
            };
            assert(cn1 =~= cn2);
            },
        },
    }
}

//  ── Idempotence completion ─────────────────────────────────────────

///  Convergence is monotone in fuel: if converged at fuel1, then converged at fuel2 >= fuel1.
pub proof fn lemma_widget_converged_monotone<T: OrderedRing>(
    widget: Widget<T>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        widget_converged(widget, fuel1),
        fuel2 >= fuel1,
    ensures
        widget_converged(widget, fuel2),
    decreases fuel2,
{
    if fuel2 == fuel1 {
        //  trivial
    } else {
        //  fuel2 > fuel1 >= 1 (since widget_converged(_, 0) is false, fuel1 >= 1)
        assert(fuel1 >= 1nat);
        assert(fuel2 >= 2nat);
        let children = get_children(widget);
        if children.len() == 0 {
            //  widget_converged(widget, fuel2) is trivially true for leaflike widgets
        } else {
            //  Need: forall|i| widget_converged(children[i], (fuel2 - 1))
            //  We have: forall|i| widget_converged(children[i], (fuel1 - 1))
            assert forall|i: int| 0 <= i < children.len() implies
                widget_converged(children[i], (fuel2 - 1) as nat)
            by {
                //  children[i] is converged at (fuel1 - 1)
                assert(widget_converged(children[i], (fuel1 - 1) as nat));
                //  By induction: converged at (fuel2 - 1) >= (fuel1 - 1)
                lemma_widget_converged_monotone(children[i], (fuel1 - 1) as nat, (fuel2 - 1) as nat);
            }
        }
    }
}

///  Helper: max_child_widget_depth bounds each child's depth.
proof fn lemma_max_child_depth_bounds<T: OrderedRing>(
    children: Seq<Widget<T>>,
    fuel: nat,
    count: nat,
    i: int,
)
    requires
        0 <= i < count,
        count <= children.len(),
    ensures
        widget_depth(children[i], fuel) <= max_child_widget_depth(children, fuel, count),
    decreases count,
{
    if i == count - 1 {
        //  cur = widget_depth(children[count-1], fuel), max = if cur >= prev { cur } else { prev } >= cur
    } else {
        lemma_max_child_depth_bounds::<T>(children, fuel, (count - 1) as nat, i);
    }
}

///  Sufficient fuel implies convergence.
///  If fuel exceeds the estimated depth, the widget has converged.
pub proof fn lemma_sufficient_fuel_converges<T: OrderedRing>(
    widget: Widget<T>,
    fuel: nat,
)
    requires
        fuel > widget_depth(widget, fuel),
    ensures
        widget_converged(widget, fuel),
    decreases fuel,
{
    let children = get_children(widget);
    if fuel == 0 {
        //  widget_depth(widget, 0) = 0, so fuel > 0 contradicts fuel == 0
    } else if children.len() == 0 {
        //  fuel >= 1, widget_converged(leaflike, fuel) = true
    } else {
        //  fuel > 0, children.len() > 0
        //  widget_depth(widget, fuel) = 1 + max_child_widget_depth(children, fuel-1, children.len())
        //  So fuel > 1 + max_child_widget_depth(...)
        //  For each child i:
        //    widget_depth(children[i], fuel-1) <= max_child_widget_depth(children, fuel-1, children.len())
        //    So fuel - 1 > widget_depth(children[i], fuel-1)
        //  By induction: widget_converged(children[i], fuel-1)
        assert forall|i: int| 0 <= i < children.len() implies
            widget_converged(children[i], (fuel - 1) as nat)
        by {
            lemma_max_child_depth_bounds::<T>(children, (fuel - 1) as nat, children.len(), i);
            lemma_sufficient_fuel_converges::<T>(children[i], (fuel - 1) as nat);
        }
    }
}

//  ── Widget path navigation ──────────────────────────────────────

///  Walk the widget tree following a path of child indices.
///  Returns the widget at the given path, or None if any index is out of bounds.
pub open spec fn widget_at_path<T: OrderedRing>(
    widget: Widget<T>, path: Seq<nat>,
) -> Option<Widget<T>>
    decreases path.len(),
{
    if path.len() == 0 {
        Some(widget)
    } else {
        let children = get_children(widget);
        let idx = path[0];
        if idx >= children.len() {
            None
        } else {
            widget_at_path(children[idx as int], path.subrange(1, path.len() as int))
        }
    }
}

///  If the widget at the given path is a TextInput, return its text_input_id.
pub open spec fn focused_text_input_id<T: OrderedRing>(
    widget: Widget<T>, path: Seq<nat>,
) -> Option<nat> {
    match widget_at_path(widget, path) {
        Some(Widget::Leaf(LeafWidget::TextInput { text_input_id, .. })) => Some(text_input_id),
        _ => None,
    }
}

///  If the widget at the given path is a TextInput, return its config.
pub open spec fn focused_text_input_config<T: OrderedRing>(
    widget: Widget<T>, path: Seq<nat>,
) -> Option<TextInputConfig> {
    match widget_at_path(widget, path) {
        Some(Widget::Leaf(LeafWidget::TextInput { config, .. })) => Some(config),
        _ => None,
    }
}

///  widget_at_path for empty path always returns Some.
pub proof fn lemma_widget_at_path_empty<T: OrderedRing>(widget: Widget<T>)
    ensures widget_at_path(widget, Seq::empty()) == Some(widget),
{}

///  widget_at_path respects path_valid: valid path implies Some result.
pub proof fn lemma_widget_at_path_valid<T: OrderedRing>(
    widget: Widget<T>, path: Seq<nat>, fuel: nat,
)
    requires
        fuel > widget_depth(widget, fuel),
    ensures
        //  Note: path_valid is on Node, but widget_at_path is on Widget.
        //  This lemma just proves non-None for in-bounds indices.
        path.len() == 0 ==> widget_at_path(widget, path).is_some(),
{}

///  Layout is deterministic: once fuel exceeds the widget tree depth,
///  the result is independent of the specific fuel value.
///  Generalizes lemma_layout_widget_fuel_monotone from fuel vs fuel+1
///  to any two converged fuel levels.
pub proof fn lemma_layout_deterministic<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        widget_converged(widget, fuel1),
        widget_converged(widget, fuel2),
    ensures
        layout_widget(limits, widget, fuel1) == layout_widget(limits, widget, fuel2),
{
    //  WLOG fuel1 <= fuel2 — prove both directions by induction on the smaller.
    //  Step up from min(fuel1,fuel2) to max(fuel1,fuel2) one step at a time.
    let lo = if fuel1 <= fuel2 { fuel1 } else { fuel2 };
    let hi = if fuel1 <= fuel2 { fuel2 } else { fuel1 };
    //  Both converged at lo (since converged at both fuel1 and fuel2, and lo is one of them)
    lemma_layout_deterministic_helper(limits, widget, lo, hi);
    //  layout(lo) == layout(hi)
    //  Since lo and hi are fuel1/fuel2 in some order, result follows.
}

///  Helper: proves layout(lo) == layout(hi) when lo <= hi and widget converged at lo.
proof fn lemma_layout_deterministic_helper<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    lo: nat,
    hi: nat,
)
    requires
        lo <= hi,
        widget_converged(widget, lo),
    ensures
        layout_widget(limits, widget, lo) == layout_widget(limits, widget, hi),
    decreases hi - lo,
{
    if lo == hi {
        //  trivial
    } else {
        lemma_layout_widget_fuel_monotone(limits, widget, lo);
        //  layout(lo) == layout(lo+1)
        lemma_widget_converged_monotone(widget, lo, lo + 1);
        //  converged at lo+1
        lemma_layout_deterministic_helper(limits, widget, lo + 1, hi);
        //  layout(lo+1) == layout(hi), chain: layout(lo) == layout(hi)
    }
}

//  ── widget_at_path composition and properties ───────────────────

///  widget_at_path composes: navigating path1 ++ path2 is the same as
///  navigating path1 first, then path2 from the result.
pub proof fn lemma_widget_at_path_compose<T: OrderedRing>(
    widget: Widget<T>,
    path1: Seq<nat>,
    path2: Seq<nat>,
)
    ensures
        widget_at_path(widget, path1 + path2) ==
        match widget_at_path(widget, path1) {
            Some(w) => widget_at_path(w, path2),
            None => None,
        },
    decreases path1.len(),
{
    if path1.len() == 0 {
        assert(path1 + path2 =~= path2);
    } else {
        let children = get_children(widget);
        let idx = path1[0];
        if idx >= children.len() {
            //  widget_at_path(widget, path1) = None
            //  widget_at_path(widget, path1 + path2) = None (first step fails)
            let combined = path1 + path2;
            assert(combined[0] == path1[0]);
            assert(combined.len() > 0);
        } else {
            let rest1 = path1.subrange(1, path1.len() as int);
            let combined = path1 + path2;
            //  combined[0] == path1[0] = idx
            assert(combined[0] == idx);
            //  combined.subrange(1, ..) == rest1 + path2
            assert(combined.subrange(1, combined.len() as int) =~= rest1 + path2);
            //  IH: widget_at_path(children[idx], rest1 + path2) ==
            //      match widget_at_path(children[idx], rest1) { Some(w) => widget_at_path(w, path2), None => None }
            lemma_widget_at_path_compose(children[idx as int], rest1, path2);
        }
    }
}

///  widget_at_path is deterministic: same inputs → same output.
///  (This is trivially true for spec functions, but worth stating.)
pub proof fn lemma_widget_at_path_deterministic<T: OrderedRing>(
    w1: Widget<T>, w2: Widget<T>,
    path1: Seq<nat>, path2: Seq<nat>,
)
    requires w1 === w2, path1 === path2,
    ensures widget_at_path(w1, path1) === widget_at_path(w2, path2),
{}

///  Single-step navigation: widget_at_path with a one-element path.
pub proof fn lemma_widget_at_path_single<T: OrderedRing>(
    widget: Widget<T>, idx: nat,
)
    requires idx < get_children(widget).len(),
    ensures
        widget_at_path(widget, seq![idx]) == Some(get_children(widget)[idx as int]),
{
    let path = seq![idx];
    let rest = path.subrange(1, path.len() as int);
    assert(rest =~= Seq::<nat>::empty());
    assert(widget_at_path(get_children(widget)[idx as int], rest)
        == Some(get_children(widget)[idx as int]));
}

///  widget_at_path returns None when path index is out of bounds.
pub proof fn lemma_widget_at_path_oob<T: OrderedRing>(
    widget: Widget<T>, path: Seq<nat>,
)
    requires
        path.len() > 0,
        path[0] >= get_children(widget).len(),
    ensures
        widget_at_path(widget, path).is_none(),
{}

} //  verus!
