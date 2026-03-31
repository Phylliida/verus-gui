use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::RuntimeWidget;
use crate::runtime::widget::layout_widget_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Layout a scroll view widget: child at (-scroll_x, -scroll_y) with viewport limits.
pub fn layout_scroll_view_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    viewport: &RuntimeSize<R, V>,
    scroll_x: &R,
    scroll_y: &R,
    child: &Box<RuntimeWidget<R, V>>,
    fuel: usize,
) -> (out: RuntimeNode<R, V>)
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
            let spec_w = Widget::Wrapper(WrapperWidget::ScrollView {
                viewport: viewport@,
                scroll_x: scroll_x@,
                scroll_y: scroll_y@,
                child: Box::new(child.model()),
            });
            layout_widget::<V>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    //  Child gets limits (zero_min, viewport)
    let child_min = RuntimeSize::new(scroll_x.zero_like(), scroll_x.zero_like());
    let child_max = viewport.copy_size();
    let child_limits = RuntimeLimits::new(child_min, child_max);
    let child_node = layout_widget_exec(&child_limits, child, fuel - 1);

    let resolved = limits.resolve_exec(viewport.copy_size());
    let x = limits.min.width.zero_like();
    let y = limits.min.width.zero_like();
    let neg_sx = scroll_x.neg();
    let neg_sy = scroll_y.neg();
    let child_size = child_node.size.copy_size();

    let ghost child_spec = {
        let cl = Limits::<V> {
            min: Size::zero_size(),
            max: viewport@,
        };
        layout_widget::<V>(cl, child.model(), (fuel - 1) as nat)
    };

    let positioned_child = RuntimeNode {
        x: neg_sx,
        y: neg_sy,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<V> {
            x: scroll_x@.neg(),
            y: scroll_y@.neg(),
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    let ghost parent_model = layout_widget::<V>(
        limits@,
        Widget::Wrapper(WrapperWidget::ScrollView {
            viewport: viewport@,
            scroll_x: scroll_x@,
            scroll_y: scroll_y@,
            child: Box::new(child.model()),
        }),
        fuel as nat,
    );

    let mut result_children: Vec<RuntimeNode<R, V>> = Vec::new();
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

} //  verus!
