use vstd::prelude::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::RuntimeWidget;
use crate::runtime::widget::layout_widget_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;

verus! {

///  Layout a sized box widget: intersect limits, layout child, wrap result.
pub fn layout_sized_box_widget_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    inner_limits: &RuntimeLimits<R, V>,
    child: &Box<RuntimeWidget<R, V>>,
    fuel: usize,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        inner_limits.wf_spec(),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::Wrapper(WrapperWidget::SizedBox {
                inner_limits: inner_limits@,
                child: Box::new(child.model()),
            });
            layout_widget::<V>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let effective = limits.intersect_exec(inner_limits);
    let child_node = layout_widget_exec(&effective, child, fuel - 1);
    let resolved = limits.resolve_exec(child_node.size.copy_size());
    let x = limits.min.width.zero_like();
    let y = limits.min.width.zero_like();
    let cx = limits.min.width.zero_like();
    let cy = limits.min.width.zero_like();
    let child_size = child_node.size.copy_size();

    let ghost child_spec = layout_widget::<V>(
        effective@, child.model(), (fuel - 1) as nat);

    let positioned_child = RuntimeNode {
        x: cx,
        y: cy,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<V> {
            x: V::zero(),
            y: V::zero(),
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    let ghost parent_model = layout_widget::<V>(
        limits@,
        Widget::Wrapper(WrapperWidget::SizedBox { inner_limits: inner_limits@, child: Box::new(child.model()) }),
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
