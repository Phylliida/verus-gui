use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::RuntimeSize;
use crate::runtime::RuntimeLimits;
use crate::runtime::RuntimeNode;
use crate::runtime::RuntimeWidget;
use crate::runtime::widget::layout_widget_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;

verus! {

///  Layout a sized box widget: intersect limits, layout child, wrap result.
pub fn layout_sized_box_widget_exec(
    limits: &RuntimeLimits,
    inner_limits: &RuntimeLimits,
    child: &Box<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
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
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let effective = limits.intersect_exec(inner_limits);
    let child_node = layout_widget_exec(&effective, child, fuel - 1);
    let resolved = limits.resolve_exec(child_node.size.copy_size());
    let x = RuntimeRational::from_int(0);
    let y = RuntimeRational::from_int(0);
    let cx = RuntimeRational::from_int(0);
    let cy = RuntimeRational::from_int(0);
    let child_size = child_node.size.copy_size();

    let ghost child_spec = layout_widget::<RationalModel>(
        effective@, child.model(), (fuel - 1) as nat);

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
        Widget::Wrapper(WrapperWidget::SizedBox { inner_limits: inner_limits@, child: Box::new(child.model()) }),
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

} //  verus!
