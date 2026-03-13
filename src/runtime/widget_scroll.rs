use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
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

/// Layout a scroll view widget: child at (-scroll_x, -scroll_y) with viewport limits.
pub fn layout_scroll_view_exec(
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

} // verus!
