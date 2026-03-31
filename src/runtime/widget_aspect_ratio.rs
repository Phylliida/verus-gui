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

pub fn layout_aspect_ratio_widget_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    ratio: &R,
    child: &Box<RuntimeWidget<R, V>>,
    fuel: usize,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        ratio.wf_spec(),
        !ratio@.eqv(V::zero()),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::Wrapper(WrapperWidget::AspectRatio {
                ratio: ratio@,
                child: Box::new(child.model()),
            });
            layout_widget::<V>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let w1 = limits.max.width.copy();
    let h1 = w1.div(ratio);

    let child_node = if h1.le(&limits.max.height) {
        let eff_max = RuntimeSize::new(limits.max.width.copy(), h1);
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
        layout_widget_exec(&eff, child, fuel - 1)
    };

    let resolved = limits.resolve_exec(child_node.size.copy_size());
    let x = limits.min.width.zero_like();
    let y = limits.min.width.zero_like();
    let cx = limits.min.width.zero_like();
    let cy = limits.min.width.zero_like();
    let child_size = child_node.size.copy_size();

    let ghost child_spec = if limits@.max.width.div(ratio@).le(limits@.max.height) {
        let eff = Limits {
            min: limits@.min,
            max: Size::new(limits@.max.width, limits@.max.width.div(ratio@)),
        };
        layout_widget::<V>(eff, child.model(), (fuel - 1) as nat)
    } else {
        let eff = Limits {
            min: limits@.min,
            max: Size::new(limits@.max.height.mul(ratio@), limits@.max.height),
        };
        layout_widget::<V>(eff, child.model(), (fuel - 1) as nat)
    };

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
        Widget::Wrapper(WrapperWidget::AspectRatio { ratio: ratio@, child: Box::new(child.model()) }),
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
