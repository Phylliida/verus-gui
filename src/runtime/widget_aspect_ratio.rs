use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::partial_order::PartialOrder;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::layout_widget_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;

verus! {

pub fn layout_aspect_ratio_widget_exec(
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

} // verus!
