use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
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

///  Layout a margin widget: shrink limits, layout child, wrap with offsets.
pub fn layout_margin_widget_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    margin: &RuntimePadding<R, V>,
    child: &Box<RuntimeWidget<R, V>>,
    fuel: usize,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        margin.wf_spec(),
        fuel > 0,
        child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_w = Widget::Wrapper(WrapperWidget::Margin {
                margin: margin@,
                child: Box::new(child.model()),
            });
            layout_widget::<V>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let pad_h = margin.horizontal_exec();
    let pad_v = margin.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);

    let child_node = layout_widget_exec(&inner, child, fuel - 1);

    //  Compute total size
    let pad_h2 = margin.horizontal_exec();
    let pad_v2 = margin.vertical_exec();
    let total_w = pad_h2.add(&child_node.size.width);
    let total_h = pad_v2.add(&child_node.size.height);
    let parent_size = limits.resolve_exec(RuntimeSize::new(total_w, total_h));

    //  Build the single child with margin offsets
    let child_x = margin.left.copy();
    let child_y = margin.top.copy();
    let child_size = child_node.size.copy_size();

    let ghost child_spec = layout_widget::<V>(
        inner@, child.model(), (fuel - 1) as nat);

    let positioned_child = RuntimeNode {
        x: child_x,
        y: child_y,
        size: child_size,
        children: child_node.children,
        model: Ghost(Node::<V> {
            x: margin@.left,
            y: margin@.top,
            size: child_spec.size,
            children: child_spec.children,
        }),
    };

    proof {
        assert(positioned_child.wf_shallow());
        assert(positioned_child@ == Node::<V> {
            x: margin@.left,
            y: margin@.top,
            size: child_spec.size,
            children: child_spec.children,
        });
    }

    let x = limits.min.width.zero_like();
    let y = limits.min.width.zero_like();

    let ghost parent_model = layout_widget::<V>(
        limits@,
        Widget::Wrapper(WrapperWidget::Margin { margin: margin@, child: Box::new(child.model()) }),
        fuel as nat,
    );

    let mut result_children: Vec<RuntimeNode<R, V>> = Vec::new();
    result_children.push(positioned_child);

    let out = RuntimeNode {
        x,
        y,
        size: parent_size,
        children: result_children,
        model: Ghost(parent_model),
    };

    proof {
        //  Show out@ == parent_model
        //  parent_model.children == Seq::empty().push(Node { x: margin.left, y: margin.top, ... })
        assert(parent_model.children.len() == 1);
        assert(out.children@.len() == 1);
        assert(out@.children.len() == 1);
        assert(out.children@[0].wf_shallow());
        assert(out.children@[0]@ == out@.children[0]);
    }

    out
}

} //  verus!
