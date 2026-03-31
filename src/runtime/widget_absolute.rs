use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::absolute::*;
use crate::runtime::widget::RuntimeAbsoluteChild;
use crate::runtime::widget::layout_widget_exec;
use crate::runtime::widget::merge_layout_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;
use crate::layout::absolute::*;
use crate::layout::absolute_proofs::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Layout an absolute widget: each child at explicit (x, y) offsets.
pub fn layout_absolute_widget_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>,
    padding: &RuntimePadding<R, V>,
    children: &Vec<RuntimeAbsoluteChild<R, V>>,
    fuel: usize,
) -> (out: RuntimeNode<R, V>)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==> children@[i].x.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==> children@[i].y.wf_spec(),
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).child.wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_ac = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::Container(ContainerWidget::Absolute {
                padding: padding@,
                children: spec_ac,
            });
            layout_widget::<V>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    let ghost spec_ac: Seq<AbsoluteChild<V>> =
        Seq::new(children@.len() as nat, |i: int| children@[i].model());

    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);
    let n = children.len();

    //  Recursively layout each child, collecting child nodes + sizes + offsets
    let mut child_nodes: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize<R, V>> = Vec::new();
    let mut offsets_x: Vec<R> = Vec::new();
    let mut offsets_y: Vec<R> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_ac.len() == n as nat,
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_nodes@.len() == i as int,
            child_sizes@.len() == i as int,
            offsets_x@.len() == i as int,
            offsets_y@.len() == i as int,
            forall|j: int| 0 <= j < children@.len() ==> children@[j].x.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==> children@[j].y.wf_spec(),
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).child.wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < n ==>
                spec_ac[j] == (#[trigger] children@[j]).model(),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == layout_widget::<V>(
                        inner@, spec_ac[j].child, (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == child_nodes@[j]@.size
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] offsets_x@[j]).wf_spec()
                &&& offsets_x@[j]@ == spec_ac[j].x
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] offsets_y@[j]).wf_spec()
                &&& offsets_y@[j]@ == spec_ac[j].y
            },
        decreases n - i,
    {
        let cn = layout_widget_exec(&inner, &children[i].child, fuel - 1);
        child_sizes.push(cn.size.copy_size());
        offsets_x.push(children[i].x.copy());
        offsets_y.push(children[i].y.copy());
        child_nodes.push(cn);
        i = i + 1;
    }

    //  Assert preconditions for absolute_layout_exec
    proof {
        assert forall|j: int| 0 <= j < child_sizes@.len() implies
            (#[trigger] child_sizes@[j]).wf_spec()
        by {}
        assert forall|j: int| 0 <= j < offsets_x@.len() implies
            (#[trigger] offsets_x@[j]).wf_spec()
        by {}
        assert forall|j: int| 0 <= j < offsets_y@.len() implies
            (#[trigger] offsets_y@[j]).wf_spec()
        by {}
    }

    let layout_result = absolute_layout_exec(limits, padding, &child_sizes,
        &offsets_x, &offsets_y);

    //  Merge
    let ghost cn_models: Seq<Node<V>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);

    proof {
        reveal(absolute_layout);
        lemma_absolute_children_len::<V>(
            padding@,
            Seq::new(child_sizes@.len() as nat, |i: int|
                (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@)),
            0,
        );
        assert(layout_result.children@.len() == child_nodes@.len());
    }

    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    //  Connect to spec
    proof {
        let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
        let spec_cn = absolute_widget_child_nodes(inner_spec, spec_ac, (fuel - 1) as nat);

        //  cn_models =~= spec_cn
        assert(cn_models.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < cn_models.len() as int implies
            cn_models[j] == spec_cn[j]
        by {
            let ac_j = spec_ac[j];
            assert(ac_j == children@[j].model());
            assert(ac_j.child == children@[j].child.model());
        }
        assert(cn_models =~= spec_cn);

        //  child_sizes view matches spec
        let sizes_view: Seq<Size<V>> =
            Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@);
        let spec_sizes: Seq<Size<V>> =
            Seq::new(spec_cn.len(), |i: int| spec_cn[i].size);
        assert(sizes_view =~= spec_sizes) by {
            assert forall|j: int| 0 <= j < sizes_view.len() as int implies
                sizes_view[j] == spec_sizes[j]
            by {}
        }

        //  offsets match spec
        let ox_view: Seq<V> =
            Seq::new(offsets_x@.len() as nat, |i: int| offsets_x@[i]@);
        let oy_view: Seq<V> =
            Seq::new(offsets_y@.len() as nat, |i: int| offsets_y@[i]@);

        //  Build spec child_data from spec_ac
        let body_offsets: Seq<(V, V)> =
            Seq::new(spec_ac.len(), |i: int| (spec_ac[i].x, spec_ac[i].y));
        let body_data: Seq<(V, V, Size<V>)> =
            Seq::new(spec_cn.len(), |i: int|
                (body_offsets[i].0, body_offsets[i].1, spec_cn[i].size));

        //  layout_result data matches body_data
        let exec_data: Seq<(V, V, Size<V>)> =
            Seq::new(child_sizes@.len() as nat, |i: int|
                (offsets_x@[i]@, offsets_y@[i]@, child_sizes@[i]@));
        assert(exec_data =~= body_data) by {
            assert forall|j: int| 0 <= j < exec_data.len() as int implies
                exec_data[j] == body_data[j]
            by {
                assert(offsets_x@[j]@ == spec_ac[j].x);
                assert(offsets_y@[j]@ == spec_ac[j].y);
            }
        }
    }

    merged
}

} //  verus!
