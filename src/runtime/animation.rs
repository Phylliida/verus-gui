use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::runtime::node::RuntimeNode;
use crate::animation::*;
use crate::node::Node;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub fn scalar_lerp_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &R, b: &R, t: &R,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), t.wf_spec(),
    ensures out.wf_spec(), out@ == scalar_lerp::<V>(a@, b@, t@),
{
    let one = t.one_like();
    let one_minus_t = one.sub(t);
    let tb = t.copy().mul(b);
    let oma = one_minus_t.mul(a);
    tb.add(&oma)
}

pub fn lerp_size_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimeSize<R, V>, b: &RuntimeSize<R, V>, t: &R,
) -> (out: RuntimeSize<R, V>)
    requires a.wf_spec(), b.wf_spec(), t.wf_spec(),
    ensures out.wf_spec(), out@ == lerp_size::<V>(a.model@, b.model@, t@),
{
    let t1 = t.copy();
    let w = scalar_lerp_exec(&a.width, &b.width, &t1);
    let h = scalar_lerp_exec(&a.height, &b.height, t);
    RuntimeSize::new(w, h)
}

pub fn copy_node_deep_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimeNode<R, V>, fuel: u64,
) -> (out: RuntimeNode<R, V>)
    requires a.wf_deep(fuel as nat), fuel > 0,
    ensures out.wf_deep((fuel - 1) as nat), out@ == a.model@,
    decreases fuel,
{
    let x = a.x.copy();
    let y = a.y.copy();
    let size = a.size.copy_size();
    let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.children.len()
        invariant
            a.wf_deep(fuel as nat),
            fuel > 0,
            0 <= idx <= a.children.len(),
            children@.len() == idx,
            forall|j: int| 0 <= j < idx ==> {
                &&& (#[trigger] children@[j]).model@ == a.model@.children[j]
                &&& (fuel > 1 ==> children@[j].wf_deep((fuel - 2) as nat))
                &&& (fuel == 1 ==> children@[j].wf_shallow())
            },
        decreases a.children.len() - idx,
    {
        assert(a.children@[idx as int].wf_deep((fuel - 1) as nat));
        assert(a.children@[idx as int].wf_shallow());
        let child = if fuel > 1 {
            copy_node_deep_exec(&a.children[idx], fuel - 1)
        } else {
            let cx = a.children[idx].x.copy();
            let cy = a.children[idx].y.copy();
            let cs = a.children[idx].size.copy_size();
            RuntimeNode {
                x: cx, y: cy, size: cs,
                children: Vec::new(),
                model: Ghost(a.model@.children[idx as int]),
            }
        };
        children.push(child);
        idx = idx + 1;
    }
    RuntimeNode { x, y, size, children, model: Ghost(a.model@) }
}

pub fn lerp_node_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimeNode<R, V>,
    b: &RuntimeNode<R, V>,
    t: &R,
    fuel: u64,
) -> (out: RuntimeNode<R, V>)
    requires
        a.wf_deep(fuel as nat),
        b.wf_deep(fuel as nat),
        t.wf_spec(),
        fuel > 0,
    ensures
        out.wf_deep((fuel - 1) as nat),
        out@ == lerp_node::<V>(a.model@, b.model@, t@, fuel as nat),
    decreases fuel,
{
    if a.children.len() != b.children.len() {
        copy_node_deep_exec(a, fuel)
    } else {
        let t1 = t.copy();
        let t2 = t.copy();
        let t3 = t.copy();
        let x = scalar_lerp_exec(&a.x, &b.x, &t1);
        let y = scalar_lerp_exec(&a.y, &b.y, &t2);
        let size = lerp_size_exec(&a.size, &b.size, &t3);

        let ghost result_spec = lerp_node::<V>(a.model@, b.model@, t@, fuel as nat);

        let mut children: Vec<RuntimeNode<R, V>> = Vec::new();
        let mut idx: usize = 0;
        while idx < a.children.len()
            invariant
                a.wf_deep(fuel as nat),
                b.wf_deep(fuel as nat),
                t.wf_spec(),
                fuel > 0,
                a.children@.len() == b.children@.len(),
                a.model@.children.len() == b.model@.children.len(),
                0 <= idx <= a.children.len(),
                children@.len() == idx,
                result_spec == lerp_node::<V>(a.model@, b.model@, t@, fuel as nat),
                forall|j: int| 0 <= j < idx ==> {
                    &&& (#[trigger] children@[j]).model@ == result_spec.children[j]
                    &&& (fuel > 1 ==> children@[j].wf_deep((fuel - 2) as nat))
                    &&& (fuel == 1 ==> children@[j].wf_shallow())
                },
            decreases a.children.len() - idx,
        {
            assert(result_spec.children[idx as int] ==
                lerp_node::<V>(
                    a.model@.children[idx as int], b.model@.children[idx as int],
                    t@, (fuel - 1) as nat,
                ));

            let tc = t.copy();
            let child = if fuel > 1 {
                lerp_node_exec(&a.children[idx], &b.children[idx], &tc, fuel - 1)
            } else {
                assert(a.children@[idx as int].wf_deep((fuel - 1) as nat));
                assert(a.children@[idx as int].wf_shallow());
                let cx = a.children[idx].x.copy();
                let cy = a.children[idx].y.copy();
                let cs = a.children[idx].size.copy_size();
                RuntimeNode {
                    x: cx, y: cy, size: cs,
                    children: Vec::new(),
                    model: Ghost(a.model@.children[idx as int]),
                }
            };
            assert(child.model@ == result_spec.children[idx as int]);
            children.push(child);
            idx = idx + 1;
        }
        RuntimeNode { x, y, size, children, model: Ghost(result_spec) }
    }
}

} //  verus!
