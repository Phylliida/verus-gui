use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::runtime::RuntimeSize;
use crate::runtime::RuntimeNode;
use crate::animation::*;
use crate::node::Node;

verus! {

///  Runtime scalar lerp: (1-t)*a + t*b.
pub fn scalar_lerp_exec(
    a: &RuntimeRational,
    b: &RuntimeRational,
    t: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        t.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == scalar_lerp::<RationalModel>(a@, b@, t@),
{
    //  scalar_lerp(a, b, t) = convex(b, a, t) = t*b + (1-t)*a
    let one = RuntimeRational::from_int(1);
    let one_minus_t = one.sub(t);  //  1 - t
    let t_copy = copy_rational(t);
    let tb = t_copy.mul(b);        //  t * b
    let oma = one_minus_t.mul(a);   //  (1-t) * a
    let result = tb.add(&oma);      //  t*b + (1-t)*a
    result
}

///  Runtime size lerp: componentwise scalar_lerp on width and height.
pub fn lerp_size_exec(
    a: &RuntimeSize,
    b: &RuntimeSize,
    t: &RuntimeRational,
) -> (out: RuntimeSize)
    requires
        a.wf_spec(),
        b.wf_spec(),
        t.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == lerp_size::<RationalModel>(a@, b@, t@),
{
    let t1 = copy_rational(t);
    let w = scalar_lerp_exec(&a.width, &b.width, &t1);
    let h = scalar_lerp_exec(&a.height, &b.height, t);
    RuntimeSize::new(w, h)
}

///  Recursively deep-copy a RuntimeNode. At fuel=1, copies shallowly.
///  At fuel>1, recurses into children.
pub fn copy_node_deep_exec(a: &RuntimeNode, fuel: u64) -> (out: RuntimeNode)
    requires a.wf_deep(fuel as nat), fuel > 0,
    ensures
        out.wf_deep((fuel - 1) as nat),
        out@ == a@,
    decreases fuel,
{
    let x = copy_rational(&a.x);
    let y = copy_rational(&a.y);
    let size = a.size.copy_size();
    let mut children: Vec<RuntimeNode> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.children.len()
        invariant
            a.wf_deep(fuel as nat),
            fuel > 0,
            0 <= idx <= a.children.len(),
            children@.len() == idx,
            forall|j: int| 0 <= j < idx ==> {
                &&& (#[trigger] children@[j])@ == a@.children[j]
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
            let cx = copy_rational(&a.children[idx].x);
            let cy = copy_rational(&a.children[idx].y);
            let cs = a.children[idx].size.copy_size();
            RuntimeNode {
                x: cx,
                y: cy,
                size: cs,
                children: Vec::new(),
                model: Ghost(a@.children[idx as int]),
            }
        };
        children.push(child);
        idx = idx + 1;
    }
    RuntimeNode { x, y, size, children, model: Ghost(a@) }
}

///  Runtime node lerp: recursive tree interpolation.
///  Requires wf_deep(fuel) to enable recursive descent into children.
///  Ensures wf_deep((fuel-1)) for full tree well-formedness.
pub fn lerp_node_exec(
    a: &RuntimeNode,
    b: &RuntimeNode,
    t: &RuntimeRational,
    fuel: u64,
) -> (out: RuntimeNode)
    requires
        a.wf_deep(fuel as nat),
        b.wf_deep(fuel as nat),
        t.wf_spec(),
        fuel > 0,
    ensures
        out.wf_deep((fuel - 1) as nat),
        out@ == lerp_node::<RationalModel>(a@, b@, t@, fuel as nat),
    decreases fuel,
{
    if a.children.len() != b.children.len() {
        //  Mismatch: lerp_node returns a. Deep copy preserves wf_deep.
        copy_node_deep_exec(a, fuel)
    } else {
        //  Matching children: interpolate fields, recurse on children
        let t1 = copy_rational(t);
        let t2 = copy_rational(t);
        let t3 = copy_rational(t);
        let x = scalar_lerp_exec(&a.x, &b.x, &t1);
        let y = scalar_lerp_exec(&a.y, &b.y, &t2);
        let size = lerp_size_exec(&a.size, &b.size, &t3);

        let ghost result_spec = lerp_node::<RationalModel>(a@, b@, t@, fuel as nat);

        let mut children: Vec<RuntimeNode> = Vec::new();
        let mut idx: usize = 0;
        while idx < a.children.len()
            invariant
                a.wf_deep(fuel as nat),
                b.wf_deep(fuel as nat),
                t.wf_spec(),
                fuel > 0,
                a.children@.len() == b.children@.len(),
                a@.children.len() == b@.children.len(),
                0 <= idx <= a.children.len(),
                children@.len() == idx,
                result_spec == lerp_node::<RationalModel>(a@, b@, t@, fuel as nat),
                forall|j: int| 0 <= j < idx ==> {
                    &&& (#[trigger] children@[j])@ == result_spec.children[j]
                    &&& (fuel > 1 ==> children@[j].wf_deep((fuel - 2) as nat))
                    &&& (fuel == 1 ==> children@[j].wf_shallow())
                },
            decreases a.children.len() - idx,
        {
            //  Help Z3: result_spec.children[idx] == lerp_node(a.child[idx], b.child[idx], t, fuel-1)
            assert(result_spec.children[idx as int] ==
                lerp_node::<RationalModel>(
                    a@.children[idx as int], b@.children[idx as int],
                    t@, (fuel - 1) as nat,
                ));

            let tc = copy_rational(t);
            let child = if fuel > 1 {
                //  wf_deep(fuel) at fuel > 1 gives children wf_deep(fuel-1)
                lerp_node_exec(
                    &a.children[idx],
                    &b.children[idx],
                    &tc,
                    fuel - 1,
                )
            } else {
                //  fuel == 1 → child fuel == 0 → lerp_node returns a.children[idx]
                assert(a.children@[idx as int].wf_deep((fuel - 1) as nat));
                assert(a.children@[idx as int].wf_shallow());
                let cx = copy_rational(&a.children[idx].x);
                let cy = copy_rational(&a.children[idx].y);
                let cs = a.children[idx].size.copy_size();
                RuntimeNode {
                    x: cx,
                    y: cy,
                    size: cs,
                    children: Vec::new(),
                    model: Ghost(a@.children[idx as int]),
                }
            };
            assert(child@ == result_spec.children[idx as int]);
            children.push(child);
            idx = idx + 1;
        }
        RuntimeNode {
            x,
            y,
            size,
            children,
            model: Ghost(result_spec),
        }
    }
}

} //  verus!
