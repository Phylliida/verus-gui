use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::size::RuntimeSize;
use crate::node::Node;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

verus! {

pub struct RuntimeNode<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub x: R,
    pub y: R,
    pub size: RuntimeSize<R, V>,
    pub children: Vec<RuntimeNode<R, V>>,
    pub model: Ghost<Node<V>>,
}

impl View for RuntimeNode<RuntimeRational, Rational> {
    type V = Node<Rational>;
    open spec fn view(&self) -> Node<Rational> { self.model@ }
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimeNode<R, V> {
    pub open spec fn wf_spec(&self) -> bool
        decreases self.children@.len(),
    {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.size.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.size.model@ == self.model@.size
        &&& self.children@.len() == self.model@.children.len()
        &&& forall|i: int| 0 <= i < self.children@.len() ==> {
            &&& (#[trigger] self.children@[i]).wf_shallow()
            &&& self.children@[i].model@ == self.model@.children[i]
        }
    }

    pub open spec fn wf_deep(&self, depth: nat) -> bool
        decreases depth,
    {
        &&& self.wf_shallow()
        &&& self.children@.len() == self.model@.children.len()
        &&& (depth > 0 ==> forall|i: int| 0 <= i < self.children@.len() ==> {
            &&& (#[trigger] self.children@[i]).wf_deep((depth - 1) as nat)
            &&& self.children@[i].model@ == self.model@.children[i]
        })
    }

    pub open spec fn wf_shallow(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.size.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.size.model@ == self.model@.size
    }

    pub fn leaf_exec(x: R, y: R, size: RuntimeSize<R, V>) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), size.wf_spec(),
        ensures out.wf_spec(), out.model@ == Node::leaf(x.model(), y.model(), size.model@),
    {
        let ghost model = Node::leaf(x.model(), y.model(), size.model@);
        RuntimeNode { x, y, size, children: Vec::new(), model: Ghost(model) }
    }
}

} //  verus!
