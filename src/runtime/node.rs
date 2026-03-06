use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::size::RuntimeSize;
use crate::node::Node;

verus! {

/// Runtime-backed layout Node with rational coordinates.
pub struct RuntimeNode {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub size: RuntimeSize,
    pub children: Vec<RuntimeNode>,
    pub model: Ghost<Node<RationalModel>>,
}

impl View for RuntimeNode {
    type V = Node<RationalModel>;

    open spec fn view(&self) -> Node<RationalModel> {
        self.model@
    }
}

impl RuntimeNode {
    /// Well-formedness: runtime fields match model, children are well-formed.
    /// Uses children depth as decreases measure for recursive call on children.
    pub open spec fn wf_spec(&self) -> bool
        decreases self.children@.len(),
    {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.size.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.size@ == self@.size
        &&& self.children@.len() == self@.children.len()
        &&& forall|i: int| 0 <= i < self.children@.len() ==> {
            &&& (#[trigger] self.children@[i]).wf_shallow()
            &&& self.children@[i]@ == self@.children[i]
        }
    }

    /// Deep well-formedness: recursively checks all children.
    /// Required for operations that traverse the full tree (e.g., hit testing).
    pub open spec fn wf_deep(&self, depth: nat) -> bool
        decreases depth,
    {
        &&& self.wf_shallow()
        &&& self.children@.len() == self@.children.len()
        &&& (depth > 0 ==> forall|i: int| 0 <= i < self.children@.len() ==> {
            &&& (#[trigger] self.children@[i]).wf_deep((depth - 1) as nat)
            &&& self.children@[i]@ == self@.children[i]
        })
    }

    /// Shallow well-formedness: checks direct fields only, no recursive child check.
    pub open spec fn wf_shallow(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.size.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.size@ == self@.size
    }

    /// A leaf node (no children).
    pub fn leaf_exec(x: RuntimeRational, y: RuntimeRational, size: RuntimeSize) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
            size.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == Node::leaf(x@, y@, size@),
    {
        let ghost model = Node::leaf(x@, y@, size@);
        RuntimeNode {
            x,
            y,
            size,
            children: Vec::new(),
            model: Ghost(model),
        }
    }
}

} // verus!
