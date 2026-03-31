use vstd::prelude::*;
use verus_algebra::traits::Equivalence;
use crate::runtime::node::RuntimeNode;
use crate::runtime::size::RuntimeSize;
use crate::diff::{DiffResult, diff_nodes, diff_children};
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub enum RuntimeDiffResult {
    Same,
    PositionChanged,
    SizeChanged,
    ChildCountChanged,
    ChildrenChanged { diffs: Vec<(usize, RuntimeDiffResult)> },
}

pub fn diff_nodes_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    old: &RuntimeNode<R, V>,
    new: &RuntimeNode<R, V>,
    fuel: usize,
) -> (out: RuntimeDiffResult)
    requires
        old.wf_deep(fuel as nat),
        new.wf_deep(fuel as nat),
    ensures
        match (&out, diff_nodes::<V>(old.model@, new.model@, fuel as nat)) {
            (RuntimeDiffResult::Same, DiffResult::<V>::Same) => true,
            (RuntimeDiffResult::PositionChanged, DiffResult::<V>::PositionChanged) => true,
            (RuntimeDiffResult::SizeChanged, DiffResult::<V>::SizeChanged) => true,
            (RuntimeDiffResult::ChildCountChanged, DiffResult::<V>::ChildCountChanged) => true,
            (RuntimeDiffResult::ChildrenChanged { .. }, DiffResult::<V>::ChildrenChanged { .. }) => true,
            _ => false,
        },
    decreases fuel,
{
    if fuel == 0 {
        return RuntimeDiffResult::Same;
    }

    if !(old.x.eq(&new.x)) || !(old.y.eq(&new.y)) {
        return RuntimeDiffResult::PositionChanged;
    }

    if !(old.size.width.eq(&new.size.width)) || !(old.size.height.eq(&new.size.height)) {
        return RuntimeDiffResult::SizeChanged;
    }

    if old.children.len() != new.children.len() {
        return RuntimeDiffResult::ChildCountChanged;
    }

    let n = old.children.len();
    let mut diffs: Vec<(usize, RuntimeDiffResult)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == old.children@.len(),
            n == new.children@.len(),
            old.wf_deep(fuel as nat),
            new.wf_deep(fuel as nat),
            fuel > 0,
            diffs@.len() == diff_children::<V>(old.model@, new.model@, i as nat, (fuel - 1) as nat).len(),
        decreases n - i,
    {
        assert(old.children@[i as int].wf_deep((fuel - 1) as nat));
        assert(new.children@[i as int].wf_deep((fuel - 1) as nat));
        let d = diff_nodes_exec(&old.children[i], &new.children[i], fuel - 1);
        match d {
            RuntimeDiffResult::Same => {},
            _ => {
                diffs.push((i, d));
            },
        }
        i = i + 1;
    }

    if diffs.len() == 0 {
        RuntimeDiffResult::Same
    } else {
        RuntimeDiffResult::ChildrenChanged { diffs }
    }
}

} //  verus!
