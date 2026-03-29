use vstd::prelude::*;
use verus_algebra::traits::Equivalence;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::node::RuntimeNode;
use crate::runtime::size::RuntimeSize;
use crate::diff::{DiffResult, diff_nodes, diff_children};

verus! {

///  Runtime diff result.
pub enum RuntimeDiffResult {
    Same,
    PositionChanged,
    SizeChanged,
    ChildCountChanged,
    ChildrenChanged { diffs: Vec<(usize, RuntimeDiffResult)> },
}

///  Check if two RuntimeRationals are equivalent (a <= b && b <= a).
fn rational_eqv(a: &RuntimeRational, b: &RuntimeRational) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(),
    ensures out == a@.eqv(b@),
{
    a.le(b) && b.le(a)
}

///  Compare two runtime nodes.
pub fn diff_nodes_exec(
    old: &RuntimeNode,
    new: &RuntimeNode,
    fuel: usize,
) -> (out: RuntimeDiffResult)
    requires
        old.wf_deep(fuel as nat),
        new.wf_deep(fuel as nat),
    ensures
        match (&out, diff_nodes::<RationalModel>(old@, new@, fuel as nat)) {
            (RuntimeDiffResult::Same, DiffResult::<RationalModel>::Same) => true,
            (RuntimeDiffResult::PositionChanged, DiffResult::<RationalModel>::PositionChanged) => true,
            (RuntimeDiffResult::SizeChanged, DiffResult::<RationalModel>::SizeChanged) => true,
            (RuntimeDiffResult::ChildCountChanged, DiffResult::<RationalModel>::ChildCountChanged) => true,
            (RuntimeDiffResult::ChildrenChanged { .. }, DiffResult::<RationalModel>::ChildrenChanged { .. }) => true,
            _ => false,
        },
    decreases fuel,
{
    if fuel == 0 {
        return RuntimeDiffResult::Same;
    }

    if !(rational_eqv(&old.x, &new.x)) || !(rational_eqv(&old.y, &new.y)) {
        return RuntimeDiffResult::PositionChanged;
    }

    if !(rational_eqv(&old.size.width, &new.size.width)) || !(rational_eqv(&old.size.height, &new.size.height)) {
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
            diffs@.len() == diff_children::<RationalModel>(old@, new@, i as nat, (fuel - 1) as nat).len(),
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
