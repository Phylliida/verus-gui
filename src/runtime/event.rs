use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::node::RuntimeNode;
use crate::runtime::hit_test::hit_test_exec;
use crate::node::Node;
use crate::hit_test::hit_test;
use crate::event::*;

verus! {

// ── Runtime event types ────────────────────────────────────────────

pub enum RuntimePointerEventKind {
    Down,
    Up,
    Move,
}

/// Runtime pointer event with rational coordinates.
pub struct RuntimePointerEvent {
    pub kind: RuntimePointerEventKind,
    pub x: RuntimeRational,
    pub y: RuntimeRational,
}

/// Runtime focus state tracking the focused path.
pub struct RuntimeFocusState {
    pub focused_path: Option<Vec<usize>>,
}

// ── Dispatch exec ──────────────────────────────────────────────────

/// Runtime event dispatch — wraps hit_test_exec.
pub fn dispatch_pointer_exec(
    root: &RuntimeNode,
    event: &RuntimePointerEvent,
    depth: usize,
) -> (out: Option<Vec<usize>>)
    requires
        root.wf_deep(depth as nat),
        event.x.wf_spec(),
        event.y.wf_spec(),
    ensures
        match (out, dispatch_pointer::<RationalModel>(root@,
            PointerEvent { kind: PointerEventKind::Down, x: event.x@, y: event.y@ },
            depth as nat))
        {
            (Some(exec_path), Some(spec_path)) => {
                exec_path@.len() == spec_path.len()
                && forall|i: int| 0 <= i < exec_path@.len() ==>
                    exec_path@[i] as nat == spec_path[i]
            },
            (None, None) => true,
            _ => false,
        },
{
    hit_test_exec(root, &event.x, &event.y, depth)
}

/// Update focus on pointer down.
pub fn update_focus_exec(
    state: &mut RuntimeFocusState,
    root: &RuntimeNode,
    event: &RuntimePointerEvent,
    depth: usize,
)
    requires
        root.wf_deep(depth as nat),
        event.x.wf_spec(),
        event.y.wf_spec(),
{
    match event.kind {
        RuntimePointerEventKind::Down => {
            state.focused_path = hit_test_exec(root, &event.x, &event.y, depth);
        },
        _ => {},
    }
}

// ── Bubble path exec ───────────────────────────────────────────────

/// Compute bubble path: sequence of prefixes from full path to empty.
pub fn bubble_path_exec(path: &Vec<usize>) -> (out: Vec<Vec<usize>>)
    ensures
        out@.len() == path@.len() + 1,
{
    let n = path.len();
    let mut result: Vec<Vec<usize>> = Vec::new();
    let mut len: usize = n;

    while len > 0
        invariant
            0 <= len <= n,
            n == path@.len(),
            result@.len() == (n - len) as nat,
        decreases len,
    {
        // Copy path[0..len]
        let mut prefix: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        while j < len
            invariant
                0 <= j <= len,
                len <= n,
                n == path@.len(),
                prefix@.len() == j,
                forall|k: int| 0 <= k < j ==> prefix@[k] == path@[k],
            decreases len - j,
        {
            prefix.push(path[j]);
            j = j + 1;
        }
        result.push(prefix);
        len = len - 1;
    }

    // Push empty path (root)
    result.push(Vec::new());
    result
}

} // verus!
