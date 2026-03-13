use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::node::RuntimeNode;
use crate::runtime::hit_test::hit_test_exec;
use crate::runtime::text_model::RuntimeTextModel;
use crate::node::Node;
use crate::hit_test::hit_test;
use crate::event::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;

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

// ── Runtime keyboard event types ──────────────────────────────────

pub struct RuntimeModifiers {
    pub shift: bool,
    pub ctrl: bool,
    pub alt: bool,
}

impl View for RuntimeModifiers {
    type V = Modifiers;
    open spec fn view(&self) -> Modifiers {
        Modifiers {
            shift: self.shift,
            ctrl: self.ctrl,
            alt: self.alt,
        }
    }
}

pub enum RuntimeKeyEventKind {
    Char(char),
    Backspace,
    Delete,
    Left,
    Right,
    Up,
    Down,
    Home,
    End,
    Enter,
    Tab,
    SelectAll,
    Undo,
    Redo,
    Cut,
    Copy,
    ComposeStart,
    ComposeUpdate(Vec<char>, usize),
    ComposeCommit,
    ComposeCancel,
}

impl View for RuntimeKeyEventKind {
    type V = KeyEventKind;
    open spec fn view(&self) -> KeyEventKind {
        match self {
            RuntimeKeyEventKind::Char(c) => KeyEventKind::Char(*c),
            RuntimeKeyEventKind::Backspace => KeyEventKind::Backspace,
            RuntimeKeyEventKind::Delete => KeyEventKind::Delete,
            RuntimeKeyEventKind::Left => KeyEventKind::Left,
            RuntimeKeyEventKind::Right => KeyEventKind::Right,
            RuntimeKeyEventKind::Up => KeyEventKind::Up,
            RuntimeKeyEventKind::Down => KeyEventKind::Down,
            RuntimeKeyEventKind::Home => KeyEventKind::Home,
            RuntimeKeyEventKind::End => KeyEventKind::End,
            RuntimeKeyEventKind::Enter => KeyEventKind::Enter,
            RuntimeKeyEventKind::Tab => KeyEventKind::Tab,
            RuntimeKeyEventKind::SelectAll => KeyEventKind::SelectAll,
            RuntimeKeyEventKind::Undo => KeyEventKind::Undo,
            RuntimeKeyEventKind::Redo => KeyEventKind::Redo,
            RuntimeKeyEventKind::Cut => KeyEventKind::Cut,
            RuntimeKeyEventKind::Copy => KeyEventKind::Copy,
            RuntimeKeyEventKind::ComposeStart => KeyEventKind::ComposeStart,
            RuntimeKeyEventKind::ComposeUpdate(text, cursor) =>
                KeyEventKind::ComposeUpdate(text@, *cursor as nat),
            RuntimeKeyEventKind::ComposeCommit => KeyEventKind::ComposeCommit,
            RuntimeKeyEventKind::ComposeCancel => KeyEventKind::ComposeCancel,
        }
    }
}

pub struct RuntimeKeyEvent {
    pub kind: RuntimeKeyEventKind,
    pub modifiers: RuntimeModifiers,
}

impl View for RuntimeKeyEvent {
    type V = KeyEvent;
    open spec fn view(&self) -> KeyEvent {
        KeyEvent {
            kind: self.kind@,
            modifiers: self.modifiers@,
        }
    }
}

/// Runtime result of key dispatch.
pub enum RuntimeKeyAction {
    NewModel(RuntimeTextModel),
    External(ExternalAction),
    None,
}

// ── Key dispatch helpers ─────────────────────────────────────────

fn key_to_move_direction_exec(event: &RuntimeKeyEvent) -> (result: Option<MoveDirection>)
    ensures
        match (result, key_to_move_direction(event@)) {
            (Some(a), Some(b)) => a === b,
            (None, None) => true,
            _ => false,
        },
{
    match event.kind {
        RuntimeKeyEventKind::Left => {
            if event.modifiers.ctrl {
                Some(MoveDirection::WordLeft)
            } else {
                Some(MoveDirection::Left)
            }
        },
        RuntimeKeyEventKind::Right => {
            if event.modifiers.ctrl {
                Some(MoveDirection::WordRight)
            } else {
                Some(MoveDirection::Right)
            }
        },
        RuntimeKeyEventKind::Up => Some(MoveDirection::Up),
        RuntimeKeyEventKind::Down => Some(MoveDirection::Down),
        RuntimeKeyEventKind::Home => {
            if event.modifiers.ctrl {
                Some(MoveDirection::Home)
            } else {
                Some(MoveDirection::LineStart)
            }
        },
        RuntimeKeyEventKind::End => {
            if event.modifiers.ctrl {
                Some(MoveDirection::End)
            } else {
                Some(MoveDirection::LineEnd)
            }
        },
        _ => None,
    }
}

// ── Key dispatch exec ────────────────────────────────────────────

/// Dispatch a keyboard event to the text model.
/// Returns None for events not handled, External for undo/clipboard,
/// or NewModel with the updated model.
///
/// Note: this is external_body because the full dispatch_key spec
/// involves many preconditions per branch that must be checked at runtime.
/// The exec function checks runtime preconditions and delegates to
/// the corresponding exec editing functions.
#[verifier::external_body]
pub fn dispatch_key_exec(
    model: RuntimeTextModel,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeKeyAction)
    requires model.wf_spec(),
{
    use crate::runtime::text_model::*;

    match &event.kind {
        RuntimeKeyEventKind::Char(ch) => {
            let ch = *ch;
            if ch == '\0' || ch == '\u{FFF9}' || ch == '\u{FFFA}' || ch == '\u{FFFB}' || ch == '\r' {
                return RuntimeKeyAction::None;
            }
            // Check splice preconditions
            let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
            let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
            if model.text.len() + 1 >= usize::MAX && sel_start == sel_end {
                return RuntimeKeyAction::None;
            }
            RuntimeKeyAction::NewModel(insert_char_exec(model, ch))
        },
        RuntimeKeyEventKind::Enter => {
            let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
            let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
            if model.text.len() + 1 >= usize::MAX && sel_start == sel_end {
                return RuntimeKeyAction::None;
            }
            RuntimeKeyAction::NewModel(insert_char_exec(model, '\n'))
        },
        RuntimeKeyEventKind::Tab => {
            let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
            let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
            if model.text.len() + 1 >= usize::MAX && sel_start == sel_end {
                return RuntimeKeyAction::None;
            }
            RuntimeKeyAction::NewModel(insert_char_exec(model, '\t'))
        },
        RuntimeKeyEventKind::Backspace => {
            if model.anchor != model.focus {
                RuntimeKeyAction::NewModel(delete_selection_exec(model))
            } else if model.focus == 0 {
                RuntimeKeyAction::None
            } else if event.modifiers.ctrl {
                if model.text.len() == 0 {
                    RuntimeKeyAction::None
                } else {
                    RuntimeKeyAction::NewModel(delete_word_backward_exec(model))
                }
            } else {
                if model.text.len() == 0 {
                    RuntimeKeyAction::None
                } else {
                    RuntimeKeyAction::NewModel(delete_backward_exec(model))
                }
            }
        },
        RuntimeKeyEventKind::Delete => {
            if model.anchor != model.focus {
                RuntimeKeyAction::NewModel(delete_selection_exec(model))
            } else if model.focus >= model.text.len() {
                RuntimeKeyAction::None
            } else if event.modifiers.ctrl {
                if model.text.len() == 0 {
                    RuntimeKeyAction::None
                } else {
                    RuntimeKeyAction::NewModel(delete_word_forward_exec(model))
                }
            } else {
                RuntimeKeyAction::NewModel(delete_forward_exec(model))
            }
        },
        RuntimeKeyEventKind::SelectAll => {
            RuntimeKeyAction::NewModel(select_all_exec(model))
        },
        RuntimeKeyEventKind::Undo => RuntimeKeyAction::External(ExternalAction::Undo),
        RuntimeKeyEventKind::Redo => RuntimeKeyAction::External(ExternalAction::Redo),
        RuntimeKeyEventKind::Cut => RuntimeKeyAction::External(ExternalAction::Cut),
        RuntimeKeyEventKind::Copy => RuntimeKeyAction::External(ExternalAction::Copy),
        RuntimeKeyEventKind::ComposeStart => {
            if model.composition.is_some() {
                return RuntimeKeyAction::None;
            }
            RuntimeKeyAction::NewModel(compose_start_exec(model))
        },
        RuntimeKeyEventKind::ComposeUpdate(text, cursor) => {
            if model.composition.is_none() || *cursor > text.len() {
                return RuntimeKeyAction::None;
            }
            // Copy text since we can't move it out of the ref
            let mut prov: Vec<char> = Vec::new();
            let mut pi: usize = 0;
            while pi < text.len() {
                prov.push(text[pi]);
                pi += 1;
            }
            RuntimeKeyAction::NewModel(compose_update_exec(model, prov, *cursor))
        },
        RuntimeKeyEventKind::ComposeCommit => {
            if model.composition.is_none() {
                return RuntimeKeyAction::None;
            }
            RuntimeKeyAction::NewModel(compose_commit_exec(model))
        },
        RuntimeKeyEventKind::ComposeCancel => {
            RuntimeKeyAction::NewModel(compose_cancel_exec(model))
        },
        _ => {
            // Arrow/Home/End keys
            let dir_opt = key_to_move_direction_exec(event);
            match dir_opt {
                Some(dir) => {
                    if model.text.len() >= usize::MAX {
                        return RuntimeKeyAction::None;
                    }
                    if event.modifiers.shift {
                        RuntimeKeyAction::NewModel(extend_selection_exec(model, dir))
                    } else {
                        RuntimeKeyAction::NewModel(move_cursor_exec(model, dir))
                    }
                },
                None => RuntimeKeyAction::None,
            }
        },
    }
}

} // verus!
