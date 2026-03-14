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
    Paste,
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
            RuntimeKeyEventKind::Paste => KeyEventKind::Paste,
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

// ── Key dispatch helpers (split for rlimit) ─────────────────────

/// Handle Char/Enter/Tab insertion.
fn dispatch_insert_char_exec(
    model: RuntimeTextModel, ch: char,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model.text.len() + 2 < usize::MAX,
        is_permitted(ch),
        ch != '\r',
    ensures
        match (result, KeyAction::NewModel(insert_char(model@, ch))) {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    proof {
        lemma_single_permitted_char_wf(ch);
        axiom_splice_wf(model@.text, sel_start as nat, sel_end as nat, seq![ch]);
    }
    RuntimeKeyAction::NewModel(insert_char_exec(model, ch))
}

/// Handle Backspace key.
fn dispatch_backspace_exec(
    model: RuntimeTextModel, ctrl: bool,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model.text.len() + 2 < usize::MAX,
        model@.composition.is_none(),
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::Backspace, modifiers: Modifiers { shift: false, ctrl, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    if model.anchor != model.focus {
        let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
        let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
        proof {
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, sel_start as nat, sel_end as nat, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_selection_exec(model))
    } else if model.focus == 0 {
        RuntimeKeyAction::None
    } else if ctrl {
        proof {
            axiom_prev_word_boundary_valid(model@.text, model@.focus);
            let prev = prev_boundary_in(word_start_boundaries(model@.text), model@.focus);
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, prev, model@.focus, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_word_backward_exec(model))
    } else {
        proof {
            axiom_prev_grapheme_boundary_valid(model@.text, model@.focus);
            let prev = prev_grapheme_boundary(model@.text, model@.focus);
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, prev, model@.focus, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_backward_exec(model))
    }
}

/// Handle Delete key.
fn dispatch_delete_exec(
    model: RuntimeTextModel, ctrl: bool,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model.text.len() + 2 < usize::MAX,
        model@.composition.is_none(),
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::Delete, modifiers: Modifiers { shift: false, ctrl, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    if model.anchor != model.focus {
        let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
        let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
        proof {
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, sel_start as nat, sel_end as nat, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_selection_exec(model))
    } else if model.focus >= model.text.len() {
        RuntimeKeyAction::None
    } else if ctrl {
        proof {
            axiom_next_word_boundary_valid(model@.text, model@.focus);
            let next = next_boundary_in(word_end_boundaries(model@.text), model@.focus);
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, model@.focus, next, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_word_forward_exec(model))
    } else {
        proof {
            axiom_next_grapheme_boundary_valid(model@.text, model@.focus);
            let next = next_grapheme_boundary(model@.text, model@.focus);
            lemma_empty_seq_wf();
            axiom_splice_wf(model@.text, model@.focus, next, Seq::<char>::empty());
        }
        RuntimeKeyAction::NewModel(delete_forward_exec(model))
    }
}

/// Handle ComposeStart.
fn dispatch_compose_start_exec(
    model: RuntimeTextModel,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::ComposeStart, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    if model.composition.is_some() {
        RuntimeKeyAction::None
    } else {
        RuntimeKeyAction::NewModel(compose_start_exec(model))
    }
}

/// Handle ComposeUpdate.
fn dispatch_compose_update_exec(
    model: RuntimeTextModel,
    text: &Vec<char>,
    cursor: usize,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::ComposeUpdate(text@, cursor as nat), modifiers: Modifiers { shift: false, ctrl: false, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    if model.composition.is_none() || cursor > text.len() {
        RuntimeKeyAction::None
    } else {
        let mut prov: Vec<char> = Vec::new();
        let mut pi: usize = 0;
        while pi < text.len()
            invariant
                pi <= text@.len(),
                prov@.len() == pi as nat,
                forall|k: int| 0 <= k < pi ==> prov@[k] == text@[k],
            decreases text@.len() - pi,
        {
            prov.push(text[pi]);
            pi += 1;
        }
        assert(prov@ =~= text@);
        RuntimeKeyAction::NewModel(compose_update_exec(model, prov, cursor))
    }
}

/// Handle ComposeCommit.
fn dispatch_compose_commit_exec(
    model: RuntimeTextModel,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model@.composition.is_some() ==>
            model@.text.len() + model@.composition.unwrap().provisional.len()
                < usize::MAX,
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::ComposeCommit, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    if model.composition.is_none() {
        RuntimeKeyAction::None
    } else {
        proof {
            let c = model@.composition.unwrap();
            axiom_compose_commit_wf(
                model@.text, c.range_start, c.range_end, c.provisional);
            assert(c.range_start <= c.range_end);
            assert(c.range_end <= model@.text.len());
            assert(model@.text.len() + c.provisional.len() < usize::MAX);
            assert(model@.text.len() - (c.range_end - c.range_start) + c.provisional.len()
                <= model@.text.len() + c.provisional.len());
        }
        RuntimeKeyAction::NewModel(compose_commit_exec(model))
    }
}

/// Handle ComposeCancel.
fn dispatch_compose_cancel_exec(
    model: RuntimeTextModel,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
    ensures
        match (result, dispatch_key(model@,
            KeyEvent { kind: KeyEventKind::ComposeCancel, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }))
        {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    RuntimeKeyAction::NewModel(compose_cancel_exec(model))
}

/// Handle movement keys (arrow, home, end).
fn dispatch_movement_exec(
    model: RuntimeTextModel,
    event: &RuntimeKeyEvent,
    dir: MoveDirection,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model.text.len() + 2 < usize::MAX,
        key_to_move_direction(event@) == Some(dir),
    ensures
        match (result, dispatch_key(model@, event@)) {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(sm)) =>
                rm@ == sm && rm.wf_spec(),
            _ => false,
        },
{
    use crate::runtime::text_model::*;
    proof {
        axiom_movement_valid(
            model@.text, model@.focus, model@.focus_affinity,
            model@.preferred_column, dir);
    }
    if event.modifiers.shift {
        RuntimeKeyAction::NewModel(extend_selection_exec(model, dir))
    } else {
        RuntimeKeyAction::NewModel(move_cursor_exec(model, dir))
    }
}

// ── Key dispatch exec ────────────────────────────────────────────

/// Dispatch a keyboard event to the text model.
/// Returns None for events not handled, External for undo/clipboard,
/// or NewModel with the updated model.
///
/// Verified against the spec `dispatch_key`. Delegates to per-category
/// helpers to keep each function within rlimit.
pub fn dispatch_key_exec(
    model: RuntimeTextModel,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeKeyAction)
    requires
        model.wf_spec(),
        model.text.len() + 2 < usize::MAX,
        model@.composition.is_some() ==>
            model@.text.len() + model@.composition.unwrap().provisional.len()
                < usize::MAX,
    ensures
        match (result, dispatch_key(model@, event@)) {
            (RuntimeKeyAction::NewModel(rm), KeyAction::NewModel(_sm)) =>
                rm@ == _sm && rm.wf_spec(),
            (RuntimeKeyAction::External(ea), KeyAction::External(eb)) => ea === eb,
            (RuntimeKeyAction::None, KeyAction::None) => true,
            _ => false,
        },
{
    match &event.kind {
        RuntimeKeyEventKind::Char(ch) => {
            let ch = *ch;
            if model.composition.is_some() {
                RuntimeKeyAction::None
            } else if ch == '\0' || ch == '\u{FFF9}' || ch == '\u{FFFA}' || ch == '\u{FFFB}' || ch == '\r' {
                RuntimeKeyAction::None
            } else {
                dispatch_insert_char_exec(model, ch)
            }
        },
        RuntimeKeyEventKind::Enter => {
            if model.composition.is_some() {
                RuntimeKeyAction::None
            } else {
                dispatch_insert_char_exec(model, '\n')
            }
        },
        RuntimeKeyEventKind::Tab => {
            if model.composition.is_some() {
                RuntimeKeyAction::None
            } else {
                dispatch_insert_char_exec(model, '\t')
            }
        },
        RuntimeKeyEventKind::Backspace => {
            if model.composition.is_some() {
                RuntimeKeyAction::None
            } else {
                dispatch_backspace_exec(model, event.modifiers.ctrl)
            }
        },
        RuntimeKeyEventKind::Delete => {
            if model.composition.is_some() {
                RuntimeKeyAction::None
            } else {
                dispatch_delete_exec(model, event.modifiers.ctrl)
            }
        },
        RuntimeKeyEventKind::SelectAll => {
            use crate::runtime::text_model::*;
            RuntimeKeyAction::NewModel(select_all_exec(model))
        },
        RuntimeKeyEventKind::Undo => RuntimeKeyAction::External(ExternalAction::Undo),
        RuntimeKeyEventKind::Redo => RuntimeKeyAction::External(ExternalAction::Redo),
        RuntimeKeyEventKind::Cut => RuntimeKeyAction::External(ExternalAction::Cut),
        RuntimeKeyEventKind::Copy => RuntimeKeyAction::External(ExternalAction::Copy),
        RuntimeKeyEventKind::Paste => RuntimeKeyAction::External(ExternalAction::Paste),
        RuntimeKeyEventKind::ComposeStart => {
            dispatch_compose_start_exec(model)
        },
        RuntimeKeyEventKind::ComposeUpdate(text, cursor) => {
            dispatch_compose_update_exec(model, text, *cursor)
        },
        RuntimeKeyEventKind::ComposeCommit => {
            dispatch_compose_commit_exec(model)
        },
        RuntimeKeyEventKind::ComposeCancel => {
            dispatch_compose_cancel_exec(model)
        },
        _ => {
            let dir_opt = key_to_move_direction_exec(event);
            match dir_opt {
                Some(dir) => dispatch_movement_exec(model, event, dir),
                None => RuntimeKeyAction::None,
            }
        },
    }
}

} // verus!
