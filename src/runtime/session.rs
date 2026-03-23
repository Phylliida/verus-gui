use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::proofs::*;
use crate::text_model::undo::*;
use crate::text_model::undo_proofs::*;
use crate::text_model::session::*;
use crate::text_model::paragraph_proofs::*;
use crate::text_model::find::*;
use crate::event::*;
use crate::runtime::text_model::*;
use crate::runtime::event::*;
use crate::runtime::session_helpers::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Runtime text edit session
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextEditSession {
    pub model: RuntimeTextModel,
    pub undo_stack: RuntimeUndoStack,
    pub last_was_insert: bool,
    pub clipboard: Vec<char>,
    pub history: Ghost<Seq<Seq<char>>>,
    pub style_history: Ghost<Seq<Seq<StyleSet>>>,
}

impl RuntimeTextEditSession {
    pub open spec fn view_session(&self) -> TextEditSession {
        TextEditSession {
            model: self.model@,
            undo_stack: self.undo_stack@,
            last_was_insert: self.last_was_insert,
            clipboard: self.clipboard@,
            history: self.history@,
            style_history: self.style_history@,
        }
    }

    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model.wf_spec()
        &&& self.undo_stack.wf_spec()
        &&& session_wf(self.view_session())
    }
}

// ── Non-text-edit helper ────────────────────────────────────────────

/// Handle a non-text-modifying NewModel operation (compose_start/update/cancel,
/// select_all, move_cursor, extend_selection). No undo entry is pushed.
fn session_handle_non_text_edit_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.model@.composition.is_some() ==>
            session.model@.text.len()
                + session.model@.composition.unwrap().provisional.len()
                < usize::MAX,
        !is_text_edit_key(event@.kind, session.model@),
        match dispatch_key(session.model@, event@) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(), event@).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(), event@).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(), event@).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    proof { lemma_apply_key_non_text_edit(session.view_session(), event@); }
    let clipboard = session.clipboard;
    let ghost old_model = session.model@;
    let ghost old_stack = session.undo_stack@;
    let ghost old_history = session.history@;
    let undo_stack = session.undo_stack;
    let history = session.history;
    let style_history = session.style_history;
    let action = dispatch_key_exec(session.model, event);
    match action {
        RuntimeKeyAction::NewModel(new_model) => {
            proof {
            }
            RuntimeTextEditSession {
                model: new_model,
                undo_stack,
                last_was_insert: false,
                clipboard,
                history,
                style_history,
            }
        },
        _ => {
            proof { assert(false); }
            dead_session(undo_stack, clipboard, history, style_history)
        },
    }
}

// ── Text-edit helper ───────────────────────────────────────────────

/// Handle a text-modifying NewModel operation with correct undo entry.
fn session_handle_text_edit_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.undo_stack.entries.len() < usize::MAX,
        session.model@.composition.is_some() ==>
            session.model@.text.len()
                + session.model@.composition.unwrap().provisional.len()
                < usize::MAX,
        is_text_edit_key(event@.kind, session.model@),
        // dispatch returns NewModel (caller checked dispatch_none):
        match dispatch_key(session.model@, event@) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(), event@).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(), event@).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(), event@).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    let is_insert = match &event.kind {
        RuntimeKeyEventKind::Char(_)
        | RuntimeKeyEventKind::Enter
        | RuntimeKeyEventKind::Tab => true,
        _ => false,
    };
    let merge = session.last_was_insert && is_insert;

    let (undo_start, undo_end, ins_text, ins_styles) =
        undo_splice_params_full_exec(&session.model, event);

    let mut entry = undo_entry_for_splice_exec(
        &session.model, undo_start, undo_end,
        &ins_text, &ins_styles, 0);

    let ghost old_model = session.model@;
    let clipboard = session.clipboard;
    let undo_stack = session.undo_stack;
    let ghost old_stack = undo_stack@;
    let ghost old_history = session.history@;
    let ghost old_style_history = session.style_history@;
    let history = session.history;
    let style_history = session.style_history;
    let action = dispatch_key_exec(session.model, event);
    match action {
        RuntimeKeyAction::NewModel(new_model) => {
            entry.focus_after = new_model.focus;
            let new_stack = push_undo_or_merge_exec(
                undo_stack, entry, merge);
            let ghost new_history = update_history_for_push(
                old_stack, old_history, entry@, new_model@.text, merge);
            let ghost new_style_history = update_style_history_for_push(
                old_stack, old_style_history, entry@, new_model@.styles, merge);
            proof {
                // Bridge: apply_key_to_session output fields
                lemma_apply_key_text_edit(session.view_session(), event@);
                // Bridge: undo params produce same text/styles as dispatch
                lemma_undo_params_match_dispatch(event@, old_model);
                // Prove entry_describes_transition
                lemma_entry_for_splice_describes_transition(
                    old_model, undo_start as nat, undo_end as nat,
                    ins_text@, style_seq_view(ins_styles@), new_model@.focus);
                // Prove push_or_merge maintains history validity
                lemma_push_or_merge_history_valid(
                    old_stack, old_history, entry@, new_model@.text, merge);
                // Style history
                lemma_entry_for_splice_describes_style_transition(
                    old_model, undo_start as nat, undo_end as nat,
                    ins_text@, style_seq_view(ins_styles@), new_model@.focus);
                lemma_push_or_merge_style_history_valid(
                    old_stack, old_style_history, entry@, new_model@.styles, merge);
            }
            RuntimeTextEditSession {
                model: new_model,
                undo_stack: new_stack,
                last_was_insert: is_insert,
                clipboard,
                history: Ghost(new_history),
                style_history: Ghost(new_style_history),
            }
        },
        _ => {
            proof { assert(false); }
            dead_session(undo_stack, clipboard, history, style_history)
        },
    }
}

// ── Input event handler (non-external-action) ───────────────────────

/// Handle input events (not Copy/Cut/Undo/Redo/Paste).
/// Checks for dispatch-none, classifies text-edit vs non-text-edit,
/// and dispatches to the appropriate handler.
/// Separated from `apply_key_to_session_exec` to reduce Z3 path explosion.
fn session_handle_input_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.undo_stack.entries.len() < usize::MAX,
        session.model@.composition.is_some() ==>
            session.model@.text.len()
                + session.model@.composition.unwrap().provisional.len()
                < usize::MAX,
        // dispatch_key does not return External for this event
        match dispatch_key(session.model@, event@) {
            KeyAction::External(_) => false,
            _ => true,
        },
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(), event@).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(), event@).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(), event@).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    // Pre-check: will dispatch return None? If so, return unchanged.
    let dispatch_none = match &event.kind {
        RuntimeKeyEventKind::Char(ch) => {
            let c = *ch;
            session.model.composition.is_some()
                || c == '\0' || c == '\u{FFF9}' || c == '\u{FFFA}'
                || c == '\u{FFFB}' || c == '\r'
        },
        RuntimeKeyEventKind::Enter | RuntimeKeyEventKind::Tab => {
            session.model.composition.is_some()
        },
        RuntimeKeyEventKind::Backspace => {
            session.model.composition.is_some()
                || (session.model.anchor == session.model.focus
                    && session.model.focus == 0)
        },
        RuntimeKeyEventKind::Delete => {
            session.model.composition.is_some()
                || (session.model.anchor == session.model.focus
                    && session.model.focus >= session.model.text.len())
        },
        RuntimeKeyEventKind::ComposeStart =>
            session.model.composition.is_some(),
        RuntimeKeyEventKind::ComposeUpdate(text, cursor) =>
            session.model.composition.is_none() || *cursor > text.len(),
        RuntimeKeyEventKind::ComposeCommit =>
            session.model.composition.is_none(),
        _ => false,
    };
    if dispatch_none {
        proof { lemma_apply_key_noop(session.view_session(), event@); }
        return session;
    }

    // Determine if this is a text-modifying operation that needs an undo entry.
    let is_text_edit = match &event.kind {
        RuntimeKeyEventKind::Char(_)
        | RuntimeKeyEventKind::Enter
        | RuntimeKeyEventKind::Tab
        | RuntimeKeyEventKind::Backspace
        | RuntimeKeyEventKind::Delete
        | RuntimeKeyEventKind::ComposeCommit => true,
        _ => false,
    };

    if is_text_edit {
        session_handle_text_edit_exec(session, event)
    } else {
        session_handle_non_text_edit_exec(session, event)
    }
}

// ── Main session dispatch ───────────────────────────────────────────

/// Apply a key event to the session.
///
/// Fully verified including Undo/Redo via ghost history tracking.
pub fn apply_key_to_session_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.undo_stack.entries.len() < usize::MAX,
        session.model@.composition.is_some() ==>
            session.model@.text.len()
                + session.model@.composition.unwrap().provisional.len()
                < usize::MAX,
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(), event@).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(), event@).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(), event@).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    match &event.kind {
        RuntimeKeyEventKind::Copy =>
            return session_copy_arm_exec(session, event),
        RuntimeKeyEventKind::Cut =>
            return session_cut_arm_exec(session, event),
        RuntimeKeyEventKind::Undo =>
            return session_undo_arm_exec(session, event),
        RuntimeKeyEventKind::Redo =>
            return session_redo_arm_exec(session, event),
        RuntimeKeyEventKind::Paste =>
            return session_paste_arm_exec(session, event),
        _ => {},
    }
    session_handle_input_exec(session, event)
}

} // verus!
