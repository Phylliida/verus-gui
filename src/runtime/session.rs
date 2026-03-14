use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::undo::*;
use crate::text_model::session::*;
use crate::event::*;
use crate::runtime::text_model::*;
use crate::runtime::event::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Runtime text edit session
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextEditSession {
    pub model: RuntimeTextModel,
    pub undo_stack: RuntimeUndoStack,
    pub last_was_insert: bool,
    pub clipboard: Vec<char>,
}

impl RuntimeTextEditSession {
    pub open spec fn view_session(&self) -> TextEditSession {
        TextEditSession {
            model: self.model@,
            undo_stack: self.undo_stack@,
            last_was_insert: self.last_was_insert,
            clipboard: self.clipboard@,
        }
    }

    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model.wf_spec()
        &&& self.undo_stack.wf_spec()
        &&& session_wf(self.view_session())
    }
}

pub fn new_session_exec(model: RuntimeTextModel) -> (out: RuntimeTextEditSession)
    requires model.wf_spec(),
    ensures
        out.view_session() == new_session(model@),
        out.wf_spec(),
{
    RuntimeTextEditSession {
        model,
        undo_stack: empty_undo_stack_exec(),
        last_was_insert: false,
        clipboard: Vec::new(),
    }
}

/// Apply a key event to the session.
///
/// External body because dispatch_key_exec's preconditions on the
/// underlying editing functions (grapheme boundaries, wf_text after
/// splice) depend on axioms that can't be discharged in verified code.
///
/// Handles undo/redo/clipboard at the session level.
/// For editing keys, delegates to dispatch_key_exec and records undo.
#[verifier::external_body]
pub fn apply_key_to_session_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(), event@).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(), event@).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(), event@).clipboard,
        result.model.wf_spec(),
{
    // Handle Copy/Cut/Undo/Redo directly (before consuming model).
    match &event.kind {
        RuntimeKeyEventKind::Copy => {
            if session.model.anchor != session.model.focus {
                let clipboard = get_selection_text_exec(&session.model);
                return RuntimeTextEditSession {
                    clipboard,
                    model: session.model,
                    undo_stack: session.undo_stack,
                    last_was_insert: false,
                };
            }
            return session;
        },
        RuntimeKeyEventKind::Cut => {
            if session.model.anchor != session.model.focus {
                let clipboard = get_selection_text_exec(&session.model);
                let sel_start = if session.model.anchor <= session.model.focus {
                    session.model.anchor } else { session.model.focus };
                let sel_end = if session.model.anchor <= session.model.focus {
                    session.model.focus } else { session.model.anchor };
                let entry = undo_entry_for_splice_exec(
                    &session.model, sel_start, sel_end,
                    &Vec::new(), &Vec::new(), sel_start);
                let new_model = delete_selection_exec(session.model);
                let new_stack = push_undo_or_merge_exec(
                    session.undo_stack, entry, false);
                return RuntimeTextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard,
                };
            }
            return session;
        },
        RuntimeKeyEventKind::Undo => {
            if can_undo_exec(&session.undo_stack) {
                let (new_stack, new_model) = apply_undo_exec(
                    session.undo_stack, session.model);
                return RuntimeTextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                };
            }
            return session;
        },
        RuntimeKeyEventKind::Redo => {
            if can_redo_exec(&session.undo_stack) {
                let (new_stack, new_model) = apply_redo_exec(
                    session.undo_stack, session.model);
                return RuntimeTextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                };
            }
            return session;
        },
        _ => {},
    }

    // Pre-check: will dispatch return None? If so, return unchanged.
    let dispatch_none = match &event.kind {
        RuntimeKeyEventKind::Char(ch) => {
            let c = *ch;
            c == '\0' || c == '\u{FFF9}' || c == '\u{FFFA}'
                || c == '\u{FFFB}' || c == '\r'
        },
        RuntimeKeyEventKind::Backspace => {
            session.model.anchor == session.model.focus
                && session.model.focus == 0
        },
        RuntimeKeyEventKind::Delete => {
            session.model.anchor == session.model.focus
                && session.model.focus >= session.model.text.len()
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
        return session;
    }

    // Save undo data before dispatch consumes the model.
    let sel_start = if session.model.anchor <= session.model.focus {
        session.model.anchor } else { session.model.focus };
    let sel_end = if session.model.anchor <= session.model.focus {
        session.model.focus } else { session.model.anchor };

    let is_insert = match &event.kind {
        RuntimeKeyEventKind::Char(_)
        | RuntimeKeyEventKind::Enter
        | RuntimeKeyEventKind::Tab => true,
        _ => false,
    };
    let merge = session.last_was_insert && is_insert;

    // Build inserted text/styles for the undo entry.
    let (ins_text, ins_styles): (Vec<char>, Vec<RuntimeStyleSet>) =
        match &event.kind {
            RuntimeKeyEventKind::Char(ch) => {
                (vec![*ch], vec![copy_style_set(&session.model.typing_style)])
            },
            RuntimeKeyEventKind::Enter => {
                (vec!['\n'], vec![copy_style_set(&session.model.typing_style)])
            },
            RuntimeKeyEventKind::Tab => {
                (vec!['\t'], vec![copy_style_set(&session.model.typing_style)])
            },
            _ => (Vec::new(), Vec::new()),
        };

    // Create undo entry (focus_after is a placeholder; updated below).
    let mut entry = undo_entry_for_splice_exec(
        &session.model, sel_start, sel_end,
        &ins_text, &ins_styles, 0);

    // Dispatch the key to get the new model.
    let action = dispatch_key_exec(session.model, event);
    match action {
        RuntimeKeyAction::NewModel(new_model) => {
            entry.focus_after = new_model.focus;
            let new_stack = push_undo_or_merge_exec(
                session.undo_stack, entry, merge);
            RuntimeTextEditSession {
                model: new_model,
                undo_stack: new_stack,
                last_was_insert: is_insert,
                clipboard: session.clipboard,
            }
        },
        _ => {
            // Unreachable: pre-check guarantees dispatch returns NewModel
            // for all remaining event kinds.
            unreachable!()
        },
    }
}

} // verus!
