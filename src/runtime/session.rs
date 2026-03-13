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

/// Apply a key event to the session. External body because the full
/// dispatch involves many preconditions per branch that must be
/// checked at runtime.
///
/// Handles undo/redo/clipboard at the session level.
/// For editing keys, delegates to dispatch_key_exec.
#[verifier::external_body]
pub fn apply_key_to_session_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires session.wf_spec(),
{
    // Handle Copy/Cut/Undo/Redo directly without consuming model.
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
                let new_model = delete_selection_exec(session.model);
                return RuntimeTextEditSession {
                    model: new_model,
                    undo_stack: session.undo_stack,
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

    // For all other keys, delegate to dispatch_key_exec.
    let action = dispatch_key_exec(session.model, event);
    match action {
        RuntimeKeyAction::NewModel(new_model) => {
            let is_insert = match &event.kind {
                RuntimeKeyEventKind::Char(_) | RuntimeKeyEventKind::Enter
                | RuntimeKeyEventKind::Tab => true,
                _ => false,
            };
            RuntimeTextEditSession {
                model: new_model,
                undo_stack: session.undo_stack,
                last_was_insert: is_insert,
                clipboard: session.clipboard,
            }
        },
        _ => {
            // dispatch returned None or unexpected External.
            // Model was consumed but no change intended.
            panic!("dispatch_key_exec returned None/External for non-external key")
        },
    }
}

} // verus!
