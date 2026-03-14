use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::undo::*;
use crate::text_model::undo_proofs::*;
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
    pub history: Ghost<Seq<Seq<char>>>,
}

impl RuntimeTextEditSession {
    pub open spec fn view_session(&self) -> TextEditSession {
        TextEditSession {
            model: self.model@,
            undo_stack: self.undo_stack@,
            last_was_insert: self.last_was_insert,
            clipboard: self.clipboard@,
            history: self.history@,
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
    let ghost init_text = model@.text;
    RuntimeTextEditSession {
        model,
        undo_stack: empty_undo_stack_exec(),
        last_was_insert: false,
        clipboard: Vec::new(),
        history: Ghost(Seq::empty().push(init_text)),
    }
}

// ── Undo/Redo helpers ───────────────────────────────────────────────

/// Apply undo at the session level. Now verified via ghost history.
fn session_apply_undo_exec(
    session: RuntimeTextEditSession,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        can_undo(session.undo_stack@),
        session.model@.composition.is_none(),
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Undo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Undo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Undo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    proof {
        lemma_undo_preconditions_from_history(
            session.undo_stack@, session.history@, session.model@.text);
    }
    let (new_stack, new_model) = apply_undo_exec(
        session.undo_stack, session.model);
    proof {
        lemma_undo_maintains_history(session.undo_stack@, session.history@);
        lemma_undo_history_position(
            session.undo_stack@, session.history@, session.view_session().model);
    }
    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: session.history,
    }
}

/// Apply redo at the session level. Now verified via ghost history.
fn session_apply_redo_exec(
    session: RuntimeTextEditSession,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        can_redo(session.undo_stack@),
        session.model@.composition.is_none(),
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Redo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Redo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Redo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    proof {
        lemma_redo_preconditions_from_history(
            session.undo_stack@, session.history@, session.model@.text);
    }
    let (new_stack, new_model) = apply_redo_exec(
        session.undo_stack, session.model);
    proof {
        lemma_redo_maintains_history(session.undo_stack@, session.history@);
        lemma_redo_history_position(
            session.undo_stack@, session.history@, session.view_session().model);
    }
    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: session.history,
    }
}

/// Helper for unreachable branches — requires false so can never be called
/// in valid execution. Used to satisfy Rust's type checker.
#[verifier::external_body]
fn dead_session(undo_stack: RuntimeUndoStack, clipboard: Vec<char>, history: Ghost<Seq<Seq<char>>>) -> (out: RuntimeTextEditSession)
    requires false,
{ unreachable!() }

// ── Main session dispatch ───────────────────────────────────────────

/// Apply a key event to the session.
///
/// Fully verified including Undo/Redo via ghost history tracking.
#[verifier::rlimit(50)]
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
{
    // Handle Copy/Cut/Undo/Redo directly (before consuming model).
    match &event.kind {
        RuntimeKeyEventKind::Copy => {
            if session.model.anchor != session.model.focus {
                let clipboard = get_selection_text_exec(&session.model);
                return RuntimeTextEditSession {
                    clipboard,
                    last_was_insert: session.last_was_insert,
                    model: session.model,
                    undo_stack: session.undo_stack,
                    history: session.history,
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
                proof {
                    axiom_splice_delete_wf(session.model@.text, sel_start as nat, sel_end as nat);
                }
                let entry = undo_entry_for_splice_exec(
                    &session.model, sel_start, sel_end,
                    &Vec::new(), &Vec::new(), sel_start);
                let ghost old_stack = session.undo_stack@;
                let ghost old_history = session.history@;
                let new_model = delete_selection_exec(session.model);
                let new_stack = push_undo_or_merge_exec(
                    session.undo_stack, entry, false);
                let ghost new_history = update_history_for_push(
                    old_stack, old_history, entry@, new_model@.text, false);
                return RuntimeTextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard,
                    history: Ghost(new_history),
                };
            }
            return session;
        },
        RuntimeKeyEventKind::Undo => {
            if can_undo_exec(&session.undo_stack) {
                if session.model.composition.is_none() {
                    return session_apply_undo_exec(session);
                }
            }
            return session;
        },
        RuntimeKeyEventKind::Redo => {
            if can_redo_exec(&session.undo_stack) {
                if session.model.composition.is_none() {
                    return session_apply_redo_exec(session);
                }
            }
            return session;
        },
        _ => {},
    }

    // Focus Z3 — session_wf expanded context no longer needed past early returns
    proof {
        assert(session.model.wf_spec());
        assert(session.undo_stack.wf_spec());
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
    // Save clipboard before model is consumed.
    let clipboard = session.clipboard;
    let undo_stack = session.undo_stack;
    let ghost old_stack = undo_stack@;
    let ghost old_history = session.history@;
    let history = session.history;
    let action = dispatch_key_exec(session.model, event);
    match action {
        RuntimeKeyAction::NewModel(new_model) => {
            entry.focus_after = new_model.focus;
            let new_stack = push_undo_or_merge_exec(
                undo_stack, entry, merge);
            let ghost new_history = update_history_for_push(
                old_stack, old_history, entry@, new_model@.text, merge);
            RuntimeTextEditSession {
                model: new_model,
                undo_stack: new_stack,
                last_was_insert: is_insert,
                clipboard,
                history: Ghost(new_history),
            }
        },
        _ => {
            // Unreachable: Copy/Cut/Undo/Redo return early above,
            // dispatch_none pre-check covers all None cases.
            proof { assert(false); }
            dead_session(undo_stack, clipboard, history)
        },
    }
}

} // verus!
