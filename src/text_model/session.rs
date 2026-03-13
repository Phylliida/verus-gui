use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::cursor::*;
use super::undo::*;
use crate::event::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Text edit session
// ──────────────────────────────────────────────────────────────────────

/// A stateful editing session wrapping a TextModel with undo/redo,
/// merge tracking for consecutive character inserts, and clipboard.
pub struct TextEditSession {
    pub model: TextModel,
    pub undo_stack: UndoStack,
    pub last_was_insert: bool,
    pub clipboard: Seq<char>,
}

/// Create a new session from a model with empty undo and clipboard.
pub open spec fn new_session(model: TextModel) -> TextEditSession {
    TextEditSession {
        model,
        undo_stack: empty_undo_stack(),
        last_was_insert: false,
        clipboard: Seq::empty(),
    }
}

/// Well-formedness of a session.
pub open spec fn session_wf(s: TextEditSession) -> bool {
    &&& s.model.wf()
    &&& undo_stack_wf(s.undo_stack)
}

/// Whether a key event kind is a character insertion (Char, Enter, Tab).
pub open spec fn is_insert_key(kind: KeyEventKind) -> bool {
    match kind {
        KeyEventKind::Char(_) => true,
        KeyEventKind::Enter => true,
        KeyEventKind::Tab => true,
        _ => false,
    }
}

/// Helper: record an edit in the session's undo stack from old_model to new_model,
/// using the selection range and splice parameters.
pub open spec fn session_record_edit(
    session: TextEditSession,
    new_model: TextModel,
    start: nat,
    end: nat,
    new_text: Seq<char>,
    new_styles: Seq<StyleSet>,
    new_focus: nat,
    merge: bool,
) -> UndoStack {
    let entry = undo_entry_for_splice(
        session.model, start, end, new_text, new_styles, new_focus);
    push_undo_or_merge(session.undo_stack, entry, merge)
}

/// Apply a key event to the entire session: dispatches via dispatch_key,
/// then handles undo/redo/clipboard at the session level.
pub open spec fn apply_key_to_session(
    session: TextEditSession,
    event: KeyEvent,
) -> TextEditSession {
    match dispatch_key(session.model, event) {
        KeyAction::NewModel(new_model) => {
            let merge = session.last_was_insert && is_insert_key(event.kind);
            let (sel_start, sel_end) = selection_range(session.model.anchor, session.model.focus);
            // Build the undo entry for this edit
            let new_text_for_entry = match event.kind {
                KeyEventKind::Char(ch) => seq![ch],
                KeyEventKind::Enter => seq!['\n'],
                KeyEventKind::Tab => seq!['\t'],
                _ => Seq::empty(),  // deletes have empty new_text
            };
            let new_styles_for_entry = if new_text_for_entry.len() > 0 {
                seq_repeat(session.model.typing_style, new_text_for_entry.len())
            } else {
                Seq::empty()
            };
            let new_focus = new_model.focus;
            let entry = undo_entry_for_splice(
                session.model, sel_start, sel_end,
                new_text_for_entry, new_styles_for_entry, new_focus);
            let new_stack = push_undo_or_merge(session.undo_stack, entry, merge);
            TextEditSession {
                model: new_model,
                undo_stack: new_stack,
                last_was_insert: is_insert_key(event.kind),
                clipboard: session.clipboard,
            }
        },
        KeyAction::External(ExternalAction::Undo) => {
            if can_undo(session.undo_stack) {
                let (new_stack, new_model) = apply_undo(session.undo_stack, session.model);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                }
            } else {
                session
            }
        },
        KeyAction::External(ExternalAction::Redo) => {
            if can_redo(session.undo_stack) {
                let (new_stack, new_model) = apply_redo(session.undo_stack, session.model);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                }
            } else {
                session
            }
        },
        KeyAction::External(ExternalAction::Cut) => {
            if has_selection(session.model.anchor, session.model.focus) {
                let clipboard = get_selection_text(session.model);
                let (sel_start, sel_end) = selection_range(
                    session.model.anchor, session.model.focus);
                let new_model = delete_selection(session.model);
                let entry = undo_entry_for_splice(
                    session.model, sel_start, sel_end,
                    Seq::empty(), Seq::empty(), sel_start);
                let new_stack = push_undo_or_merge(
                    session.undo_stack, entry, false);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard,
                }
            } else {
                session
            }
        },
        KeyAction::External(ExternalAction::Copy) => {
            if has_selection(session.model.anchor, session.model.focus) {
                TextEditSession {
                    clipboard: get_selection_text(session.model),
                    ..session
                }
            } else {
                session
            }
        },
        KeyAction::None => session,
    }
}

} // verus!
