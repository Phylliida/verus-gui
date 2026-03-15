use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::cursor::*;
use super::undo::*;
use super::find::*;
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
    pub history: Seq<Seq<char>>,
    pub style_history: Seq<Seq<StyleSet>>,
}

/// Create a new session from a model with empty undo and clipboard.
pub open spec fn new_session(model: TextModel) -> TextEditSession {
    TextEditSession {
        model,
        undo_stack: empty_undo_stack(),
        last_was_insert: false,
        clipboard: Seq::empty(),
        history: seq![model.text],
        style_history: seq![model.styles],
    }
}

/// Well-formedness of a session.
pub open spec fn session_wf(s: TextEditSession) -> bool {
    &&& s.model.wf()
    &&& undo_stack_wf(s.undo_stack)
    &&& undo_history_valid(s.undo_stack, s.history)
    &&& s.history[s.undo_stack.position as int] =~= s.model.text
    &&& undo_style_history_valid(s.undo_stack, s.style_history)
    &&& s.style_history[s.undo_stack.position as int] =~= s.model.styles
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

/// Update history after a push_undo_or_merge operation.
pub open spec fn update_history_for_push(
    stack: UndoStack, history: Seq<Seq<char>>,
    entry: UndoEntry, new_text: Seq<char>, merge: bool,
) -> Seq<Seq<char>> {
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        // Merge: drop history[position], append new_text after history[0..position]
        history.subrange(0, stack.position as int).push(new_text)
    } else {
        // Push: truncate to position+1 entries, append new_text
        history.subrange(0, stack.position as int + 1).push(new_text)
    }
}

/// Update style history after a push_undo_or_merge operation.
pub open spec fn update_style_history_for_push(
    stack: UndoStack, style_history: Seq<Seq<StyleSet>>,
    entry: UndoEntry, new_styles: Seq<StyleSet>, merge: bool,
) -> Seq<Seq<StyleSet>> {
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        style_history.subrange(0, stack.position as int).push(new_styles)
    } else {
        style_history.subrange(0, stack.position as int + 1).push(new_styles)
    }
}

/// Whether a key event kind is a text-modifying operation that needs an undo entry.
pub open spec fn is_text_edit_key(kind: KeyEventKind, model: TextModel) -> bool {
    match kind {
        KeyEventKind::Char(_) | KeyEventKind::Enter | KeyEventKind::Tab => true,
        KeyEventKind::Backspace | KeyEventKind::Delete => true,
        KeyEventKind::ComposeCommit => true,
        _ => false,
    }
}

/// Compute the actual splice parameters for an undo entry, per operation kind.
pub open spec fn undo_splice_params(
    kind: KeyEventKind, model: TextModel,
) -> (nat, nat, Seq<char>, Seq<StyleSet>) {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    match kind {
        KeyEventKind::Char(ch) => (sel_start, sel_end, seq![ch],
            seq![model.typing_style]),
        KeyEventKind::Enter => (sel_start, sel_end, seq!['\n'],
            seq![model.typing_style]),
        KeyEventKind::Tab => (sel_start, sel_end, seq!['\t'],
            seq![model.typing_style]),
        KeyEventKind::Backspace => {
            if has_selection(model.anchor, model.focus) {
                (sel_start, sel_end, Seq::empty(), Seq::empty())
            } else if model.focus == 0 {
                // No-op (dispatch returns None), unreachable in NewModel
                (0, 0, Seq::empty(), Seq::empty())
            } else {
                // dispatch_key checks ctrl modifier, but we only have KeyEventKind here.
                // The ctrl case is handled by Backspace kind at dispatch level.
                // Actually, dispatch_key checks event.modifiers.ctrl which we don't have here.
                // We need to pass modifiers. Let's use the full event instead.
                // For now, use the non-ctrl case (prev_grapheme).
                // The ctrl case will be a separate match in the full function.
                let prev = prev_grapheme_boundary(model.text, model.focus);
                (prev, model.focus, Seq::empty(), Seq::empty())
            }
        },
        KeyEventKind::Delete => {
            if has_selection(model.anchor, model.focus) {
                (sel_start, sel_end, Seq::empty(), Seq::empty())
            } else if model.focus >= model.text.len() {
                (0, 0, Seq::empty(), Seq::empty())
            } else {
                let next = next_grapheme_boundary(model.text, model.focus);
                (model.focus, next, Seq::empty(), Seq::empty())
            }
        },
        KeyEventKind::ComposeCommit => {
            match model.composition {
                Some(c) => (c.range_start, c.range_end, c.provisional,
                    seq_repeat(model.typing_style, c.provisional.len())),
                None => (0, 0, Seq::empty(), Seq::empty()),
            }
        },
        _ => (0, 0, Seq::empty(), Seq::empty()),
    }
}

/// Compute undo splice params, taking modifiers into account for word deletion.
#[verifier::opaque]
pub open spec fn undo_splice_params_full(
    event: KeyEvent, model: TextModel,
) -> (nat, nat, Seq<char>, Seq<StyleSet>) {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    match event.kind {
        KeyEventKind::Backspace => {
            if has_selection(model.anchor, model.focus) {
                (sel_start, sel_end, Seq::empty(), Seq::empty())
            } else if model.focus == 0 {
                (0, 0, Seq::empty(), Seq::empty())
            } else if event.modifiers.ctrl {
                let prev = prev_boundary_in(
                    word_start_boundaries(model.text), model.focus);
                (prev, model.focus, Seq::empty(), Seq::empty())
            } else {
                let prev = prev_grapheme_boundary(model.text, model.focus);
                (prev, model.focus, Seq::empty(), Seq::empty())
            }
        },
        KeyEventKind::Delete => {
            if has_selection(model.anchor, model.focus) {
                (sel_start, sel_end, Seq::empty(), Seq::empty())
            } else if model.focus >= model.text.len() {
                (0, 0, Seq::empty(), Seq::empty())
            } else if event.modifiers.ctrl {
                let next = next_boundary_in(
                    word_end_boundaries(model.text), model.focus);
                (model.focus, next, Seq::empty(), Seq::empty())
            } else {
                let next = next_grapheme_boundary(model.text, model.focus);
                (model.focus, next, Seq::empty(), Seq::empty())
            }
        },
        _ => undo_splice_params(event.kind, model),
    }
}

/// Apply a key event to the entire session: dispatches via dispatch_key,
/// then handles undo/redo/clipboard at the session level.
pub open spec fn apply_key_to_session(
    session: TextEditSession,
    event: KeyEvent,
) -> TextEditSession {
    match dispatch_key(session.model, event) {
        KeyAction::NewModel(new_model) => {
            if is_text_edit_key(event.kind, session.model) {
                let merge = session.last_was_insert && is_insert_key(event.kind);
                let (entry_start, entry_end, entry_new_text, entry_new_styles) =
                    undo_splice_params_full(event, session.model);
                let entry = undo_entry_for_splice(
                    session.model, entry_start, entry_end,
                    entry_new_text, entry_new_styles, new_model.focus);
                let new_stack = push_undo_or_merge(session.undo_stack, entry, merge);
                let new_history = update_history_for_push(
                    session.undo_stack, session.history, entry, new_model.text, merge);
                let new_style_history = update_style_history_for_push(
                    session.undo_stack, session.style_history, entry, new_model.styles, merge);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: is_insert_key(event.kind),
                    clipboard: session.clipboard,
                    history: new_history,
                    style_history: new_style_history,
                }
            } else {
                // Non-text-modifying operation: no undo entry
                TextEditSession {
                    model: new_model,
                    last_was_insert: false,
                    undo_stack: session.undo_stack,
                    clipboard: session.clipboard,
                    history: session.history,
                    style_history: session.style_history,
                }
            }
        },
        KeyAction::External(ExternalAction::Undo) => {
            if can_undo(session.undo_stack) && session.model.composition.is_none() {
                let (new_stack, new_model) = apply_undo(session.undo_stack, session.model);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                    history: session.history,
                    style_history: session.style_history,
                }
            } else {
                session
            }
        },
        KeyAction::External(ExternalAction::Redo) => {
            if can_redo(session.undo_stack) && session.model.composition.is_none() {
                let (new_stack, new_model) = apply_redo(session.undo_stack, session.model);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                    history: session.history,
                    style_history: session.style_history,
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
                let new_history = update_history_for_push(
                    session.undo_stack, session.history, entry, new_model.text, false);
                let new_style_history = update_style_history_for_push(
                    session.undo_stack, session.style_history, entry, new_model.styles, false);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard,
                    history: new_history,
                    style_history: new_style_history,
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
        KeyAction::External(ExternalAction::Paste) => {
            let clean = canonicalize_newlines(filter_permitted(session.clipboard));
            let (sel_start, sel_end) = selection_range(
                session.model.anchor, session.model.focus);
            if (clean.len() > 0 || has_selection(session.model.anchor, session.model.focus))
                && session.model.text.len() + clean.len() < usize::MAX
            {
                let clean_styles = seq_repeat(session.model.typing_style, clean.len());
                let new_model = paste(session.model, session.clipboard, Seq::empty());
                let entry = undo_entry_for_splice(
                    session.model, sel_start, sel_end,
                    clean, clean_styles, sel_start + clean.len());
                let new_stack = push_undo_or_merge(session.undo_stack, entry, false);
                let new_history = update_history_for_push(
                    session.undo_stack, session.history, entry, new_model.text, false);
                let new_style_history = update_style_history_for_push(
                    session.undo_stack, session.style_history, entry, new_model.styles, false);
                TextEditSession {
                    model: new_model,
                    undo_stack: new_stack,
                    last_was_insert: false,
                    clipboard: session.clipboard,
                    history: new_history,
                    style_history: new_style_history,
                }
            } else {
                session
            }
        },
        // Find/replace external actions are handled by separate session functions,
        // not through apply_key_to_session.
        KeyAction::External(ExternalAction::FindNext(_)) => session,
        KeyAction::External(ExternalAction::FindPrev(_)) => session,
        KeyAction::External(ExternalAction::ReplaceAt(_, _, _)) => session,
        KeyAction::External(ExternalAction::ReplaceAll(_, _)) => session,
        KeyAction::None => session,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Find/replace session handlers
// ──────────────────────────────────────────────────────────────────────

/// Find next occurrence of pattern and select it. No undo entry.
pub open spec fn session_find_next(
    session: TextEditSession, pattern: Seq<char>,
) -> TextEditSession {
    match find_next(session.model.text, pattern, session.model.focus) {
        Some(pos) => {
            let new_model = TextModel {
                anchor: pos,
                focus: pos + pattern.len(),
                ..session.model
            };
            TextEditSession { model: new_model, ..session }
        },
        None => session,
    }
}

/// Find previous occurrence of pattern and select it. No undo entry.
pub open spec fn session_find_prev(
    session: TextEditSession, pattern: Seq<char>,
) -> TextEditSession {
    match find_prev(session.model.text, pattern, session.model.anchor) {
        Some(pos) => {
            let new_model = TextModel {
                anchor: pos,
                focus: pos + pattern.len(),
                ..session.model
            };
            TextEditSession { model: new_model, ..session }
        },
        None => session,
    }
}

/// Replace text at `[start..start+pat_len)` with `repl`. Creates undo entry.
pub open spec fn session_replace_at(
    session: TextEditSession, start: nat, pat_len: nat, repl: Seq<char>,
) -> TextEditSession {
    let end = start + pat_len;
    let new_styles = Seq::new(repl.len(), |i: int| session.model.default_style);
    let new_focus = start + repl.len();
    let new_model = splice(session.model, start, end, repl, new_styles, new_focus);
    let entry = undo_entry_for_splice(session.model, start, end, repl, new_styles, new_focus);
    let new_stack = push_undo_or_merge(session.undo_stack, entry, false);
    let new_history = update_history_for_push(
        session.undo_stack, session.history, entry, new_model.text, false);
    let new_style_history = update_style_history_for_push(
        session.undo_stack, session.style_history, entry, new_model.styles, false);
    TextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: new_history,
        style_history: new_style_history,
    }
}

/// Replace all occurrences of `pattern` with `repl`. Uses fuel for termination.
/// Creates a single undo entry covering the entire text replacement.
pub open spec fn session_replace_all(
    session: TextEditSession, pattern: Seq<char>, repl: Seq<char>,
    fuel: nat,
) -> TextEditSession {
    let new_model = replace_all(session.model, pattern, repl, 0, fuel);
    if new_model.text =~= session.model.text {
        session
    } else {
        // Full-text replacement: undo entry from 0..old_len to new text
        let entry = undo_entry_for_splice(
            session.model, 0, session.model.text.len(),
            new_model.text, new_model.styles, new_model.focus);
        let new_stack = push_undo_or_merge(session.undo_stack, entry, false);
        let new_history = update_history_for_push(
            session.undo_stack, session.history, entry, new_model.text, false);
        let new_style_history = update_style_history_for_push(
            session.undo_stack, session.style_history, entry, new_model.styles, false);
        TextEditSession {
            model: new_model,
            undo_stack: new_stack,
            last_was_insert: false,
            clipboard: session.clipboard,
            history: new_history,
            style_history: new_style_history,
        }
    }
}

} // verus!
