use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::proofs::*;
use crate::text_model::undo::*;
use crate::text_model::undo_proofs::*;
use crate::text_model::session::*;
use crate::text_model::paragraph_proofs::*;
use crate::text_model::find::*;
use crate::text_model::find_proofs::*;
use crate::event::*;
use crate::runtime::text_model::*;
use crate::runtime::event::*;
use crate::runtime::session::RuntimeTextEditSession;

verus! {

/// Create a Vec of `count` copies of a style set.
pub fn repeat_style_set_exec(style: &RuntimeStyleSet, count: usize) -> (out: Vec<RuntimeStyleSet>)
    ensures
        out@.len() == count,
        forall|k: int| 0 <= k < count as int ==>
            (#[trigger] out@[k])@ == style@,
        style_seq_view(out@) =~= seq_repeat(style@, count as nat),
{
    let mut result: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            result@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] result@[k])@ == style@,
        decreases count - i,
    {
        result.push(copy_style_set(style));
        i += 1;
    }
    proof {
        lemma_seq_repeat_len(style@, count as nat);
        assert forall|k: int| 0 <= k < result@.len()
            implies (#[trigger] style_seq_view(result@))[k] == seq_repeat(style@, count as nat)[k]
        by {
            lemma_seq_repeat_index(style@, count as nat, k);
        }
    }
    result
}

pub fn new_session_exec(model: RuntimeTextModel) -> (out: RuntimeTextEditSession)
    requires model.wf_spec(),
    ensures
        out.view_session() == new_session(model@),
        out.wf_spec(),
{
    let ghost init_text = model@.text;
    let ghost init_styles = model@.styles;
    RuntimeTextEditSession {
        model,
        undo_stack: empty_undo_stack_exec(),
        last_was_insert: false,
        clipboard: Vec::new(),
        history: Ghost(Seq::empty().push(init_text)),
        style_history: Ghost(Seq::empty().push(init_styles)),
    }
}

// ── Undo/Redo helpers ───────────────────────────────────────────────

/// Apply undo at the session level. Now verified via ghost history.
pub fn session_apply_undo_exec(
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
        lemma_apply_key_undo(session.view_session());
        lemma_undo_preconditions_from_history(
            session.undo_stack@, session.history@, session.model@.text);
    }
    let (new_stack, new_model) = apply_undo_exec(
        session.undo_stack, session.model);
    proof {
        lemma_undo_maintains_history(session.undo_stack@, session.history@);
        lemma_undo_history_position(
            session.undo_stack@, session.history@, session.view_session().model);
        lemma_undo_maintains_style_history(session.undo_stack@, session.style_history@);
        lemma_undo_style_history_position(
            session.undo_stack@, session.style_history@, session.view_session().model);
    }
    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: session.history,
        style_history: session.style_history,
    }
}

/// Apply redo at the session level. Now verified via ghost history.
pub fn session_apply_redo_exec(
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
        lemma_apply_key_redo(session.view_session());
        lemma_redo_preconditions_from_history(
            session.undo_stack@, session.history@, session.model@.text);
    }
    let (new_stack, new_model) = apply_redo_exec(
        session.undo_stack, session.model);
    proof {
        lemma_redo_maintains_history(session.undo_stack@, session.history@);
        lemma_redo_history_position(
            session.undo_stack@, session.history@, session.view_session().model);
        lemma_redo_maintains_style_history(session.undo_stack@, session.style_history@);
        lemma_redo_style_history_position(
            session.undo_stack@, session.style_history@, session.view_session().model);
    }
    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: session.history,
        style_history: session.style_history,
    }
}

/// Helper for unreachable branches — requires false so can never be called
/// in valid execution. Used to satisfy Rust's type checker.
/// Not external_body: the body constructs a dummy value that is never executed.
pub fn dead_session(undo_stack: RuntimeUndoStack, clipboard: Vec<char>, history: Ghost<Seq<Seq<char>>>, style_history: Ghost<Seq<Seq<StyleSet>>>) -> (out: RuntimeTextEditSession)
    requires false,
{
    // requires false → body never executes → any construction is fine
    let dummy_style = RuntimeStyleSet {
        bold: None, italic: None, underline: None, strikethrough: None,
        font_size: None, font_family: None, color: None, bg_color: None,
    };
    let dummy_style2 = RuntimeStyleSet {
        bold: None, italic: None, underline: None, strikethrough: None,
        font_size: None, font_family: None, color: None, bg_color: None,
    };
    let model = RuntimeTextModel {
        text: Vec::new(), styles: Vec::new(),
        anchor: 0, focus: 0, focus_affinity: Affinity::Downstream,
        preferred_column: None,
        typing_style: dummy_style,
        default_style: dummy_style2,
        composition: None, paragraph_styles: Vec::new(),
        model: Ghost(TextModel {
            text: Seq::empty(), styles: Seq::empty(),
            anchor: 0, focus: 0, focus_affinity: Affinity::Downstream,
            preferred_column: None,
            typing_style: StyleSet {
                bold: None, italic: None, underline: None, strikethrough: None,
                font_size: None, font_family: None, color: None, bg_color: None,
            },
            default_style: StyleSet {
                bold: None, italic: None, underline: None, strikethrough: None,
                font_size: None, font_family: None, color: None, bg_color: None,
            },
            composition: None, paragraph_styles: Seq::empty(),
        }),
    };
    RuntimeTextEditSession {
        model, undo_stack, last_was_insert: false,
        clipboard, history, style_history,
    }
}

// ── Cut helper ──────────────────────────────────────────────────────

/// Handle Cut at the session level with full wf_spec preservation.
pub fn session_handle_cut_exec(
    session: RuntimeTextEditSession,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        has_selection(session.model@.anchor, session.model@.focus),
        session.undo_stack.entries.len() < usize::MAX,
        session.model.text.len() + 2 < usize::MAX,
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Cut, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Cut, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Cut, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    let clipboard = get_selection_text_exec(&session.model);
    let sel_start = if session.model.anchor <= session.model.focus {
        session.model.anchor } else { session.model.focus };
    let sel_end = if session.model.anchor <= session.model.focus {
        session.model.focus } else { session.model.anchor };
    proof {
        lemma_apply_key_cut(session.view_session());
        lemma_empty_seq_wf();
        axiom_splice_wf(session.model@.text, sel_start as nat, sel_end as nat, Seq::<char>::empty());
    }
    let entry = undo_entry_for_splice_exec(
        &session.model, sel_start, sel_end,
        &Vec::new(), &Vec::new(), sel_start);
    let ghost old_model = session.model@;
    let ghost old_stack = session.undo_stack@;
    let ghost old_history = session.history@;
    let ghost old_style_history = session.style_history@;
    let new_model = delete_selection_exec(session.model);
    let new_stack = push_undo_or_merge_exec(
        session.undo_stack, entry, false);
    let ghost new_history = update_history_for_push(
        old_stack, old_history, entry@, new_model@.text, false);
    let ghost new_style_history = update_style_history_for_push(
        old_stack, old_style_history, entry@, new_model@.styles, false);
    proof {
        // Prove entry_describes_transition for the cut
        lemma_entry_for_splice_describes_transition(
            old_model, sel_start as nat, sel_end as nat,
            Seq::<char>::empty(), Seq::<StyleSet>::empty(), sel_start as nat);
        // Prove push_or_merge maintains history validity
        lemma_push_or_merge_history_valid(
            old_stack, old_history, entry@, new_model@.text, false);
        // Style history
        lemma_entry_for_splice_describes_style_transition(
            old_model, sel_start as nat, sel_end as nat,
            Seq::<char>::empty(), Seq::<StyleSet>::empty(), sel_start as nat);
        lemma_push_or_merge_style_history_valid(
            old_stack, old_style_history, entry@, new_model@.styles, false);
    }
    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard,
        history: Ghost(new_history),
        style_history: Ghost(new_style_history),
    }
}

// ── Paste helper ────────────────────────────────────────────────────

/// Handle Paste at the session level with full wf_spec preservation.
pub fn session_handle_paste_exec(
    session: RuntimeTextEditSession,
    clean: Vec<char>,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.undo_stack.entries.len() < usize::MAX,
        session.model.text.len() + 2 < usize::MAX,
        clean@ =~= canonicalize_newlines(filter_permitted(session.clipboard@)),
        clean.len() > 0 || has_selection(session.model@.anchor, session.model@.focus),
        session.model.text.len() + clean.len() < usize::MAX,
    ensures
        result.view_session().model
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Paste, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).model,
        result.view_session().last_was_insert
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Paste, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).last_was_insert,
        result.view_session().clipboard
            == apply_key_to_session(session.view_session(),
                KeyEvent { kind: KeyEventKind::Paste, modifiers: Modifiers { shift: false, ctrl: false, alt: false } }).clipboard,
        result.model.wf_spec(),
        result.wf_spec(),
{
    let sel_start = if session.model.anchor <= session.model.focus {
        session.model.anchor } else { session.model.focus };
    let sel_end = if session.model.anchor <= session.model.focus {
        session.model.focus } else { session.model.anchor };

    let clean_styles = repeat_style_set_exec(
        &session.model.typing_style, clean.len());
    let new_focus = sel_start + clean.len();

    let entry = undo_entry_for_splice_exec(
        &session.model, sel_start, sel_end,
        &clean, &clean_styles, new_focus);

    let ghost old_model = session.model@;
    let ghost old_stack = session.undo_stack@;
    let ghost old_history = session.history@;
    let ghost old_style_history = session.style_history@;

    proof {
        lemma_apply_key_paste(session.view_session());
        axiom_paste_wf(
            session.model@.text,
            sel_start as nat, sel_end as nat, session.clipboard@);
    }

    let new_model = paste_exec(session.model, &session.clipboard);
    let new_stack = push_undo_or_merge_exec(
        session.undo_stack, entry, false);
    let ghost new_history = update_history_for_push(
        old_stack, old_history, entry@, new_model@.text, false);
    let ghost new_style_history = update_style_history_for_push(
        old_stack, old_style_history, entry@, new_model@.styles, false);

    proof {
        lemma_entry_for_splice_describes_transition(
            old_model, sel_start as nat, sel_end as nat,
            clean@, style_seq_view(clean_styles@), new_focus as nat);
        lemma_push_or_merge_history_valid(
            old_stack, old_history, entry@, new_model@.text, false);
        lemma_entry_for_splice_describes_style_transition(
            old_model, sel_start as nat, sel_end as nat,
            clean@, style_seq_view(clean_styles@), new_focus as nat);
        lemma_push_or_merge_style_history_valid(
            old_stack, old_style_history, entry@, new_model@.styles, false);
    }

    RuntimeTextEditSession {
        model: new_model,
        undo_stack: new_stack,
        last_was_insert: false,
        clipboard: session.clipboard,
        history: Ghost(new_history),
        style_history: Ghost(new_style_history),
    }
}

// ── Undo splice params extraction ─────────────────────────────────

/// Extract undo splice parameters for a text-edit key event.
/// Mirrors the spec `undo_splice_params_full`. Separated from
/// `session_handle_text_edit_exec` to reduce Z3 path explosion.
pub fn undo_splice_params_full_exec(
    model: &RuntimeTextModel,
    event: &RuntimeKeyEvent,
) -> (result: (usize, usize, Vec<char>, Vec<RuntimeStyleSet>))
    requires
        model.wf_spec(),
        is_text_edit_key(event@.kind, model@),
        match dispatch_key(model@, event@) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
        model@.composition.is_some() ==>
            model@.text.len()
                + model@.composition.unwrap().provisional.len()
                < usize::MAX,
    ensures
        result.0 as nat == undo_splice_params_full(event@, model@).0,
        result.1 as nat == undo_splice_params_full(event@, model@).1,
        result.2@ =~= undo_splice_params_full(event@, model@).2,
        style_seq_view(result.3@) =~= undo_splice_params_full(event@, model@).3,
        result.0 <= result.1,
        result.1 <= model.text.len(),
        result.2.len() == result.3.len(),
{
    proof { reveal(undo_splice_params_full); }
    let sel_start = if model.anchor <= model.focus {
        model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus {
        model.focus } else { model.anchor };

    match &event.kind {
        RuntimeKeyEventKind::Char(ch) => {
            (sel_start, sel_end,
             vec![*ch], vec![copy_style_set(&model.typing_style)])
        },
        RuntimeKeyEventKind::Enter => {
            (sel_start, sel_end,
             vec!['\n'], vec![copy_style_set(&model.typing_style)])
        },
        RuntimeKeyEventKind::Tab => {
            (sel_start, sel_end,
             vec!['\t'], vec![copy_style_set(&model.typing_style)])
        },
        RuntimeKeyEventKind::Backspace => {
            if model.anchor != model.focus {
                (sel_start, sel_end, Vec::new(), Vec::new())
            } else if event.modifiers.ctrl {
                proof {
                    axiom_prev_word_boundary_valid(
                        model@.text, model@.focus);
                }
                let prev = prev_word_start_exec(
                    &model.text, model.focus);
                (prev, model.focus, Vec::new(), Vec::new())
            } else {
                proof {
                    axiom_prev_grapheme_boundary_valid(
                        model@.text, model@.focus);
                }
                let prev = prev_grapheme_boundary_exec(
                    &model.text, model.focus);
                (prev, model.focus, Vec::new(), Vec::new())
            }
        },
        RuntimeKeyEventKind::Delete => {
            if model.anchor != model.focus {
                (sel_start, sel_end, Vec::new(), Vec::new())
            } else if event.modifiers.ctrl {
                proof {
                    axiom_next_word_boundary_valid(
                        model@.text, model@.focus);
                }
                let next = next_word_end_exec(
                    &model.text, model.focus);
                (model.focus, next, Vec::new(), Vec::new())
            } else {
                proof {
                    axiom_next_grapheme_boundary_valid(
                        model@.text, model@.focus);
                }
                let next = next_grapheme_boundary_exec(
                    &model.text, model.focus);
                (model.focus, next, Vec::new(), Vec::new())
            }
        },
        RuntimeKeyEventKind::ComposeCommit => {
            let c = model.composition.as_ref().unwrap();
            let prov_text: Vec<char> = copy_char_vec(&c.provisional);
            let prov_styles: Vec<RuntimeStyleSet> =
                repeat_style_set_exec(&model.typing_style, c.provisional.len());
            (c.range_start, c.range_end, prov_text, prov_styles)
        },
        _ => {
            proof { assert(false); }
            (0, 0, Vec::new(), Vec::new())
        },
    }
}

// ── Per-arm helpers for apply_key_to_session_exec ───────────────────
// Each handles one event kind (active + noop path), keeping the
// parent dispatch trivially small.

/// Handle Copy event: copy selection to clipboard, or noop.
pub fn session_copy_arm_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        match dispatch_key(session.model@, event@) {
            KeyAction::External(ExternalAction::Copy) => true,
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
    if session.model.anchor != session.model.focus {
        proof { lemma_apply_key_copy(session.view_session(), event@); }
        let clipboard = get_selection_text_exec(&session.model);
        RuntimeTextEditSession {
            clipboard,
            last_was_insert: session.last_was_insert,
            model: session.model,
            undo_stack: session.undo_stack,
            history: session.history,
            style_history: session.style_history,
        }
    } else {
        proof { lemma_apply_key_noop(session.view_session(), event@); }
        session
    }
}

/// Handle Cut event: cut selection, or noop if no selection.
pub fn session_cut_arm_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.undo_stack.entries.len() < usize::MAX,
        match dispatch_key(session.model@, event@) {
            KeyAction::External(ExternalAction::Cut) => true,
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
    if session.model.anchor != session.model.focus {
        proof { lemma_apply_key_kind_determines_result(session.view_session(), event@, KeyEventKind::Cut); }
        session_handle_cut_exec(session)
    } else {
        proof { lemma_apply_key_noop(session.view_session(), event@); }
        session
    }
}

/// Handle Undo event: apply undo if possible, or noop.
pub fn session_undo_arm_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        match dispatch_key(session.model@, event@) {
            KeyAction::External(ExternalAction::Undo) => true,
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
    if can_undo_exec(&session.undo_stack) {
        if session.model.composition.is_none() {
            proof { lemma_apply_key_kind_determines_result(session.view_session(), event@, KeyEventKind::Undo); }
            return session_apply_undo_exec(session);
        }
    }
    proof { lemma_apply_key_noop(session.view_session(), event@); }
    session
}

/// Handle Redo event: apply redo if possible, or noop.
pub fn session_redo_arm_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        match dispatch_key(session.model@, event@) {
            KeyAction::External(ExternalAction::Redo) => true,
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
    if can_redo_exec(&session.undo_stack) {
        if session.model.composition.is_none() {
            proof { lemma_apply_key_kind_determines_result(session.view_session(), event@, KeyEventKind::Redo); }
            return session_apply_redo_exec(session);
        }
    }
    proof { lemma_apply_key_noop(session.view_session(), event@); }
    session
}

/// Handle Paste event: paste clipboard, or noop if empty/overflow.
pub fn session_paste_arm_exec(
    session: RuntimeTextEditSession,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        session.model.text.len() + 2 < usize::MAX,
        session.undo_stack.entries.len() < usize::MAX,
        match dispatch_key(session.model@, event@) {
            KeyAction::External(ExternalAction::Paste) => true,
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
    let filtered = filter_permitted_exec(&session.clipboard);
    let clean = canonicalize_newlines_exec(&filtered);
    if (clean.len() > 0 || session.model.anchor != session.model.focus)
        && clean.len() < usize::MAX - session.model.text.len()
    {
        proof { lemma_apply_key_kind_determines_result(session.view_session(), event@, KeyEventKind::Paste); }
        session_handle_paste_exec(session, clean)
    } else {
        proof { lemma_apply_key_noop(session.view_session(), event@); }
        session
    }
}

// ──────────────────────────────────────────────────────────────────────
// Find exec
// ──────────────────────────────────────────────────────────────────────

/// Runtime find next: scan text forward for pattern.
pub fn find_next_exec(
    text: &Vec<char>, pattern: &Vec<char>, from: usize,
) -> (out: Option<usize>)
    requires
        pattern@.len() < usize::MAX,
    ensures
        match out {
            Some(pos) => find_next(text@, pattern@, from as nat) == Some(pos as nat),
            None => find_next(text@, pattern@, from as nat).is_none(),
        },
{
    if pattern.len() == 0 {
        return None;
    }
    let pat_len = pattern.len();
    let text_len = text.len();

    // If from > text_len or text too short for pattern, no match
    if from > text_len || text_len < pat_len {
        // find_next_scan with from + pat_len > text_len → None
        proof { lemma_find_next_scan_none_out_of_range(text@, pattern@, from as nat); }
        return None;
    }

    // Compute the last valid start position (text_len - pat_len)
    let last_start = text_len - pat_len;
    let mut i = from;

    while i <= last_start
        invariant
            from <= i,
            pat_len == pattern@.len(),
            pat_len > 0,
            last_start == text_len - pat_len,
            text_len == text@.len(),
            i <= text_len,
            // Key invariant: no match exists in [from, i)
            forall|p: nat| from as nat <= p && p < i as nat ==>
                !seq_matches_at(text@, pattern@, p),
        decreases last_start - i + 1,
    {
        // Check if pattern matches at i
        let mut j: usize = 0;
        let mut matches = true;
        while j < pat_len && matches
            invariant
                0 <= j <= pat_len,
                i as int + pat_len as int <= text_len as int,
                text_len == text@.len(),
                pat_len == pattern@.len(),
                matches ==> (forall|k: nat| k < j as nat ==>
                    text@[(i + k) as int] == pattern@[k as int]),
                !matches ==> !seq_matches_at(text@, pattern@, i as nat),
            decreases pat_len - j,
        {
            assert((i as int) + (j as int) < (text_len as int));
            if text[i + j] != pattern[j] {
                matches = false;
            }
            j = j + 1;
        }

        if matches {
            // Pattern matches at i. By invariant, no match in [from, i).
            // So i is the first match = find_next_scan result.
            proof {
                // matches ==> seq_matches_at(text@, pattern@, i as nat)
                assert(seq_matches_at(text@, pattern@, i as nat));
                lemma_find_next_scan_matches_first(
                    text@, pattern@, from as nat, i as nat, text@.len());
            }
            return Some(i);
        }

        // !matches at position i — no match here
        // The invariant for next iteration will include this position

        if i == last_start {
            // Checked all positions [from, last_start]. None matched.
            // For p > last_start: p + pat_len > text_len, so no valid match.
            proof {
                // Invariant gives: no match in [from, i). Plus !matches gives: no match at i.
                // So no match in [from, i] = [from, last_start].
                // Any p with p + pat_len <= text_len has p <= last_start.
                // Combined: no match for any valid p >= from.
                assert(forall|p: nat| from as nat <= p && p + pattern@.len() <= text@.len()
                    ==> !seq_matches_at(text@, pattern@, p));
                lemma_find_next_scan_exhausted(
                    text@, pattern@, from as nat, text@.len());
            }
            return None;
        }
        i = i + 1;
    }

    // Loop condition i > last_start without break — same exhaustion
    proof {
        assert(forall|p: nat| from as nat <= p && p + pattern@.len() <= text@.len()
            ==> !seq_matches_at(text@, pattern@, p));
        lemma_find_next_scan_exhausted(
            text@, pattern@, from as nat, text@.len());
    }
    None
}

/// Runtime find prev: scan text backward for pattern.
pub fn find_prev_exec(
    text: &Vec<char>, pattern: &Vec<char>, from: usize,
) -> (out: Option<usize>)
    requires
        pattern@.len() < usize::MAX,
    ensures
        match out {
            Some(pos) => find_prev(text@, pattern@, from as nat) == Some(pos as nat),
            None => find_prev(text@, pattern@, from as nat).is_none(),
        },
{
    if pattern.len() == 0 || from == 0 {
        // find_prev with empty pattern or from==0 returns None
        return None;
    }
    let pat_len = pattern.len();
    let text_len = text.len();
    let mut pos = from;

    while pos > 0
        invariant
            pos <= from,
            pat_len == pattern@.len(),
            pat_len > 0,
            text_len == text@.len(),
            // Key invariant: no match in [pos, from)
            forall|p: nat| pos as nat <= p && p < from as nat ==>
                !seq_matches_at(text@, pattern@, p),
        decreases pos,
    {
        pos = pos - 1;

        if text_len >= pat_len && pos <= text_len - pat_len {
            let mut j: usize = 0;
            let mut matches = true;
            while j < pat_len && matches
                invariant
                    0 <= j <= pat_len,
                    pos as int + pat_len as int <= text_len as int,
                    text_len == text@.len(),
                    pat_len == pattern@.len(),
                    matches ==> (forall|k: nat| k < j as nat ==>
                        text@[(pos + k) as int] == pattern@[k as int]),
                    !matches ==> !seq_matches_at(text@, pattern@, pos as nat),
                decreases pat_len - j,
            {
                assert((pos as int) + (j as int) < (text_len as int));
                if text[pos + j] != pattern[j] {
                    matches = false;
                }
                j = j + 1;
            }

            if matches {
                // Pattern matches at pos. No match in (pos, from). So pos is the last match.
                proof {
                    assert(seq_matches_at(text@, pattern@, pos as nat));
                    lemma_find_prev_scan_matches_last(
                        text@, pattern@, from as nat, pos as nat, from as nat);
                }
                return Some(pos);
            }
        } else {
            // pos + pat_len > text_len, so !seq_matches_at trivially
        }
    }

    // Exhausted: no match in [0, from)
    proof {
        lemma_find_prev_scan_exhausted(
            text@, pattern@, from as nat, from as nat);
    }
    None
}

// ──────────────────────────────────────────────────────────────────────
// Session find/replace exec
// ──────────────────────────────────────────────────────────────────────

/// Find next and select the match.
pub fn session_find_next_exec(
    mut session: RuntimeTextEditSession,
    pattern: &Vec<char>,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        pattern@.len() < usize::MAX,
    ensures
        result.model.wf_spec(),
{
    let from = session.model.focus;
    let found = find_next_exec(&session.model.text, pattern, from);
    match found {
        Some(pos) => {
            let text_len = session.model.text.len();
            let end = if text_len >= pattern.len() && pos <= text_len - pattern.len() {
                pos + pattern.len()
            } else {
                text_len
            };
            proof {
                lemma_find_next_correct(session.model@.text, pattern@, from as nat);
                // seq_matches_at → pos + pattern.len() <= text.len() and pos <= text.len()
                axiom_find_result_grapheme_aligned(session.model@.text, pattern@, pos as nat);
                // pos and pos + pattern.len() are grapheme boundaries
                // end == pos + pattern.len() (since text_len >= pattern.len() && pos <= text_len - pattern.len())
                // or end == text_len (which is always a grapheme boundary by axiom_grapheme_boundaries_valid)
                axiom_grapheme_boundaries_valid(session.model@.text);
            }
            session.model.anchor = pos;
            session.model.focus = end;
            session.model.model = Ghost(TextModel {
                anchor: pos as nat,
                focus: end as nat,
                ..session.model.model@
            });
            session
        },
        None => session,
    }
}

/// Find previous and select the match.
pub fn session_find_prev_exec(
    mut session: RuntimeTextEditSession,
    pattern: &Vec<char>,
) -> (result: RuntimeTextEditSession)
    requires
        session.wf_spec(),
        pattern@.len() < usize::MAX,
    ensures
        result.model.wf_spec(),
{
    let from = session.model.anchor;
    let found = find_prev_exec(&session.model.text, pattern, from);
    match found {
        Some(pos) => {
            let text_len = session.model.text.len();
            let end = if text_len >= pattern.len() && pos <= text_len - pattern.len() {
                pos + pattern.len()
            } else {
                text_len
            };
            proof {
                lemma_find_prev_correct(session.model@.text, pattern@, from as nat);
                axiom_find_result_grapheme_aligned(session.model@.text, pattern@, pos as nat);
                axiom_grapheme_boundaries_valid(session.model@.text);
            }
            session.model.anchor = pos;
            session.model.focus = end;
            session.model.model = Ghost(TextModel {
                anchor: pos as nat,
                focus: end as nat,
                ..session.model.model@
            });
            session
        },
        None => session,
    }
}

} // verus!
