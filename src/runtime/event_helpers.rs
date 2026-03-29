use vstd::prelude::*;
use crate::runtime::text_model::RuntimeTextModel;
use crate::runtime::event::{RuntimeKeyEvent, RuntimeKeyEventKind, RuntimeKeyAction};
use crate::event::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;

verus! {

pub fn key_to_move_direction_exec(event: &RuntimeKeyEvent) -> (result: Option<MoveDirection>)
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

///  Handle Char/Enter/Tab insertion.
pub fn dispatch_insert_char_exec(
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

///  Handle Backspace key.
pub fn dispatch_backspace_exec(
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

///  Handle Delete key.
pub fn dispatch_delete_exec(
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

///  Handle ComposeStart.
pub fn dispatch_compose_start_exec(
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

///  Handle ComposeUpdate.
pub fn dispatch_compose_update_exec(
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

///  Handle ComposeCommit.
pub fn dispatch_compose_commit_exec(
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

///  Handle ComposeCancel.
pub fn dispatch_compose_cancel_exec(
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

///  Handle movement keys (arrow, home, end).
pub fn dispatch_movement_exec(
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

} //  verus!
