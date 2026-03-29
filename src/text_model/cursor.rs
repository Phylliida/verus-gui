use vstd::prelude::*;
use super::*;
use super::operations::resolve_typing_style;

verus! {

//  ──────────────────────────────────────────────────────────────────────
//  Move direction
//  ──────────────────────────────────────────────────────────────────────

///  Direction of cursor movement.
pub enum MoveDirection {
    Left,
    Right,
    WordLeft,
    WordRight,
    LineStart,
    LineEnd,
    Home,
    End,
    Up,
    Down,
}

//  ──────────────────────────────────────────────────────────────────────
//  Line helpers
//  ──────────────────────────────────────────────────────────────────────

///  The line (paragraph) number containing position `pos`.
///  Equals the count of '\n' characters in `text[0..pos)`.
pub open spec fn line_of(text: Seq<char>, pos: nat) -> nat {
    if pos == 0 || text.len() == 0 {
        0
    } else {
        count_char(text.subrange(0, pos as int), '\n')
    }
}

///  Start of the line containing `pos`: scan back for '\n' or return 0.
pub open spec fn line_start(text: Seq<char>, pos: nat) -> nat
    decreases pos,
{
    if pos == 0 {
        0
    } else if text[pos as int - 1] == '\n' {
        pos
    } else {
        line_start(text, (pos - 1) as nat)
    }
}

///  End of the line containing `pos`: scan forward for '\n' or return text.len().
pub open spec fn line_end(text: Seq<char>, pos: nat) -> nat
    decreases text.len() - pos,
{
    if pos >= text.len() {
        text.len()
    } else if text[pos as int] == '\n' {
        pos
    } else {
        line_end(text, pos + 1)
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Movement resolution
//  ──────────────────────────────────────────────────────────────────────

///  Compute `(new_focus, new_affinity, new_preferred_column)` for a movement.
///
///  Horizontal movements clear `preferred_column` to `None`.
///  Vertical movements preserve/establish `preferred_column`.
pub open spec fn resolve_movement(
    text: Seq<char>,
    focus: nat,
    affinity: Affinity,
    preferred_column: Option<nat>,
    direction: MoveDirection,
) -> (nat, Affinity, Option<nat>) {
    match direction {
        MoveDirection::Left => {
            let new_pos = prev_grapheme_boundary(text, focus);
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Right => {
            let new_pos = next_grapheme_boundary(text, focus);
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::WordLeft => {
            let new_pos = if text.len() == 0 { 0 } else {
                prev_boundary_in(word_start_boundaries(text), focus)
            };
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::WordRight => {
            let new_pos = if text.len() == 0 { 0 } else {
                next_boundary_in(word_end_boundaries(text), focus)
            };
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineStart => {
            let new_pos = line_start(text, focus);
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineEnd => {
            let new_pos = line_end(text, focus);
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Home => {
            (0, Affinity::Downstream, None)
        },
        MoveDirection::End => {
            (text.len(), Affinity::Upstream, None)
        },
        MoveDirection::Up => {
            let (cur_line, cur_col) = text_pos_to_visual(text, focus, affinity);
            let col = match preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            if cur_line == 0 {
                //  Already on first line, go to start
                (0, Affinity::Downstream, Some(col))
            } else {
                let (new_pos, new_aff) = visual_to_text_pos(text, (cur_line - 1) as nat, col);
                (new_pos, new_aff, Some(col))
            }
        },
        MoveDirection::Down => {
            let (cur_line, cur_col) = text_pos_to_visual(text, focus, affinity);
            let col = match preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            let (new_pos, new_aff) = visual_to_text_pos(text, cur_line + 1, col);
            //  If visual_to_text_pos returns beyond text.len(), clamp
            if new_pos > text.len() {
                (text.len(), Affinity::Upstream, Some(col))
            } else {
                (new_pos, new_aff, Some(col))
            }
        },
    }
}

///  Whether a direction is horizontal (clears preferred_column).
pub open spec fn is_horizontal(dir: MoveDirection) -> bool {
    match dir {
        MoveDirection::Left
        | MoveDirection::Right
        | MoveDirection::WordLeft
        | MoveDirection::WordRight
        | MoveDirection::LineStart
        | MoveDirection::LineEnd
        | MoveDirection::Home
        | MoveDirection::End => true,
        _ => false,
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Public cursor/selection operations
//  ──────────────────────────────────────────────────────────────────────

///  Move cursor (collapsing selection) in the given direction.
pub open spec fn move_cursor(model: TextModel, dir: MoveDirection) -> TextModel {
    let (new_focus, new_aff, new_pref) = resolve_movement(
        model.text, model.focus, model.focus_affinity, model.preferred_column, dir);
    let new_styles = model.styles;
    let new_typing = resolve_typing_style(model.text, model.styles, new_focus, model.default_style);
    TextModel {
        anchor: new_focus,
        focus: new_focus,
        focus_affinity: new_aff,
        preferred_column: new_pref,
        typing_style: new_typing,
        ..model
    }
}

///  Extend selection: move focus, keep anchor fixed.
pub open spec fn extend_selection(model: TextModel, dir: MoveDirection) -> TextModel {
    let (new_focus, new_aff, new_pref) = resolve_movement(
        model.text, model.focus, model.focus_affinity, model.preferred_column, dir);
    TextModel {
        focus: new_focus,
        focus_affinity: new_aff,
        preferred_column: if is_horizontal(dir) { None } else { new_pref },
        ..model
    }
}

///  Select all text: anchor = 0, focus = text.len().
pub open spec fn select_all(model: TextModel) -> TextModel {
    TextModel {
        anchor: 0,
        focus: model.text.len(),
        focus_affinity: Affinity::Upstream,
        preferred_column: None,
        ..model
    }
}

///  Collapse selection to the leftmost position.
pub open spec fn collapse_left(model: TextModel) -> TextModel {
    let pos = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let new_typing = resolve_typing_style(model.text, model.styles, pos, model.default_style);
    TextModel {
        anchor: pos,
        focus: pos,
        focus_affinity: Affinity::Downstream,
        preferred_column: None,
        typing_style: new_typing,
        ..model
    }
}

///  Collapse selection to the rightmost position.
pub open spec fn collapse_right(model: TextModel) -> TextModel {
    let pos = if model.anchor >= model.focus { model.anchor } else { model.focus };
    let new_typing = resolve_typing_style(model.text, model.styles, pos, model.default_style);
    TextModel {
        anchor: pos,
        focus: pos,
        focus_affinity: Affinity::Upstream,
        preferred_column: None,
        typing_style: new_typing,
        ..model
    }
}

} //  verus!
