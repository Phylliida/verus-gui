use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::cursor::*;
use crate::text_model::viewport::*;
use crate::text_input::*;
use crate::event::*;
use crate::runtime::text_model::*;
use crate::text_model::session::*;
use crate::runtime::session::*;
use crate::runtime::session_helpers::*;
use crate::runtime::event::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Runtime text input config
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextInputConfig {
    pub line_width: Option<usize>,
    pub max_lines: Option<usize>,
    pub editable: bool,
}

impl View for RuntimeTextInputConfig {
    type V = TextInputConfig;
    open spec fn view(&self) -> TextInputConfig {
        TextInputConfig {
            line_width: match self.line_width {
                Some(w) => Some(w as nat),
                None => None,
            },
            max_lines: match self.max_lines {
                Some(m) => Some(m as nat),
                None => None,
            },
            editable: self.editable,
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Runtime text input widget
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextInput {
    pub session: RuntimeTextEditSession,
    pub config: RuntimeTextInputConfig,
    pub viewport: RuntimeTextViewport,
    pub cursor_visible: bool,
    pub blink_counter: usize,
}

/// Create a new text input with default viewport.
pub fn new_text_input_exec(
    model: RuntimeTextModel,
    config: RuntimeTextInputConfig,
    visible_lines: usize,
) -> (out: RuntimeTextInput)
    requires model.wf_spec(),
    ensures
        out.session.wf_spec(),
        out.session.view_session() == new_session(model@),
        out.config@ == config@,
        out.viewport@ == (TextViewport { scroll_line: 0, visible_lines: visible_lines as nat }),
        out.cursor_visible == true,
        out.blink_counter == 0,
{
    RuntimeTextInput {
        session: new_session_exec(model),
        config,
        viewport: RuntimeTextViewport {
            scroll_line: 0,
            visible_lines,
        },
        cursor_visible: true,
        blink_counter: 0,
    }
}

/// Handle a key event on the text input.
/// Filters keys per config, delegates to session, scrolls to cursor.
pub fn text_input_handle_key_exec(
    mut input: RuntimeTextInput,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextInput)
    requires
        input.session.wf_spec(),
        input.session.model.text.len() + 2 < usize::MAX,
        input.session.undo_stack.entries.len() < usize::MAX,
        input.session.model@.composition.is_some() ==>
            input.session.model@.text.len()
                + input.session.model@.composition.unwrap().provisional.len()
                < usize::MAX,
        input.viewport.scroll_line as u64 + input.viewport.visible_lines as u64 <= usize::MAX as u64,
    ensures
        result.session.view_session().model
            == text_input_handle_key(
                input.session.view_session(), input.config@, event@).model,
        result.session.view_session().last_was_insert
            == text_input_handle_key(
                input.session.view_session(), input.config@, event@).last_was_insert,
        result.session.view_session().clipboard
            == text_input_handle_key(
                input.session.view_session(), input.config@, event@).clipboard,
        result.session.model.wf_spec(),
{
    // Mirror spec key_allowed_by_config structure exactly.
    let is_enter = match &event.kind {
        RuntimeKeyEventKind::Enter => true,
        _ => false,
    };
    let is_single_line = match input.config.max_lines {
        Some(1) => true,
        _ => false,
    };
    let is_movement = match &event.kind {
        RuntimeKeyEventKind::Left
        | RuntimeKeyEventKind::Right
        | RuntimeKeyEventKind::Up
        | RuntimeKeyEventKind::Down
        | RuntimeKeyEventKind::Home
        | RuntimeKeyEventKind::End
        | RuntimeKeyEventKind::SelectAll
        | RuntimeKeyEventKind::Copy => true,
        _ => false,
    };
    let allowed = if is_enter && is_single_line {
        false
    } else if !input.config.editable && !is_movement {
        false
    } else {
        true
    };

    if !allowed {
        return input;
    }

    // Apply to session
    input.session = apply_key_to_session_exec(input.session, event);

    // Compute cursor line and scroll to it
    let cursor_line = {
        let pos = input.session.model.focus;
        match input.config.line_width {
            Some(w) => {
                let (line, _col) = wrapped_pos_to_visual_exec(
                    &input.session.model.text, pos, w);
                line
            },
            None => {
                let aff = match input.session.model.focus_affinity {
                    Affinity::Upstream => Affinity::Upstream,
                    Affinity::Downstream => Affinity::Downstream,
                };
                let (line, _col) = text_pos_to_visual_exec(
                    &input.session.model.text, pos, aff);
                line
            },
        }
    };
    input.viewport = scroll_to_cursor_exec(input.viewport, cursor_line);

    // Reset blink
    input.cursor_visible = true;
    input.blink_counter = 0;

    input
}

/// Tick the blink timer. Toggle cursor visibility every `blink_rate` ticks.
pub fn text_input_tick_exec(
    mut input: RuntimeTextInput, blink_rate: usize,
) -> (result: RuntimeTextInput)
    requires
        blink_rate > 0,
        input.blink_counter < usize::MAX,
{
    if input.blink_counter + 1 >= blink_rate {
        input.cursor_visible = !input.cursor_visible;
        input.blink_counter = 0;
    } else {
        input.blink_counter = input.blink_counter + 1;
    }
    input
}

/// Handle a click on a text input: compute cursor position from local coords.
pub fn text_input_handle_click_exec(
    mut input: RuntimeTextInput,
    local_x: usize,
    local_y: usize,
    char_width: usize,
    line_height: usize,
    shift: bool,
) -> (result: RuntimeTextInput)
    requires
        input.session.wf_spec(),
        char_width > 0,
        line_height > 0,
        input.viewport.scroll_line as u64 + (local_y / line_height) as u64 <= usize::MAX as u64,
    ensures
        result.session.model.focus <= result.session.model.text@.len(),
        result.session.model.anchor <= result.session.model.text@.len(),
{
    let scroll_line = input.viewport.scroll_line;
    let line = scroll_line + local_y / line_height;
    let col = local_x / char_width;

    let text_pos = match input.config.line_width {
        Some(w) => wrapped_visual_to_pos_exec(
            &input.session.model.text, line, col, w),
        None => {
            let (pos, _aff) = visual_to_text_pos_exec(
                &input.session.model.text, line, col);
            pos
        },
    };

    // Clamp to text length
    let text_len = input.session.model.text.len();
    let clamped = if text_pos > text_len { text_len } else { text_pos };

    if shift {
        input.session.model.focus = clamped;
    } else {
        input.session.model.anchor = clamped;
        input.session.model.focus = clamped;
    }
    input.session.model.focus_affinity = Affinity::Downstream;

    // Reset blink
    input.cursor_visible = true;
    input.blink_counter = 0;

    input
}

} // verus!
