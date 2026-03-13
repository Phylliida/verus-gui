use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::cursor::*;
use crate::text_model::viewport::*;
use crate::text_input::*;
use crate::event::*;
use crate::runtime::text_model::*;
use crate::runtime::session::*;
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
#[verifier::external_body]
pub fn new_text_input_exec(
    model: RuntimeTextModel,
    config: RuntimeTextInputConfig,
    visible_lines: usize,
) -> (out: RuntimeTextInput)
    requires model.wf_spec(),
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
#[verifier::external_body]
pub fn text_input_handle_key_exec(
    mut input: RuntimeTextInput,
    event: &RuntimeKeyEvent,
) -> (result: RuntimeTextInput)
{
    // Check if key is allowed by config
    let allowed = match &event.kind {
        RuntimeKeyEventKind::Enter => {
            // Single-line: block Enter
            match input.config.max_lines {
                Some(1) => false,
                _ => true,
            }
        },
        _ if !input.config.editable => {
            // Read-only: only movement/copy
            match &event.kind {
                RuntimeKeyEventKind::Left
                | RuntimeKeyEventKind::Right
                | RuntimeKeyEventKind::Up
                | RuntimeKeyEventKind::Down
                | RuntimeKeyEventKind::Home
                | RuntimeKeyEventKind::End
                | RuntimeKeyEventKind::SelectAll
                | RuntimeKeyEventKind::Copy => true,
                _ => false,
            }
        },
        _ => true,
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
                let (line, _col) = text_pos_to_visual_exec(
                    &input.session.model.text, pos,
                    input.session.model.focus_affinity);
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

} // verus!
