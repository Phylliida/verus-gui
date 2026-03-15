use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;
use crate::text_model::session::*;
use crate::text_model::word_wrap::*;
use crate::event::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Text input configuration
// ──────────────────────────────────────────────────────────────────────

/// Configuration for a text input widget.
pub struct TextInputConfig {
    /// Soft wrap width: None = no wrap, Some(w) = wrap at w columns.
    pub line_width: Option<nat>,
    /// Maximum number of visible lines: None = unlimited, Some(1) = single-line.
    pub max_lines: Option<nat>,
    /// Whether the text is editable.
    pub editable: bool,
}

/// A single-line text input config.
pub open spec fn single_line_config() -> TextInputConfig {
    TextInputConfig {
        line_width: None,
        max_lines: Some(1nat),
        editable: true,
    }
}

/// A multi-line text area config with optional wrap.
pub open spec fn multi_line_config(wrap_width: Option<nat>) -> TextInputConfig {
    TextInputConfig {
        line_width: wrap_width,
        max_lines: None,
        editable: true,
    }
}

/// A read-only text display config.
pub open spec fn read_only_config() -> TextInputConfig {
    TextInputConfig {
        line_width: None,
        max_lines: None,
        editable: false,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Key filtering
// ──────────────────────────────────────────────────────────────────────

/// Whether a key event is a movement/selection-only key (no editing).
pub open spec fn is_movement_key(kind: KeyEventKind) -> bool {
    match kind {
        KeyEventKind::Left
        | KeyEventKind::Right
        | KeyEventKind::Up
        | KeyEventKind::Down
        | KeyEventKind::Home
        | KeyEventKind::End
        | KeyEventKind::SelectAll => true,
        KeyEventKind::Copy => true,
        _ => false,
    }
}

/// Whether a key event is allowed by the given config.
pub open spec fn key_allowed_by_config(
    config: TextInputConfig, kind: KeyEventKind,
) -> bool {
    // Single-line mode: filter Enter
    if config.max_lines == Some(1nat) && matches!(kind, KeyEventKind::Enter) {
        false
    } else if !config.editable && !is_movement_key(kind) {
        // Read-only: only allow movement/copy keys
        false
    } else {
        true
    }
}

// ──────────────────────────────────────────────────────────────────────
// Preferred size
// ──────────────────────────────────────────────────────────────────────

/// Compute the preferred size (width, height) of a text input in abstract units.
/// Width = max line length (or line_width if wrapping).
/// Height = number of visual lines * line_height, capped by max_lines.
pub open spec fn text_input_preferred_size(
    config: TextInputConfig,
    model: TextModel,
    line_height: nat,
) -> (nat, nat) {
    let num_lines = match config.line_width {
        Some(w) => wrapped_line_count(model.text, w),
        None => paragraph_count(model.text),
    };
    let visible = match config.max_lines {
        Some(m) => if num_lines < m { num_lines } else { m },
        None => num_lines,
    };
    let width = match config.line_width {
        Some(w) => w,
        None => model.text.len(),  // Simplified: full text length as width
    };
    (width, visible * line_height)
}

// ──────────────────────────────────────────────────────────────────────
// Key dispatch with config filtering
// ──────────────────────────────────────────────────────────────────────

/// Handle a key event on the text input session, respecting config.
/// Filters keys based on single-line / read-only settings.
pub open spec fn text_input_handle_key(
    session: TextEditSession,
    config: TextInputConfig,
    event: KeyEvent,
) -> TextEditSession {
    if !key_allowed_by_config(config, event.kind) {
        session
    } else {
        apply_key_to_session(session, event)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Click-to-cursor
// ──────────────────────────────────────────────────────────────────────

/// Convert local (x, y) coordinates within a text input to a (line, col) position.
/// char_width and line_height are the metrics for the monospace grid.
/// scroll_line is the current scroll offset in lines.
pub open spec fn text_input_click_pos(
    local_x: nat,
    local_y: nat,
    char_width: nat,
    line_height: nat,
    scroll_line: nat,
) -> (nat, nat) {
    if char_width == 0 || line_height == 0 {
        (scroll_line, 0)
    } else {
        let line = scroll_line + local_y / line_height;
        let col = local_x / char_width;
        (line, col)
    }
}

/// Handle a click on a text input: move the cursor to the clicked position.
/// If shift is held, extend the selection instead of moving.
pub open spec fn text_input_handle_click(
    session: TextEditSession,
    config: TextInputConfig,
    local_x: nat,
    local_y: nat,
    char_width: nat,
    line_height: nat,
    scroll_line: nat,
    shift: bool,
) -> TextEditSession {
    let (line, col) = text_input_click_pos(
        local_x, local_y, char_width, line_height, scroll_line);
    let (text_pos, affinity) = match config.line_width {
        Some(w) => {
            let pos = wrapped_visual_to_pos(session.model.text, line, col, w);
            (pos, Affinity::Downstream)
        },
        None => visual_to_text_pos(session.model.text, line, col),
    };
    let new_model = if shift {
        TextModel { focus: text_pos, focus_affinity: affinity, ..session.model }
    } else {
        TextModel {
            anchor: text_pos, focus: text_pos,
            focus_affinity: affinity, ..session.model
        }
    };
    TextEditSession { model: new_model, ..session }
}

/// Click without shift resets selection: anchor == focus.
pub proof fn lemma_click_no_shift_collapses_selection(
    session: TextEditSession,
    config: TextInputConfig,
    local_x: nat,
    local_y: nat,
    char_width: nat,
    line_height: nat,
    scroll_line: nat,
)
    ensures ({
        let result = text_input_handle_click(
            session, config, local_x, local_y,
            char_width, line_height, scroll_line, false);
        result.model.anchor == result.model.focus
    }),
{}

} // verus!
