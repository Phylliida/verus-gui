use vstd::prelude::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Text viewport
// ──────────────────────────────────────────────────────────────────────

/// Viewport state for a scrollable text area.
pub struct TextViewport {
    pub scroll_line: nat,
    pub visible_lines: nat,
}

/// Whether the cursor line is within the visible viewport.
pub open spec fn cursor_visible(vp: TextViewport, cursor_line: nat) -> bool {
    cursor_line >= vp.scroll_line
    && cursor_line < vp.scroll_line + vp.visible_lines
}

/// Adjust scroll_line so that cursor_line is visible.
/// If cursor is above viewport, scroll up to it.
/// If cursor is below viewport, scroll down to show it.
/// If already visible, no change.
pub open spec fn scroll_to_cursor(
    vp: TextViewport, cursor_line: nat,
) -> TextViewport {
    if vp.visible_lines == 0 {
        vp
    } else if cursor_line < vp.scroll_line {
        // Cursor above viewport: scroll up
        TextViewport { scroll_line: cursor_line, ..vp }
    } else if cursor_line >= vp.scroll_line + vp.visible_lines {
        // Cursor below viewport: scroll down
        TextViewport {
            scroll_line: (cursor_line - vp.visible_lines + 1) as nat,
            ..vp
        }
    } else {
        vp
    }
}

/// Scroll by delta lines (positive = down, negative = up), clamped to [0, total_lines).
pub open spec fn scroll_by(
    vp: TextViewport, delta: int, total_lines: nat,
) -> TextViewport {
    let new_scroll = (vp.scroll_line as int) + delta;
    let clamped = if new_scroll < 0 {
        0nat
    } else if total_lines == 0 {
        0nat
    } else if new_scroll >= total_lines as int {
        (total_lines - 1) as nat
    } else {
        new_scroll as nat
    };
    TextViewport { scroll_line: clamped, ..vp }
}

} // verus!
