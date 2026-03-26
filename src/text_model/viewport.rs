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

// ──────────────────────────────────────────────────────────────────────
// Viewport proofs
// ──────────────────────────────────────────────────────────────────────

/// After scroll_to_cursor, the cursor is visible (when visible_lines > 0).
pub proof fn lemma_scroll_to_cursor_makes_visible(
    vp: TextViewport, cursor_line: nat,
)
    requires vp.visible_lines > 0,
    ensures cursor_visible(scroll_to_cursor(vp, cursor_line), cursor_line),
{
    let result = scroll_to_cursor(vp, cursor_line);
    if cursor_line < vp.scroll_line {
        // result.scroll_line = cursor_line
        // cursor_line >= cursor_line ✓
        // cursor_line < cursor_line + visible_lines (since visible_lines > 0) ✓
    } else if cursor_line >= vp.scroll_line + vp.visible_lines {
        // result.scroll_line = cursor_line - visible_lines + 1
        // cursor_line >= cursor_line - visible_lines + 1 ✓ (since visible_lines >= 1)
        // cursor_line < (cursor_line - visible_lines + 1) + visible_lines = cursor_line + 1 ✓
    } else {
        // Already visible, no change
    }
}

/// scroll_to_cursor preserves visible_lines.
pub proof fn lemma_scroll_to_cursor_preserves_visible_lines(
    vp: TextViewport, cursor_line: nat,
)
    ensures scroll_to_cursor(vp, cursor_line).visible_lines == vp.visible_lines,
{
}

/// scroll_to_cursor is idempotent: applying it twice gives the same result.
pub proof fn lemma_scroll_to_cursor_idempotent(
    vp: TextViewport, cursor_line: nat,
)
    requires vp.visible_lines > 0,
    ensures
        scroll_to_cursor(scroll_to_cursor(vp, cursor_line), cursor_line)
            === scroll_to_cursor(vp, cursor_line),
{
    let r = scroll_to_cursor(vp, cursor_line);
    // r makes cursor visible: cursor_line >= r.scroll_line && cursor_line < r.scroll_line + r.visible_lines
    lemma_scroll_to_cursor_makes_visible(vp, cursor_line);
    // So the second call sees the cursor already visible → returns r unchanged
}

/// scroll_to_cursor is a no-op when the cursor is already visible.
pub proof fn lemma_scroll_to_cursor_noop_when_visible(
    vp: TextViewport, cursor_line: nat,
)
    requires cursor_visible(vp, cursor_line),
    ensures scroll_to_cursor(vp, cursor_line) === vp,
{
}

/// scroll_by keeps scroll_line in [0, max(total_lines-1, 0)].
pub proof fn lemma_scroll_by_in_bounds(
    vp: TextViewport, delta: int, total_lines: nat,
)
    ensures ({
        let result = scroll_by(vp, delta, total_lines);
        if total_lines == 0 {
            result.scroll_line == 0
        } else {
            result.scroll_line <= (total_lines - 1) as nat
        }
    }),
{
}

/// scroll_by preserves visible_lines.
pub proof fn lemma_scroll_by_preserves_visible_lines(
    vp: TextViewport, delta: int, total_lines: nat,
)
    ensures scroll_by(vp, delta, total_lines).visible_lines == vp.visible_lines,
{
}

/// scroll_by with delta=0 is a no-op when scroll_line < total_lines.
pub proof fn lemma_scroll_by_zero_noop(
    vp: TextViewport, total_lines: nat,
)
    requires total_lines > 0, vp.scroll_line < total_lines,
    ensures scroll_by(vp, 0, total_lines) === vp,
{
}

} // verus!
