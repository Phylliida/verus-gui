use vstd::prelude::*;
use super::*;
use super::cursor::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Selection rectangles
// ──────────────────────────────────────────────────────────────────────

/// Sentinel value meaning "to end of line" for end_col.
pub open spec fn LINE_END_SENTINEL() -> nat { 0xFFFF_FFFF }

/// A rectangle covering part of a line in the selection highlight.
pub struct SelectionRect {
    pub line: nat,
    pub start_col: nat,
    pub end_col: nat,
}

/// Compute highlight rectangles for the selection between `anchor` and `focus`.
/// Returns one rect per line the selection spans.
/// Empty selection → empty sequence.
pub open spec fn selection_rects(
    text: Seq<char>, anchor: nat, focus: nat,
) -> Seq<SelectionRect> {
    if anchor == focus {
        Seq::empty()
    } else {
        let (sel_start, sel_end) = selection_range(anchor, focus);
        let (start_line, start_col) = text_pos_to_visual(text, sel_start, Affinity::Downstream);
        let (end_line, end_col) = text_pos_to_visual(text, sel_end, Affinity::Upstream);
        if start_line == end_line {
            // Single line selection
            seq![SelectionRect { line: start_line, start_col, end_col }]
        } else {
            // Multi-line: first partial + full middle lines + last partial
            selection_rects_multiline(
                text, start_line, start_col, end_line, end_col)
        }
    }
}

/// Build rects for a multi-line selection.
/// First line: start_col to end of line (sentinel).
/// Middle lines: full line.
/// Last line: start of line to end_col.
pub open spec fn selection_rects_multiline(
    text: Seq<char>,
    start_line: nat,
    start_col: nat,
    end_line: nat,
    end_col: nat,
) -> Seq<SelectionRect>
    recommends start_line < end_line,
    decreases end_line - start_line,
{
    if start_line >= end_line {
        Seq::empty()
    } else if start_line + 1 == end_line {
        // Just two lines: first partial + last partial
        seq![
            SelectionRect {
                line: start_line,
                start_col,
                end_col: LINE_END_SENTINEL(),
            },
            SelectionRect {
                line: end_line,
                start_col: 0,
                end_col,
            },
        ]
    } else {
        // First line + recurse for middle + last
        seq![SelectionRect {
            line: start_line,
            start_col,
            end_col: LINE_END_SENTINEL(),
        }].add(
            selection_rects_multiline(
                text, start_line + 1, 0, end_line, end_col)
        )
    }
}

/// Number of lines the selection spans.
pub open spec fn selection_line_count(
    text: Seq<char>, anchor: nat, focus: nat,
) -> nat {
    if anchor == focus {
        0
    } else {
        let (sel_start, sel_end) = selection_range(anchor, focus);
        let (start_line, _) = text_pos_to_visual(text, sel_start, Affinity::Downstream);
        let (end_line, _) = text_pos_to_visual(text, sel_end, Affinity::Upstream);
        if end_line >= start_line {
            ((end_line - start_line) + 1) as nat
        } else {
            1nat
        }
    }
}

} // verus!
