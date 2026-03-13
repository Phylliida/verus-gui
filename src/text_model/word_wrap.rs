use vstd::prelude::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Soft word wrap
// ──────────────────────────────────────────────────────────────────────

/// Check if a character is a word-break opportunity (space, tab, hyphen).
pub open spec fn is_break_opportunity(c: char) -> bool {
    c == ' ' || c == '\t' || c == '-'
}

/// Find the next '\n' position at or after `pos`, or text.len() if none.
pub open spec fn next_newline_or_end(text: Seq<char>, pos: nat) -> nat
    decreases text.len() - pos,
{
    if pos >= text.len() {
        text.len()
    } else if text[pos as int] == '\n' {
        pos
    } else {
        next_newline_or_end(text, pos + 1)
    }
}

/// next_newline_or_end always returns >= pos (when pos <= text.len()).
pub proof fn lemma_next_newline_or_end_ge(text: Seq<char>, pos: nat)
    requires pos <= text.len(),
    ensures next_newline_or_end(text, pos) >= pos,
    decreases text.len() - pos,
{
    if pos >= text.len() {
    } else if text[pos as int] == '\n' {
    } else {
        lemma_next_newline_or_end_ge(text, pos + 1);
    }
}

/// next_newline_or_end always returns <= text.len().
pub proof fn lemma_next_newline_or_end_le(text: Seq<char>, pos: nat)
    ensures next_newline_or_end(text, pos) <= text.len(),
    decreases text.len() - pos,
{
    if pos >= text.len() {
    } else if text[pos as int] == '\n' {
    } else {
        lemma_next_newline_or_end_le(text, pos + 1);
    }
}

/// Count the number of visual lines after wrapping.
pub open spec fn wrapped_line_count(
    text: Seq<char>, line_width: nat,
) -> nat {
    if line_width == 0 || text.len() == 0 {
        1
    } else {
        count_visual_lines(text, 0, line_width, text.len() + 1)
    }
}

/// Count visual lines starting from position `pos`, with fuel.
pub open spec fn count_visual_lines(
    text: Seq<char>, pos: nat, line_width: nat, fuel: nat,
) -> nat
    recommends line_width > 0,
    decreases fuel,
{
    if fuel == 0 || pos >= text.len() {
        1  // trailing empty line (or fuel exhausted)
    } else {
        let hard_end = next_newline_or_end(text, pos);
        let line_len = if hard_end >= pos { (hard_end - pos) as nat } else { 0nat };
        let visual: nat = if line_len == 0 || line_width == 0 {
            1nat
        } else {
            // ceil(line_len / line_width) = (line_len - 1) / line_width + 1
            (((line_len - 1) as nat) / line_width + 1) as nat
        };
        if hard_end < text.len() && hard_end >= pos {
            (visual + count_visual_lines(
                text, (hard_end + 1) as nat, line_width, (fuel - 1) as nat)) as nat
        } else {
            visual
        }
    }
}

/// Map a text position to visual (line, column) accounting for soft wrap.
/// Uninterpreted — implemented as external_body in exec.
pub uninterp spec fn wrapped_pos_to_visual(
    text: Seq<char>, pos: nat, line_width: nat,
) -> (nat, nat);

/// Map visual (line, column) back to text position accounting for soft wrap.
/// Uninterpreted — implemented as external_body in exec.
pub uninterp spec fn wrapped_visual_to_pos(
    text: Seq<char>, line: nat, col: nat, line_width: nat,
) -> nat;

} // verus!
