use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::cursor::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Pattern matching
// ──────────────────────────────────────────────────────────────────────

/// Whether `text[pos..pos+pattern.len())` matches `pattern`.
pub open spec fn seq_matches_at(text: Seq<char>, pattern: Seq<char>, pos: nat) -> bool {
    pos + pattern.len() <= text.len()
    && forall|i: nat| i < pattern.len() ==>
        text[(pos + i) as int] == #[trigger] pattern[i as int]
}

// ──────────────────────────────────────────────────────────────────────
// Find next/prev
// ──────────────────────────────────────────────────────────────────────

/// Scan forward from `from` for the first match of `pattern` in `text`.
/// Returns the position of the first match, or None if no match exists.
pub open spec fn find_next_scan(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
) -> Option<nat>
    decreases fuel,
{
    if fuel == 0 {
        None
    } else if from + pattern.len() > text.len() {
        None
    } else if seq_matches_at(text, pattern, from) {
        Some(from)
    } else {
        find_next_scan(text, pattern, from + 1, (fuel - 1) as nat)
    }
}

/// Find the next occurrence of `pattern` in `text` starting at position `from`.
pub open spec fn find_next(
    text: Seq<char>, pattern: Seq<char>, from: nat,
) -> Option<nat> {
    if pattern.len() == 0 {
        None  // Empty pattern: no match
    } else {
        find_next_scan(text, pattern, from, text.len())
    }
}

/// Scan backward from `from` (exclusive upper bound on start pos) for pattern.
pub open spec fn find_prev_scan(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
) -> Option<nat>
    decreases fuel,
{
    if fuel == 0 || from == 0 {
        None
    } else {
        let pos = (from - 1) as nat;
        if seq_matches_at(text, pattern, pos) {
            Some(pos)
        } else {
            find_prev_scan(text, pattern, pos, (fuel - 1) as nat)
        }
    }
}

/// Find the previous occurrence of `pattern` in `text` before position `from`.
pub open spec fn find_prev(
    text: Seq<char>, pattern: Seq<char>, from: nat,
) -> Option<nat> {
    if pattern.len() == 0 {
        None
    } else {
        find_prev_scan(text, pattern, from, from)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Replace
// ──────────────────────────────────────────────────────────────────────

/// Replace the substring at `[start..start+pat_len)` with `repl`.
/// Returns a new TextModel with cursor after the replacement.
pub open spec fn replace_at(
    model: TextModel, start: nat, pat_len: nat, repl: Seq<char>,
) -> TextModel {
    let end = start + pat_len;
    let new_styles = Seq::new(repl.len(), |i: int| model.default_style);
    let new_focus = start + repl.len();
    splice(model, start, end, repl, new_styles, new_focus)
}

/// Replace all occurrences of `pattern` with `repl`, starting from `from`.
/// Uses fuel for termination.
pub open spec fn replace_all(
    model: TextModel, pattern: Seq<char>, repl: Seq<char>,
    from: nat, fuel: nat,
) -> TextModel
    decreases fuel,
{
    if fuel == 0 {
        model
    } else {
        match find_next(model.text, pattern, from) {
            None => model,
            Some(pos) => {
                let new_model = replace_at(model, pos, pattern.len(), repl);
                // Continue searching after the replacement
                let next_from = pos + repl.len();
                replace_all(new_model, pattern, repl, next_from, (fuel - 1) as nat)
            },
        }
    }
}

} // verus!
