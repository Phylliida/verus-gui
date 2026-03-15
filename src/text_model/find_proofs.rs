use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::find::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Pattern matching properties
// ──────────────────────────────────────────────────────────────────────

/// A text always matches itself at position 0.
pub proof fn lemma_seq_matches_at_self(text: Seq<char>)
    requires text.len() > 0,
    ensures seq_matches_at(text, text, 0),
{
    assert forall|i: nat| i < text.len() implies
        text[(0 + i) as int] == #[trigger] text[i as int]
    by {}
}

/// If `text[pos..pos+pattern.len()) == pattern`, then seq_matches_at holds.
pub proof fn lemma_seq_matches_at_subrange(
    text: Seq<char>, pattern: Seq<char>, pos: nat,
)
    requires
        pos + pattern.len() <= text.len(),
        text.subrange(pos as int, (pos + pattern.len()) as int) =~= pattern,
    ensures
        seq_matches_at(text, pattern, pos),
{
    assert forall|i: nat| i < pattern.len() implies
        text[(pos + i) as int] == #[trigger] pattern[i as int]
    by {
        assert(text.subrange(pos as int, (pos + pattern.len()) as int)[i as int]
            == text[(pos + i) as int]);
    }
}

// ──────────────────────────────────────────────────────────────────────
// find_next correctness
// ──────────────────────────────────────────────────────────────────────

/// If find_next_scan returns Some(pos), then the pattern matches at pos.
pub proof fn lemma_find_next_scan_correct(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        find_next_scan(text, pattern, from, fuel) is Some,
    ensures
        seq_matches_at(text, pattern, find_next_scan(text, pattern, from, fuel).unwrap()),
        find_next_scan(text, pattern, from, fuel).unwrap() >= from,
    decreases fuel,
{
    if fuel == 0 {
    } else if from + pattern.len() > text.len() {
    } else if seq_matches_at(text, pattern, from) {
    } else {
        lemma_find_next_scan_correct(text, pattern, from + 1, (fuel - 1) as nat);
    }
}

/// find_next returns a valid match position.
pub proof fn lemma_find_next_correct(
    text: Seq<char>, pattern: Seq<char>, from: nat,
)
    requires
        find_next(text, pattern, from) is Some,
    ensures
        seq_matches_at(text, pattern, find_next(text, pattern, from).unwrap()),
        find_next(text, pattern, from).unwrap() >= from,
{
    lemma_find_next_scan_correct(text, pattern, from, text.len());
}

/// find_next_scan returns the FIRST match at or after `from`.
pub proof fn lemma_find_next_scan_first(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        find_next_scan(text, pattern, from, fuel) is Some,
    ensures
        forall|p: nat| from <= p < find_next_scan(text, pattern, from, fuel).unwrap()
            ==> !seq_matches_at(text, pattern, p),
    decreases fuel,
{
    if fuel == 0 {
    } else if from + pattern.len() > text.len() {
    } else if seq_matches_at(text, pattern, from) {
        // Returns from; no positions in [from, from) to check
    } else {
        lemma_find_next_scan_first(text, pattern, from + 1, (fuel - 1) as nat);
        // By IH: no match in [from+1, result). And from doesn't match.
    }
}

/// find_next returns the first match.
pub proof fn lemma_find_next_first(
    text: Seq<char>, pattern: Seq<char>, from: nat,
)
    requires
        find_next(text, pattern, from) is Some,
    ensures
        forall|p: nat| from <= p < find_next(text, pattern, from).unwrap()
            ==> !seq_matches_at(text, pattern, p),
{
    lemma_find_next_scan_first(text, pattern, from, text.len());
}

/// If find_next_scan returns None, there is no match at or after `from`
/// within the fuel range.
pub proof fn lemma_find_next_scan_none(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        find_next_scan(text, pattern, from, fuel).is_none(),
        pattern.len() > 0,
    ensures
        forall|p: nat| from <= p && p + pattern.len() <= text.len()
            && p < from + fuel
            ==> !seq_matches_at(text, pattern, p),
    decreases fuel,
{
    if fuel == 0 {
    } else if from + pattern.len() > text.len() {
        // All p >= from with p + pattern.len() <= text.len() is empty
    } else {
        // !seq_matches_at(text, pattern, from)
        // and find_next_scan(text, pattern, from+1, fuel-1) is None
        lemma_find_next_scan_none(text, pattern, from + 1, (fuel - 1) as nat);
    }
}

/// If find_next returns None, no match exists at or after `from`
/// (for non-empty patterns).
pub proof fn lemma_find_next_none(
    text: Seq<char>, pattern: Seq<char>, from: nat,
)
    requires
        find_next(text, pattern, from).is_none(),
        pattern.len() > 0,
    ensures
        forall|p: nat| from <= p && p + pattern.len() <= text.len()
            ==> !seq_matches_at(text, pattern, p),
{
    lemma_find_next_scan_none(text, pattern, from, text.len());
}

// ──────────────────────────────────────────────────────────────────────
// find_prev correctness
// ──────────────────────────────────────────────────────────────────────

/// find_prev_scan returns a valid match position.
pub proof fn lemma_find_prev_scan_correct(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        find_prev_scan(text, pattern, from, fuel) is Some,
    ensures
        seq_matches_at(text, pattern, find_prev_scan(text, pattern, from, fuel).unwrap()),
        find_prev_scan(text, pattern, from, fuel).unwrap() < from,
    decreases fuel,
{
    if fuel == 0 || from == 0 {
    } else {
        let pos = (from - 1) as nat;
        if seq_matches_at(text, pattern, pos) {
        } else {
            lemma_find_prev_scan_correct(text, pattern, pos, (fuel - 1) as nat);
        }
    }
}

/// find_prev returns a valid match position before `from`.
pub proof fn lemma_find_prev_correct(
    text: Seq<char>, pattern: Seq<char>, from: nat,
)
    requires
        find_prev(text, pattern, from) is Some,
    ensures
        seq_matches_at(text, pattern, find_prev(text, pattern, from).unwrap()),
        find_prev(text, pattern, from).unwrap() < from,
{
    lemma_find_prev_scan_correct(text, pattern, from, from);
}

} // verus!
