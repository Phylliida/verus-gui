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

// ──────────────────────────────────────────────────────────────────────
// Bridge lemmas: connect iterative scan to recursive spec
// ──────────────────────────────────────────────────────────────────────

/// If from + pattern.len() > text.len() or from > text.len(), find_next is None.
pub proof fn lemma_find_next_scan_none_out_of_range(
    text: Seq<char>, pattern: Seq<char>, from: nat,
)
    requires pattern.len() > 0,
    ensures
        (from + pattern.len() > text.len() || from > text.len())
            ==> find_next(text, pattern, from).is_none(),
{
    // find_next_scan with from + pattern.len() > text.len() returns None immediately
    // (second base case of the recursion)
}

/// If seq_matches_at(text, pattern, i) and no match in [from, i),
/// then find_next_scan(text, pattern, from, fuel) == Some(i)
/// when fuel >= i - from + 1.
pub proof fn lemma_find_next_scan_matches_first(
    text: Seq<char>, pattern: Seq<char>, from: nat, i: nat, fuel: nat,
)
    requires
        pattern.len() > 0,
        from <= i,
        i + pattern.len() <= text.len(),
        seq_matches_at(text, pattern, i),
        forall|p: nat| from <= p && p < i ==> !seq_matches_at(text, pattern, p),
        fuel >= i - from + 1,
    ensures
        find_next_scan(text, pattern, from, fuel) == Some(i),
    decreases i - from,
{
    if from == i {
        // scan finds match at from == i
    } else {
        // from < i. seq_matches_at(text, pattern, from) is false (from < i, invariant).
        // So scan recurses: find_next_scan(text, pattern, from+1, fuel-1)
        // By IH with from' = from+1, fuel' = fuel-1 >= i - (from+1) + 1:
        lemma_find_next_scan_matches_first(
            text, pattern, from + 1, i, (fuel - 1) as nat);
    }
}

/// If no match exists in the valid range, find_next returns None.
pub proof fn lemma_find_next_scan_exhausted(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        pattern.len() > 0,
        from + fuel >= text.len(),
        forall|p: nat| from <= p && p + pattern.len() <= text.len()
            ==> !seq_matches_at(text, pattern, p),
    ensures
        find_next_scan(text, pattern, from, fuel).is_none(),
    decreases fuel,
{
    if fuel == 0 {
        // from + 0 >= text.len() → from >= text.len() → from + pattern.len() > text.len() → base case
    } else if from + pattern.len() > text.len() {
    } else {
        // (from+1) + (fuel-1) = from + fuel >= text.len()
        lemma_find_next_scan_exhausted(text, pattern, from + 1, (fuel - 1) as nat);
    }
}

/// Bridge for find_prev: if seq_matches_at(text, pattern, pos) and
/// no match in (pos, from), then find_prev(text, pattern, from) == Some(pos).
pub proof fn lemma_find_prev_scan_matches_last(
    text: Seq<char>, pattern: Seq<char>, from: nat, pos: nat, fuel: nat,
)
    requires
        pattern.len() > 0,
        pos < from,
        pos + pattern.len() <= text.len(),
        seq_matches_at(text, pattern, pos),
        forall|p: nat| pos < p && p < from ==> !seq_matches_at(text, pattern, p),
        fuel >= from,
    ensures
        find_prev_scan(text, pattern, from, fuel) == Some(pos),
    decreases fuel,
{
    if fuel == 0 || from == 0 {
        // Impossible: pos < from and fuel >= from > 0
    } else {
        let check = (from - 1) as nat;
        if check == pos {
            // Found match at pos
        } else {
            // check > pos or check doesn't match
            // If check matches: check > pos and check < from, contradicts "no match in (pos, from)"
            // So check doesn't match. Recurse with from' = check.
            if seq_matches_at(text, pattern, check) {
                // check > pos and pos < check < from, contradicts forall
                assert(false);
            }
            lemma_find_prev_scan_matches_last(
                text, pattern, check, pos, (fuel - 1) as nat);
        }
    }
}

/// If no match exists before from, find_prev returns None.
pub proof fn lemma_find_prev_scan_exhausted(
    text: Seq<char>, pattern: Seq<char>, from: nat, fuel: nat,
)
    requires
        pattern.len() > 0,
        fuel >= from,
        forall|p: nat| p < from && p + pattern.len() <= text.len()
            ==> !seq_matches_at(text, pattern, p),
    ensures
        find_prev_scan(text, pattern, from, fuel).is_none(),
    decreases fuel,
{
    if fuel == 0 || from == 0 {
    } else {
        let check = (from - 1) as nat;
        // check < from, so !seq_matches_at by precondition (if in range)
        lemma_find_prev_scan_exhausted(text, pattern, check, (fuel - 1) as nat);
    }
}

} // verus!
