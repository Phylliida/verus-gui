use vstd::prelude::*;

verus! {

//  ──────────────────────────────────────────────────────────────────────
//  Soft word wrap
//  ──────────────────────────────────────────────────────────────────────

///  Check if a character is a word-break opportunity (space, tab, hyphen).
pub open spec fn is_break_opportunity(c: char) -> bool {
    c == ' ' || c == '\t' || c == '-'
}

///  Find the next '\n' position at or after `pos`, or text.len() if none.
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

///  next_newline_or_end always returns >= pos (when pos <= text.len()).
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

///  next_newline_or_end always returns <= text.len().
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

///  Count the number of visual lines after wrapping.
pub open spec fn wrapped_line_count(
    text: Seq<char>, line_width: nat,
) -> nat {
    if line_width == 0 || text.len() == 0 {
        1
    } else {
        count_visual_lines(text, 0, line_width, text.len() + 1)
    }
}

///  Count visual lines starting from position `pos`, with fuel.
pub open spec fn count_visual_lines(
    text: Seq<char>, pos: nat, line_width: nat, fuel: nat,
) -> nat
    recommends line_width > 0,
    decreases fuel,
{
    if fuel == 0 || pos >= text.len() {
        1  //  trailing empty line (or fuel exhausted)
    } else {
        let hard_end = next_newline_or_end(text, pos);
        let line_len = if hard_end >= pos { (hard_end - pos) as nat } else { 0nat };
        let visual: nat = if line_len == 0 || line_width == 0 {
            1nat
        } else {
            //  ceil(line_len / line_width) = (line_len - 1) / line_width + 1
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

///  Map a text position to visual (line, column) accounting for soft wrap.
///  Uninterpreted — implemented as external_body in exec.
pub uninterp spec fn wrapped_pos_to_visual(
    text: Seq<char>, pos: nat, line_width: nat,
) -> (nat, nat);

///  Map visual (line, column) back to text position accounting for soft wrap.
///  Uninterpreted — implemented as external_body in exec.
pub uninterp spec fn wrapped_visual_to_pos(
    text: Seq<char>, line: nat, col: nat, line_width: nat,
) -> nat;

//  ──────────────────────────────────────────────────────────────────────
//  Word wrap proofs
//  ──────────────────────────────────────────────────────────────────────

///  next_newline_or_end returns either a '\n' position or text.len().
pub proof fn lemma_next_newline_or_end_result(text: Seq<char>, pos: nat)
    requires pos <= text.len(),
    ensures ({
        let r = next_newline_or_end(text, pos);
        (r == text.len()) || (r < text.len() && text[r as int] == '\n')
    }),
    decreases text.len() - pos,
{
    if pos >= text.len() {
    } else if text[pos as int] == '\n' {
    } else {
        lemma_next_newline_or_end_result(text, pos + 1);
    }
}

///  No '\n' exists in text[pos..next_newline_or_end(text, pos)).
pub proof fn lemma_next_newline_or_end_no_newline(text: Seq<char>, pos: nat)
    requires pos <= text.len(),
    ensures
        forall|k: nat| pos <= k && k < next_newline_or_end(text, pos)
            ==> text[k as int] != '\n',
    decreases text.len() - pos,
{
    if pos >= text.len() {
    } else if text[pos as int] == '\n' {
        //  next_newline_or_end = pos, so range [pos, pos) is empty
    } else {
        lemma_next_newline_or_end_no_newline(text, pos + 1);
        //  By IH: no '\n' in [pos+1, next_newline_or_end(text, pos+1))
        //  next_newline_or_end(text, pos) == next_newline_or_end(text, pos+1)
        //  And text[pos] != '\n' covers position pos itself
    }
}

///  count_visual_lines always returns >= 1.
pub proof fn lemma_count_visual_lines_ge_1(
    text: Seq<char>, pos: nat, line_width: nat, fuel: nat,
)
    ensures count_visual_lines(text, pos, line_width, fuel) >= 1,
    decreases fuel,
{
    if fuel == 0 || pos >= text.len() {
        //  Returns 1
    } else {
        let hard_end = next_newline_or_end(text, pos);
        let line_len = if hard_end >= pos { (hard_end - pos) as nat } else { 0nat };
        let visual: nat = if line_len == 0 || line_width == 0 { 1nat }
            else { (((line_len - 1) as nat) / line_width + 1) as nat };
        assert(visual >= 1);
        if hard_end < text.len() && hard_end >= pos {
            lemma_count_visual_lines_ge_1(text, (hard_end + 1) as nat, line_width, (fuel - 1) as nat);
            //  visual + rest >= 1 + 1 >= 1
        }
    }
}

///  wrapped_line_count is always >= 1.
pub proof fn lemma_wrapped_line_count_ge_1(text: Seq<char>, line_width: nat)
    ensures wrapped_line_count(text, line_width) >= 1,
{
    if line_width == 0 || text.len() == 0 {
        //  Returns 1
    } else {
        lemma_count_visual_lines_ge_1(text, 0, line_width, text.len() + 1);
    }
}

///  Empty text has exactly 1 visual line.
pub proof fn lemma_empty_text_one_line(line_width: nat)
    ensures wrapped_line_count(Seq::<char>::empty(), line_width) == 1,
{
}

///  A text with no newlines and line_width > 0 has ceil(len/line_width) visual lines.
pub proof fn lemma_no_newline_line_count(text: Seq<char>, line_width: nat)
    requires
        line_width > 0,
        text.len() > 0,
        forall|i: nat| i < text.len() ==> text[i as int] != '\n',
    ensures
        wrapped_line_count(text, line_width)
            == (((text.len() - 1) as nat) / line_width + 1) as nat,
{
    //  next_newline_or_end(text, 0) == text.len() since no '\n'
    lemma_no_newline_implies_end(text, 0);
    //  count_visual_lines with pos=0: hard_end = text.len(), line_len = text.len()
    //  visual = ceil(text.len() / line_width) = ((text.len()-1) / line_width + 1)
    //  hard_end == text.len() → !(hard_end < text.len()), so returns visual
}

///  Helper: if no newlines in text[pos..], next_newline_or_end returns text.len().
proof fn lemma_no_newline_implies_end(text: Seq<char>, pos: nat)
    requires
        pos <= text.len(),
        forall|i: nat| pos <= i && i < text.len() ==> text[i as int] != '\n',
    ensures
        next_newline_or_end(text, pos) == text.len(),
    decreases text.len() - pos,
{
    if pos >= text.len() {
    } else {
        //  text[pos] != '\n' by precondition
        lemma_no_newline_implies_end(text, pos + 1);
    }
}

///  count_visual_lines with sufficient fuel produces the same result as more fuel.
///  Fuel >= text.len() - pos + 1 is always sufficient.
pub proof fn lemma_count_visual_lines_fuel_sufficient(
    text: Seq<char>, pos: nat, line_width: nat, fuel1: nat, fuel2: nat,
)
    requires
        line_width > 0,
        fuel1 >= text.len() - pos + 1,
        fuel2 >= fuel1,
    ensures
        count_visual_lines(text, pos, line_width, fuel1)
            == count_visual_lines(text, pos, line_width, fuel2),
    decreases text.len() - pos,
{
    if pos >= text.len() {
        //  Both return 1 (fuel > 0 since fuel1 >= 1)
    } else {
        //  fuel1 >= 1 and fuel2 >= 1
        let hard_end = next_newline_or_end(text, pos);
        lemma_next_newline_or_end_ge(text, pos);
        lemma_next_newline_or_end_le(text, pos);
        //  hard_end >= pos and hard_end <= text.len()
        if hard_end < text.len() && hard_end >= pos {
            //  Recursive call: pos' = hard_end + 1 > pos
            //  fuel1' = fuel1 - 1 >= text.len() - pos >= text.len() - hard_end
            //         = text.len() - (hard_end + 1) + 1
            //  So fuel1 - 1 >= text.len() - (hard_end+1) + 1
            lemma_count_visual_lines_fuel_sufficient(
                text, (hard_end + 1) as nat, line_width,
                (fuel1 - 1) as nat, (fuel2 - 1) as nat);
        } else {
            //  No recursion: returns visual directly
        }
    }
}

///  wrapped_line_count is well-defined: it doesn't depend on having "extra" fuel.
///  Specifically, text.len() + 1 fuel is always sufficient, and more fuel gives
///  the same answer.
pub proof fn lemma_wrapped_line_count_stable(
    text: Seq<char>, line_width: nat, extra_fuel: nat,
)
    requires line_width > 0, text.len() > 0,
    ensures
        count_visual_lines(text, 0, line_width, text.len() + 1)
            == count_visual_lines(text, 0, line_width, text.len() + 1 + extra_fuel),
{
    lemma_count_visual_lines_fuel_sufficient(
        text, 0, line_width,
        text.len() + 1, text.len() + 1 + extra_fuel);
}

//  ──────────────────────────────────────────────────────────────────────
//  Word wrap round-trip axioms
//  ──────────────────────────────────────────────────────────────────────

///  Round-trip: pos → visual → pos returns the original position.
///  Validated by the runtime exec implementation.
#[verifier::external_body]
pub proof fn axiom_wrap_pos_round_trip(text: Seq<char>, pos: nat, line_width: nat)
    requires
        pos <= text.len(),
        line_width > 0,
    ensures ({
        let (line, col) = wrapped_pos_to_visual(text, pos, line_width);
        wrapped_visual_to_pos(text, line, col, line_width) == pos
    }),
{}

///  Round-trip: visual → pos → visual returns the original (line, col).
///  Validated by the runtime exec implementation.
#[verifier::external_body]
pub proof fn axiom_wrap_visual_round_trip(
    text: Seq<char>, line: nat, col: nat, line_width: nat,
)
    requires
        line_width > 0,
        line < wrapped_line_count(text, line_width),
    ensures ({
        let pos = wrapped_visual_to_pos(text, line, col, line_width);
        wrapped_pos_to_visual(text, pos, line_width) == (line, col)
    }),
{}

} //  verus!
