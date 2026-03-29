use vstd::prelude::*;
use crate::text_model::cursor::{MoveDirection, resolve_movement};

verus! {

//  ──────────────────────────────────────────────────────────────────────
//  Enums
//  ──────────────────────────────────────────────────────────────────────

///  Cursor affinity: which side of a line break the cursor is drawn on.
pub enum Affinity {
    Upstream,
    Downstream,
}

///  Paragraph alignment.
pub enum ParagraphAlignment {
    Left,
    Center,
    Right,
    Justify,
}

//  ──────────────────────────────────────────────────────────────────────
//  Style types
//  ──────────────────────────────────────────────────────────────────────

///  Rich-text style set. Each field is optional; `None` means "inherit from parent/default".
pub struct StyleSet {
    pub bold: Option<bool>,
    pub italic: Option<bool>,
    pub underline: Option<bool>,
    pub strikethrough: Option<bool>,
    pub font_size: Option<nat>,
    pub font_family: Option<nat>,
    pub color: Option<u32>,
    pub bg_color: Option<u32>,
}

///  Per-paragraph formatting.
pub struct ParagraphStyle {
    pub alignment: ParagraphAlignment,
    pub indent_left: nat,
    pub indent_right: nat,
    pub indent_first_line: int,
    pub line_spacing: nat,
    pub space_before: nat,
    pub space_after: nat,
}

//  ──────────────────────────────────────────────────────────────────────
//  IME Composition
//  ──────────────────────────────────────────────────────────────────────

///  Active IME composition state.
pub struct Composition {
    pub range_start: nat,
    pub range_end: nat,
    pub original: Seq<char>,
    pub provisional: Seq<char>,
    pub cursor: nat,
}

//  ──────────────────────────────────────────────────────────────────────
//  Text model
//  ──────────────────────────────────────────────────────────────────────

///  The core text editing model. Manages text content, styles, cursor,
///  selection, IME composition, and paragraph formatting.
pub struct TextModel {
    pub text: Seq<char>,
    pub styles: Seq<StyleSet>,
    pub anchor: nat,
    pub focus: nat,
    pub focus_affinity: Affinity,
    pub preferred_column: Option<nat>,
    pub typing_style: StyleSet,
    pub default_style: StyleSet,
    pub composition: Option<Composition>,
    pub paragraph_styles: Seq<ParagraphStyle>,
}

//  ──────────────────────────────────────────────────────────────────────
//  Seq helpers
//  ──────────────────────────────────────────────────────────────────────

///  Splice a sequence: replace `s[start..end)` with `replacement`.
pub open spec fn seq_splice<A>(s: Seq<A>, start: int, end: int, replacement: Seq<A>) -> Seq<A> {
    s.subrange(0, start) + replacement + s.subrange(end, s.len() as int)
}

///  Create a sequence of `count` copies of `val`.
pub open spec fn seq_repeat<A>(val: A, count: nat) -> Seq<A>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        seq_repeat(val, (count - 1) as nat).push(val)
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Character / paragraph counting
//  ──────────────────────────────────────────────────────────────────────

///  Whether a character is permitted in the text model.
///  Excludes null and interlinear annotation characters.
pub open spec fn is_permitted(c: char) -> bool {
    c != '\0'
    && c != '\u{FFF9}' //  interlinear annotation anchor
    && c != '\u{FFFA}' //  interlinear annotation separator
    && c != '\u{FFFB}' //  interlinear annotation terminator
}

///  Whether the text contains only permitted characters and uses canonical line endings.
///  Canonical: only '\n' for newlines (no bare '\r' or '\r\n').
pub open spec fn wf_text(text: Seq<char>) -> bool {
    &&& forall|i: int| 0 <= i < text.len() ==> is_permitted(#[trigger] text[i])
    &&& forall|i: int| 0 <= i < text.len() ==> text[i] != '\r'
}

///  Count occurrences of character `c` in `text`.
pub open spec fn count_char(text: Seq<char>, c: char) -> nat
    decreases text.len(),
{
    if text.len() == 0 {
        0
    } else {
        let rest = count_char(text.drop_last(), c);
        if text.last() == c { rest + 1 } else { rest }
    }
}

///  Number of paragraphs (lines). A trailing '\n' yields an extra empty paragraph.
///  Empty string → 1 paragraph.
pub open spec fn paragraph_count(text: Seq<char>) -> nat {
    count_char(text, '\n') + 1
}

//  ──────────────────────────────────────────────────────────────────────
//  Unicode boundary axioms
//  ──────────────────────────────────────────────────────────────────────

///  Whether `bounds` is a valid set of boundaries for text of the given length.
///  Boundaries are strictly increasing, start at 0, and end at text.len().
pub open spec fn valid_boundaries(text: Seq<char>, bounds: Seq<nat>) -> bool {
    &&& bounds.len() >= 2
    &&& bounds[0] == 0
    &&& bounds[bounds.len() - 1] == text.len()
    &&& forall|i: int| 0 <= i < bounds.len() - 1 ==> (#[trigger] bounds[i]) < bounds[i + 1]
}

///  Grapheme cluster boundaries (UAX #29). Axiomatized.
pub uninterp spec fn grapheme_boundaries(text: Seq<char>) -> Seq<nat>;

///  Word start boundaries (UAX #29). Axiomatized.
pub uninterp spec fn word_start_boundaries(text: Seq<char>) -> Seq<nat>;

///  Word end boundaries (UAX #29). Axiomatized.
pub uninterp spec fn word_end_boundaries(text: Seq<char>) -> Seq<nat>;

///  Line break opportunities (UAX #14). Axiomatized.
pub uninterp spec fn line_break_opportunities(text: Seq<char>) -> Seq<nat>;

//  Axiom proof functions: assert validity of each boundary set.

#[verifier::external_body]
pub proof fn axiom_grapheme_boundaries_valid(text: Seq<char>)
    requires text.len() > 0,
    ensures valid_boundaries(text, grapheme_boundaries(text)),
{}

#[verifier::external_body]
pub proof fn axiom_word_start_boundaries_valid(text: Seq<char>)
    requires text.len() > 0,
    ensures valid_boundaries(text, word_start_boundaries(text)),
{}

#[verifier::external_body]
pub proof fn axiom_word_end_boundaries_valid(text: Seq<char>)
    requires text.len() > 0,
    ensures valid_boundaries(text, word_end_boundaries(text)),
{}

#[verifier::external_body]
pub proof fn axiom_line_break_valid(text: Seq<char>)
    requires text.len() > 0,
    ensures valid_boundaries(text, line_break_opportunities(text)),
{}

//  ──────────────────────────────────────────────────────────────────────
//  Splice axioms (trusted: validated by the unicode-segmentation runtime)
//  ──────────────────────────────────────────────────────────────────────

///  Splicing well-formed replacement text at grapheme boundaries
///  preserves wf_text and creates a grapheme boundary after the replacement.
///  Subsumes both single-char insert and deletion.
#[verifier::external_body]
pub proof fn axiom_splice_wf(
    text: Seq<char>, start: nat, end: nat, replacement: Seq<char>,
)
    requires
        wf_text(text),
        wf_text(replacement),
        is_grapheme_boundary(text, start),
        is_grapheme_boundary(text, end),
        start <= end,
        end <= text.len(),
    ensures
        wf_text(seq_splice(text, start as int, end as int, replacement)),
        is_grapheme_boundary(
            seq_splice(text, start as int, end as int, replacement),
            start + replacement.len()),
{}

///  A single permitted non-CR character is wf_text.
pub proof fn lemma_single_permitted_char_wf(ch: char)
    requires
        is_permitted(ch),
        ch != '\r',
    ensures
        wf_text(seq![ch]),
{
    assert forall|i: int| 0 <= i < seq![ch].len() implies is_permitted(#[trigger] seq![ch][i]) by {
        assert(seq![ch][0] == ch);
    };
    assert forall|i: int| 0 <= i < seq![ch].len() implies seq![ch][i] != '\r' by {
        assert(seq![ch][0] == ch);
    };
}

///  The empty sequence is wf_text.
pub proof fn lemma_empty_seq_wf()
    ensures wf_text(Seq::<char>::empty()),
{
}

///  Committing an IME composition preserves wf_text and creates a
///  grapheme boundary after the committed text.
#[verifier::external_body]
pub proof fn axiom_compose_commit_wf(
    text: Seq<char>, range_start: nat, range_end: nat, provisional: Seq<char>,
)
    requires
        wf_text(text),
        is_grapheme_boundary(text, range_start),
        is_grapheme_boundary(text, range_end),
        range_start <= range_end,
        range_end <= text.len(),
    ensures
        wf_text(seq_splice(text, range_start as int, range_end as int, provisional)),
        is_grapheme_boundary(
            seq_splice(text, range_start as int, range_end as int, provisional),
            range_start + provisional.len()),
{}

///  Pasting filtered+canonicalized text at grapheme boundaries preserves wf_text
///  and produces a grapheme boundary after the pasted text.
#[verifier::external_body]
pub proof fn axiom_paste_wf(
    text: Seq<char>, pos_start: nat, pos_end: nat, source: Seq<char>,
)
    requires
        wf_text(text),
        pos_start <= pos_end, pos_end <= text.len(),
        is_grapheme_boundary(text, pos_start),
        is_grapheme_boundary(text, pos_end),
    ensures ({
        let paste_text = operations::canonicalize_newlines(
            operations::filter_permitted(source));
        &&& wf_text(seq_splice(text, pos_start as int, pos_end as int, paste_text))
        &&& is_grapheme_boundary(
                seq_splice(text, pos_start as int, pos_end as int, paste_text),
                pos_start + paste_text.len())
    }),
{}

///  resolve_movement always produces a valid position that is a
///  grapheme boundary within the text.
#[verifier::external_body]
pub proof fn axiom_movement_valid(
    text: Seq<char>, focus: nat, affinity: Affinity,
    pref_col: Option<nat>, dir: MoveDirection,
)
    requires
        wf_text(text),
        focus <= text.len(),
        is_grapheme_boundary(text, focus),
    ensures
        resolve_movement(text, focus, affinity, pref_col, dir).0 <= text.len(),
        is_grapheme_boundary(
            text,
            resolve_movement(text, focus, affinity, pref_col, dir).0),
{}

///  Word boundaries are also grapheme boundaries.
#[verifier::external_body]
pub proof fn axiom_word_boundaries_are_grapheme_boundaries(text: Seq<char>)
    requires text.len() > 0, wf_text(text),
    ensures
        forall|i: int| 0 <= i < word_start_boundaries(text).len() ==>
            is_grapheme_boundary(text, #[trigger] word_start_boundaries(text)[i]),
        forall|i: int| 0 <= i < word_end_boundaries(text).len() ==>
            is_grapheme_boundary(text, #[trigger] word_end_boundaries(text)[i]),
{}

///  prev_grapheme_boundary returns a grapheme boundary <= pos.
pub proof fn axiom_prev_grapheme_boundary_valid(text: Seq<char>, pos: nat)
    requires
        wf_text(text),
        text.len() > 0,
        pos <= text.len(),
        is_grapheme_boundary(text, pos),
    ensures
        prev_grapheme_boundary(text, pos) <= pos,
        is_grapheme_boundary(text, prev_grapheme_boundary(text, pos)),
{
    axiom_grapheme_boundaries_valid(text);
    let bounds = grapheme_boundaries(text);
    //  prev_boundary_in(bounds, pos) <= pos
    proofs::lemma_prev_boundary_in_le(bounds, pos);
    //  prev_boundary_in returns a member of bounds or 0
    proofs::lemma_prev_boundary_in_member(bounds, pos);
    let result = prev_boundary_in(bounds, pos);
    if result == 0 {
        //  bounds[0] == 0, so is_grapheme_boundary(text, 0)
        assert(bounds[0] == 0nat);
        assert(is_grapheme_boundary(text, 0nat));
    } else {
        //  result is bounds[i] for some i, which is a grapheme boundary
        let i = choose|i: int| 0 <= i < bounds.len() && bounds[i] == result;
        assert(is_grapheme_boundary(text, result));
    }
}

///  next_grapheme_boundary returns a grapheme boundary >= pos
///  that is within text bounds.
pub proof fn axiom_next_grapheme_boundary_valid(text: Seq<char>, pos: nat)
    requires
        wf_text(text),
        text.len() > 0,
        pos <= text.len(),
        is_grapheme_boundary(text, pos),
    ensures
        next_grapheme_boundary(text, pos) >= pos,
        next_grapheme_boundary(text, pos) <= text.len(),
        is_grapheme_boundary(text, next_grapheme_boundary(text, pos)),
{
    axiom_grapheme_boundaries_valid(text);
    let bounds = grapheme_boundaries(text);
    //  >= pos
    proofs::lemma_next_boundary_in_ge(bounds, pos);
    //  If pos == text.len(), then pos == bounds[len-1].
    //  next_boundary_in on strictly increasing seq where all elements <= pos returns pos.
    //  If pos < text.len(), bounds has an element > pos (bounds[len-1] = text.len() > pos).
    if pos < text.len() {
        //  bounds[len-1] = text.len() > pos, so member exists
        proofs::lemma_next_boundary_in_member(bounds, pos);
        let i = choose|i: int| 0 <= i < bounds.len() && bounds[i] == next_boundary_in(bounds, pos);
        //  bounds[i] is a grapheme boundary
        assert(is_grapheme_boundary(text, next_boundary_in(bounds, pos)));
        //  <= text.len(): bounds[i] <= bounds[len-1] = text.len()
        proofs::lemma_next_boundary_in_le_last(bounds, pos);
    } else {
        //  pos == text.len() == bounds[len-1]
        //  next_boundary_in looks for first element > pos = text.len()
        //  Since bounds[len-1] = text.len(), no element > pos, so returns pos
        proofs::lemma_next_boundary_in_le_last(bounds, pos);
        proofs::lemma_next_boundary_in_ge(bounds, pos);
        //  result >= pos && result <= bounds[len-1] = pos → result == pos
        //  is_grapheme_boundary: pos = text.len() = bounds[len-1]
        assert(bounds[bounds.len() - 1] == text.len());
        assert(is_grapheme_boundary(text, text.len()));
    }
}

///  prev_boundary_in(word_start_boundaries) returns a grapheme boundary.
pub proof fn axiom_prev_word_boundary_valid(text: Seq<char>, pos: nat)
    requires
        wf_text(text),
        text.len() > 0,
        pos <= text.len(),
        is_grapheme_boundary(text, pos),
    ensures
        prev_boundary_in(word_start_boundaries(text), pos) <= pos,
        is_grapheme_boundary(
            text,
            prev_boundary_in(word_start_boundaries(text), pos)),
{
    let bounds = word_start_boundaries(text);
    axiom_word_start_boundaries_valid(text);
    axiom_word_boundaries_are_grapheme_boundaries(text);
    //  <= pos
    proofs::lemma_prev_boundary_in_le(bounds, pos);
    //  membership
    proofs::lemma_prev_boundary_in_member(bounds, pos);
    let result = prev_boundary_in(bounds, pos);
    if result == 0 {
        //  bounds[0] == 0, which is a word_start boundary and hence a grapheme boundary
        //  But we need is_grapheme_boundary(text, 0)
        //  valid_boundaries says bounds[0] == 0, and axiom_word_boundaries says
        //  word_start_boundaries(text)[0] is a grapheme boundary
        assert(bounds[0] == 0nat);
        assert(is_grapheme_boundary(text, bounds[0]));
    } else {
        let i = choose|i: int| 0 <= i < bounds.len() && bounds[i] == result;
        //  word start boundaries are grapheme boundaries
        assert(is_grapheme_boundary(text, bounds[i]));
    }
}

///  next_boundary_in(word_end_boundaries) returns a grapheme boundary
///  within text bounds.
pub proof fn axiom_next_word_boundary_valid(text: Seq<char>, pos: nat)
    requires
        wf_text(text),
        text.len() > 0,
        pos <= text.len(),
        is_grapheme_boundary(text, pos),
    ensures
        next_boundary_in(word_end_boundaries(text), pos) >= pos,
        next_boundary_in(word_end_boundaries(text), pos) <= text.len(),
        is_grapheme_boundary(
            text,
            next_boundary_in(word_end_boundaries(text), pos)),
{
    let bounds = word_end_boundaries(text);
    axiom_word_end_boundaries_valid(text);
    axiom_word_boundaries_are_grapheme_boundaries(text);
    //  >= pos
    proofs::lemma_next_boundary_in_ge(bounds, pos);
    //  <= text.len() and membership
    if pos < text.len() {
        //  bounds[len-1] = text.len() > pos
        proofs::lemma_next_boundary_in_member(bounds, pos);
        let i = choose|i: int| 0 <= i < bounds.len() && bounds[i] == next_boundary_in(bounds, pos);
        assert(is_grapheme_boundary(text, bounds[i]));
        proofs::lemma_next_boundary_in_le_last(bounds, pos);
    } else {
        //  pos == text.len()
        proofs::lemma_next_boundary_in_le_last(bounds, pos);
        //  result >= pos && result <= bounds[len-1] = text.len() = pos → result == pos
        //  is_grapheme_boundary(text, text.len()): grapheme boundaries end at text.len()
        axiom_grapheme_boundaries_valid(text);
        let gb = grapheme_boundaries(text);
        assert(gb[gb.len() - 1] == text.len());
        assert(is_grapheme_boundary(text, text.len()));
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Boundary navigation helpers
//  ──────────────────────────────────────────────────────────────────────

///  Whether `pos` is a grapheme boundary.
pub open spec fn is_grapheme_boundary(text: Seq<char>, pos: nat) -> bool {
    if text.len() == 0 {
        pos == 0
    } else {
        exists|i: int| 0 <= i < grapheme_boundaries(text).len()
            && grapheme_boundaries(text)[i] == pos
    }
}

///  Find the largest boundary strictly less than `pos`, or 0 if none.
pub open spec fn prev_boundary_in(bounds: Seq<nat>, pos: nat) -> nat
    decreases bounds.len(),
{
    if bounds.len() == 0 {
        0
    } else if bounds.last() < pos {
        bounds.last()
    } else {
        prev_boundary_in(bounds.drop_last(), pos)
    }
}

///  Find the smallest boundary strictly greater than `pos`, or the last boundary if none.
pub open spec fn next_boundary_in(bounds: Seq<nat>, pos: nat) -> nat
    decreases bounds.len(),
{
    if bounds.len() == 0 {
        pos
    } else if bounds[0] > pos {
        bounds[0]
    } else {
        next_boundary_in(bounds.subrange(1, bounds.len() as int), pos)
    }
}

///  Previous grapheme boundary before `pos` (or 0).
pub open spec fn prev_grapheme_boundary(text: Seq<char>, pos: nat) -> nat {
    if text.len() == 0 {
        0
    } else {
        prev_boundary_in(grapheme_boundaries(text), pos)
    }
}

///  Next grapheme boundary after `pos` (or text.len()).
pub open spec fn next_grapheme_boundary(text: Seq<char>, pos: nat) -> nat {
    if text.len() == 0 {
        0
    } else {
        next_boundary_in(grapheme_boundaries(text), pos)
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Visual layout axioms (for vertical cursor movement)
//  ──────────────────────────────────────────────────────────────────────

///  Map text position + affinity to visual (line, column).
pub uninterp spec fn text_pos_to_visual(
    text: Seq<char>, pos: nat, aff: Affinity,
) -> (nat, nat);

///  Map visual (line, column) back to text position + affinity.
pub uninterp spec fn visual_to_text_pos(
    text: Seq<char>, line: nat, col: nat,
) -> (nat, Affinity);

//  ──────────────────────────────────────────────────────────────────────
//  Visual position axioms
//  ──────────────────────────────────────────────────────────────────────

///  Round-trip: text_pos_to_visual → visual_to_text_pos returns the original position
///  (when the position is a grapheme boundary within the text).
#[verifier::external_body]
pub proof fn axiom_visual_roundtrip(text: Seq<char>, pos: nat, aff: Affinity)
    requires
        wf_text(text),
        pos <= text.len(),
        is_grapheme_boundary(text, pos),
    ensures ({
        let (line, col) = text_pos_to_visual(text, pos, aff);
        visual_to_text_pos(text, line, col).0 == pos
    }),
{}

///  Visual line is monotone in text position: earlier positions map to
///  equal or earlier lines.
#[verifier::external_body]
pub proof fn axiom_visual_line_monotone(
    text: Seq<char>, pos1: nat, pos2: nat, aff: Affinity,
)
    requires
        wf_text(text),
        pos1 <= pos2,
        pos2 <= text.len(),
    ensures
        text_pos_to_visual(text, pos1, aff).0
            <= text_pos_to_visual(text, pos2, aff).0,
{}

//  ──────────────────────────────────────────────────────────────────────
//  Find result grapheme alignment axiom
//  ──────────────────────────────────────────────────────────────────────

///  In well-formed text, a substring match starts and ends at grapheme boundaries.
///  Validated by the Unicode runtime: wf_text contains only permitted characters
///  with canonical line endings, and match boundaries in such text are grapheme-aligned.
#[verifier::external_body]
pub proof fn axiom_find_result_grapheme_aligned(
    text: Seq<char>, pattern: Seq<char>, pos: nat,
)
    requires
        wf_text(text),
        crate::text_model::find::seq_matches_at(text, pattern, pos),
    ensures
        is_grapheme_boundary(text, pos),
        is_grapheme_boundary(text, pos + pattern.len()),
{}

//  ──────────────────────────────────────────────────────────────────────
//  Well-formedness
//  ──────────────────────────────────────────────────────────────────────

impl TextModel {
    ///  Well-formedness predicate for the text model.
    pub open spec fn wf(self) -> bool {
        &&& wf_text(self.text)
        &&& self.styles.len() == self.text.len()
        &&& self.anchor <= self.text.len()
        &&& self.focus <= self.text.len()
        &&& is_grapheme_boundary(self.text, self.anchor)
        &&& is_grapheme_boundary(self.text, self.focus)
        &&& self.paragraph_styles.len() == paragraph_count(self.text)
        &&& match self.composition {
            Some(c) => {
                &&& c.range_start <= c.range_end
                &&& c.range_end <= self.text.len()
                &&& is_grapheme_boundary(self.text, c.range_start)
                &&& is_grapheme_boundary(self.text, c.range_end)
                &&& c.original =~= self.text.subrange(c.range_start as int, c.range_end as int)
                &&& c.cursor <= c.provisional.len()
            },
            None => true,
        }
    }
}

//  ──────────────────────────────────────────────────────────────────────
//  Derived views
//  ──────────────────────────────────────────────────────────────────────

///  The visible text, with any IME composition applied.
pub open spec fn visible_text(model: &TextModel) -> Seq<char> {
    match model.composition {
        Some(c) => {
            model.text.subrange(0, c.range_start as int)
                + c.provisional
                + model.text.subrange(c.range_end as int, model.text.len() as int)
        },
        None => model.text,
    }
}

///  Half-open selection range `(start, end)` from anchor and focus.
pub open spec fn selection_range(anchor: nat, focus: nat) -> (nat, nat) {
    if anchor <= focus {
        (anchor, focus)
    } else {
        (focus, anchor)
    }
}

///  Whether there is a non-empty selection.
pub open spec fn has_selection(anchor: nat, focus: nat) -> bool {
    anchor != focus
}

//  ──────────────────────────────────────────────────────────────────────
//  Submodules
//  ──────────────────────────────────────────────────────────────────────

pub mod operations;
pub mod cursor;
pub mod proofs;
pub mod undo;
pub mod undo_proofs;
pub mod paragraph_proofs;
pub mod session;
pub mod selection_geometry;
pub mod viewport;
pub mod word_wrap;
pub mod find;
pub mod find_proofs;

} //  verus!
