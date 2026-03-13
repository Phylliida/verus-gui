use vstd::prelude::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Enums
// ──────────────────────────────────────────────────────────────────────

/// Cursor affinity: which side of a line break the cursor is drawn on.
pub enum Affinity {
    Upstream,
    Downstream,
}

/// Paragraph alignment.
pub enum ParagraphAlignment {
    Left,
    Center,
    Right,
    Justify,
}

// ──────────────────────────────────────────────────────────────────────
// Style types
// ──────────────────────────────────────────────────────────────────────

/// Rich-text style set. Each field is optional; `None` means "inherit from parent/default".
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

/// Per-paragraph formatting.
pub struct ParagraphStyle {
    pub alignment: ParagraphAlignment,
    pub indent_left: nat,
    pub indent_right: nat,
    pub indent_first_line: int,
    pub line_spacing: nat,
    pub space_before: nat,
    pub space_after: nat,
}

// ──────────────────────────────────────────────────────────────────────
// IME Composition
// ──────────────────────────────────────────────────────────────────────

/// Active IME composition state.
pub struct Composition {
    pub range_start: nat,
    pub range_end: nat,
    pub original: Seq<char>,
    pub provisional: Seq<char>,
    pub cursor: nat,
}

// ──────────────────────────────────────────────────────────────────────
// Text model
// ──────────────────────────────────────────────────────────────────────

/// The core text editing model. Manages text content, styles, cursor,
/// selection, IME composition, and paragraph formatting.
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

// ──────────────────────────────────────────────────────────────────────
// Seq helpers
// ──────────────────────────────────────────────────────────────────────

/// Splice a sequence: replace `s[start..end)` with `replacement`.
pub open spec fn seq_splice<A>(s: Seq<A>, start: int, end: int, replacement: Seq<A>) -> Seq<A> {
    s.subrange(0, start) + replacement + s.subrange(end, s.len() as int)
}

/// Create a sequence of `count` copies of `val`.
pub open spec fn seq_repeat<A>(val: A, count: nat) -> Seq<A>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        seq_repeat(val, (count - 1) as nat).push(val)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Character / paragraph counting
// ──────────────────────────────────────────────────────────────────────

/// Whether a character is permitted in the text model.
/// Excludes null and interlinear annotation characters.
pub open spec fn is_permitted(c: char) -> bool {
    c != '\0'
    && c != '\u{FFF9}' // interlinear annotation anchor
    && c != '\u{FFFA}' // interlinear annotation separator
    && c != '\u{FFFB}' // interlinear annotation terminator
}

/// Whether the text contains only permitted characters and uses canonical line endings.
/// Canonical: only '\n' for newlines (no bare '\r' or '\r\n').
pub open spec fn wf_text(text: Seq<char>) -> bool {
    &&& forall|i: int| 0 <= i < text.len() ==> is_permitted(#[trigger] text[i])
    &&& forall|i: int| 0 <= i < text.len() ==> text[i] != '\r'
}

/// Count occurrences of character `c` in `text`.
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

/// Number of paragraphs (lines). A trailing '\n' yields an extra empty paragraph.
/// Empty string → 1 paragraph.
pub open spec fn paragraph_count(text: Seq<char>) -> nat {
    count_char(text, '\n') + 1
}

// ──────────────────────────────────────────────────────────────────────
// Unicode boundary axioms
// ──────────────────────────────────────────────────────────────────────

/// Whether `bounds` is a valid set of boundaries for text of the given length.
/// Boundaries are strictly increasing, start at 0, and end at text.len().
pub open spec fn valid_boundaries(text: Seq<char>, bounds: Seq<nat>) -> bool {
    &&& bounds.len() >= 2
    &&& bounds[0] == 0
    &&& bounds[bounds.len() - 1] == text.len()
    &&& forall|i: int| 0 <= i < bounds.len() - 1 ==> (#[trigger] bounds[i]) < bounds[i + 1]
}

/// Grapheme cluster boundaries (UAX #29). Axiomatized.
pub uninterp spec fn grapheme_boundaries(text: Seq<char>) -> Seq<nat>;

/// Word start boundaries (UAX #29). Axiomatized.
pub uninterp spec fn word_start_boundaries(text: Seq<char>) -> Seq<nat>;

/// Word end boundaries (UAX #29). Axiomatized.
pub uninterp spec fn word_end_boundaries(text: Seq<char>) -> Seq<nat>;

/// Line break opportunities (UAX #14). Axiomatized.
pub uninterp spec fn line_break_opportunities(text: Seq<char>) -> Seq<nat>;

// Axiom proof functions: assert validity of each boundary set.

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

// ──────────────────────────────────────────────────────────────────────
// Boundary navigation helpers
// ──────────────────────────────────────────────────────────────────────

/// Whether `pos` is a grapheme boundary.
pub open spec fn is_grapheme_boundary(text: Seq<char>, pos: nat) -> bool {
    if text.len() == 0 {
        pos == 0
    } else {
        exists|i: int| 0 <= i < grapheme_boundaries(text).len()
            && grapheme_boundaries(text)[i] == pos
    }
}

/// Find the largest boundary strictly less than `pos`, or 0 if none.
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

/// Find the smallest boundary strictly greater than `pos`, or the last boundary if none.
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

/// Previous grapheme boundary before `pos` (or 0).
pub open spec fn prev_grapheme_boundary(text: Seq<char>, pos: nat) -> nat {
    if text.len() == 0 {
        0
    } else {
        prev_boundary_in(grapheme_boundaries(text), pos)
    }
}

/// Next grapheme boundary after `pos` (or text.len()).
pub open spec fn next_grapheme_boundary(text: Seq<char>, pos: nat) -> nat {
    if text.len() == 0 {
        0
    } else {
        next_boundary_in(grapheme_boundaries(text), pos)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Visual layout axioms (for vertical cursor movement)
// ──────────────────────────────────────────────────────────────────────

/// Map text position + affinity to visual (line, column).
pub uninterp spec fn text_pos_to_visual(
    text: Seq<char>, pos: nat, aff: Affinity,
) -> (nat, nat);

/// Map visual (line, column) back to text position + affinity.
pub uninterp spec fn visual_to_text_pos(
    text: Seq<char>, line: nat, col: nat,
) -> (nat, Affinity);

// ──────────────────────────────────────────────────────────────────────
// Well-formedness
// ──────────────────────────────────────────────────────────────────────

impl TextModel {
    /// Well-formedness predicate for the text model.
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

// ──────────────────────────────────────────────────────────────────────
// Derived views
// ──────────────────────────────────────────────────────────────────────

/// The visible text, with any IME composition applied.
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

/// Half-open selection range `(start, end)` from anchor and focus.
pub open spec fn selection_range(anchor: nat, focus: nat) -> (nat, nat) {
    if anchor <= focus {
        (anchor, focus)
    } else {
        (focus, anchor)
    }
}

/// Whether there is a non-empty selection.
pub open spec fn has_selection(anchor: nat, focus: nat) -> bool {
    anchor != focus
}

// ──────────────────────────────────────────────────────────────────────
// Submodules
// ──────────────────────────────────────────────────────────────────────

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

} // verus!
