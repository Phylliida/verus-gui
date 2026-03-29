use vstd::prelude::*;
use super::*;
use super::cursor::*;

verus! {

//  ──────────────────────────────────────────────────────────────────────
//  Selection rectangles
//  ──────────────────────────────────────────────────────────────────────

///  Sentinel value meaning "to end of line" for end_col.
pub open spec fn LINE_END_SENTINEL() -> nat { 0xFFFF_FFFF }

///  A rectangle covering part of a line in the selection highlight.
pub struct SelectionRect {
    pub line: nat,
    pub start_col: nat,
    pub end_col: nat,
}

///  Compute highlight rectangles for the selection between `anchor` and `focus`.
///  Returns one rect per line the selection spans.
///  Empty selection → empty sequence.
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
            //  Single line selection
            seq![SelectionRect { line: start_line, start_col, end_col }]
        } else {
            //  Multi-line: first partial + full middle lines + last partial
            selection_rects_multiline(
                text, start_line, start_col, end_line, end_col)
        }
    }
}

///  Build rects for a multi-line selection.
///  First line: start_col to end of line (sentinel).
///  Middle lines: full line.
///  Last line: start of line to end_col.
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
        //  Just two lines: first partial + last partial
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
        //  First line + recurse for middle + last
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

///  Number of lines the selection spans.
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

//  ──────────────────────────────────────────────────────────────────────
//  Selection geometry proofs
//  ──────────────────────────────────────────────────────────────────────

///  Empty selection produces empty rects.
pub proof fn lemma_empty_selection_empty_rects(
    text: Seq<char>, pos: nat,
)
    ensures selection_rects(text, pos, pos) === Seq::<SelectionRect>::empty(),
{
}

///  selection_rects_multiline produces end_line - start_line + 1 rects
///  when start_line < end_line.
pub proof fn lemma_multiline_rect_count(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures
        selection_rects_multiline(text, start_line, start_col, end_line, end_col).len()
            == (end_line - start_line) + 1,
    decreases end_line - start_line,
{
    if start_line + 1 == end_line {
        //  Two rects
    } else {
        lemma_multiline_rect_count(text, start_line + 1, 0, end_line, end_col);
        //  1 + (end_line - (start_line+1) + 1) = end_line - start_line + 1
    }
}

///  First rect in multiline selection has the start_line and start_col.
pub proof fn lemma_multiline_first_rect(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures ({
        let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
        rects.len() > 0
        && rects[0].line == start_line
        && rects[0].start_col == start_col
        && rects[0].end_col == LINE_END_SENTINEL()
    }),
    decreases end_line - start_line,
{
    if start_line + 1 == end_line {
        //  Directly two rects, first is start_line
    } else {
        //  First element is seq![...start_line...], rest is recursive
    }
}

///  Last rect in multiline selection has the end_line and end_col.
pub proof fn lemma_multiline_last_rect(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures ({
        let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
        rects.len() > 0
        && rects[rects.len() - 1].line == end_line
        && rects[rects.len() - 1].start_col == 0
        && rects[rects.len() - 1].end_col == end_col
    }),
    decreases end_line - start_line,
{
    if start_line + 1 == end_line {
        //  Two rects, last is end_line
    } else {
        lemma_multiline_last_rect(text, start_line + 1, 0, end_line, end_col);
        lemma_multiline_rect_count(text, start_line + 1, 0, end_line, end_col);
        let rest = selection_rects_multiline(text, start_line + 1, 0, end_line, end_col);
        let full = seq![SelectionRect {
            line: start_line, start_col,
            end_col: LINE_END_SENTINEL(),
        }].add(rest);
        //  full.last() == rest.last()
        assert(full[full.len() - 1] == rest[rest.len() - 1]);
    }
}

///  All rects in multiline selection have lines in [start_line, end_line].
pub proof fn lemma_multiline_lines_in_range(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures ({
        let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
        forall|i: int| 0 <= i < rects.len()
            ==> #[trigger] rects[i].line >= start_line
                && rects[i].line <= end_line
    }),
    decreases end_line - start_line,
{
    let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
    if start_line + 1 == end_line {
        assert forall|i: int| 0 <= i < rects.len() implies
            #[trigger] rects[i].line >= start_line && rects[i].line <= end_line
        by {
            if i == 0 {} else {}
        };
    } else {
        lemma_multiline_lines_in_range(text, start_line + 1, 0, end_line, end_col);
        let rest = selection_rects_multiline(text, start_line + 1, 0, end_line, end_col);
        assert forall|i: int| 0 <= i < rects.len() implies
            #[trigger] rects[i].line >= start_line && rects[i].line <= end_line
        by {
            if i == 0 {
            } else {
                assert(rects[i] == rest[i - 1]);
                assert(rest[i - 1].line >= start_line + 1);
            }
        };
    }
}

///  Lines in multiline selection rects are monotonically non-decreasing.
pub proof fn lemma_multiline_lines_monotone(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures
        forall|i: int, j: int|
            0 <= i <= j && j < selection_rects_multiline(
                text, start_line, start_col, end_line, end_col).len()
            ==> selection_rects_multiline(
                    text, start_line, start_col, end_line, end_col)[i].line
                <= selection_rects_multiline(
                    text, start_line, start_col, end_line, end_col)[j].line,
    decreases end_line - start_line,
{
    let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
    if start_line + 1 == end_line {
        //  Two rects: start_line <= end_line
    } else {
        lemma_multiline_lines_monotone(text, start_line + 1, 0, end_line, end_col);
        lemma_multiline_lines_in_range(text, start_line + 1, 0, end_line, end_col);
        let rest = selection_rects_multiline(text, start_line + 1, 0, end_line, end_col);
        assert forall|i: int, j: int|
            0 <= i <= j && j < rects.len()
        implies rects[i].line <= rects[j].line
        by {
            if i == 0 {
                if j == 0 {
                } else {
                    //  rects[0].line == start_line, rects[j].line >= start_line + 1
                    assert(rest[j - 1].line >= start_line + 1);
                }
            } else {
                //  Both in rest
                assert(rects[i] == rest[i - 1]);
                assert(rects[j] == rest[j - 1]);
            }
        };
    }
}

///  selection_line_count matches actual rect count for single-line selections.
pub proof fn lemma_selection_line_count_single(
    text: Seq<char>, anchor: nat, focus: nat,
)
    requires
        anchor != focus,
        ({
            let (sel_start, sel_end) = selection_range(anchor, focus);
            let (start_line, _) = text_pos_to_visual(text, sel_start, Affinity::Downstream);
            let (end_line, _) = text_pos_to_visual(text, sel_end, Affinity::Upstream);
            start_line == end_line
        }),
    ensures
        selection_line_count(text, anchor, focus) == 1,
{
    let (sel_start, sel_end) = selection_range(anchor, focus);
    let (start_line, _) = text_pos_to_visual(text, sel_start, Affinity::Downstream);
    let (end_line, _) = text_pos_to_visual(text, sel_end, Affinity::Upstream);
    //  end_line == start_line → (end_line - start_line) + 1 = 1
}

///  Each rect in a multiline selection covers a distinct line:
///  rect[i].line == start_line + i.
pub proof fn lemma_multiline_rect_line_identity(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures ({
        let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
        forall|i: int| 0 <= i < rects.len()
            ==> #[trigger] rects[i].line == (start_line + i) as nat
    }),
    decreases end_line - start_line,
{
    let rects = selection_rects_multiline(text, start_line, start_col, end_line, end_col);
    if start_line + 1 == end_line {
        assert forall|i: int| 0 <= i < rects.len()
        implies #[trigger] rects[i].line == (start_line + i) as nat
        by {
            if i == 0 {} else {}
        };
    } else {
        lemma_multiline_rect_line_identity(text, start_line + 1, 0, end_line, end_col);
        let rest = selection_rects_multiline(text, start_line + 1, 0, end_line, end_col);
        assert forall|i: int| 0 <= i < rects.len()
        implies #[trigger] rects[i].line == (start_line + i) as nat
        by {
            if i == 0 {
            } else {
                assert(rects[i] == rest[i - 1]);
                assert(rest[i - 1].line == (start_line + 1 + (i - 1)) as nat);
            }
        };
    }
}

///  Strict monotonicity: consecutive rects have strictly increasing line numbers.
pub proof fn lemma_multiline_lines_strictly_increasing(
    text: Seq<char>,
    start_line: nat, start_col: nat,
    end_line: nat, end_col: nat,
)
    requires start_line < end_line,
    ensures
        forall|i: int, j: int|
            0 <= i < j && j < selection_rects_multiline(
                text, start_line, start_col, end_line, end_col).len()
            ==> selection_rects_multiline(
                    text, start_line, start_col, end_line, end_col)[i].line
                < selection_rects_multiline(
                    text, start_line, start_col, end_line, end_col)[j].line,
{
    lemma_multiline_rect_line_identity(text, start_line, start_col, end_line, end_col);
    //  rect[i].line = start_line + i < start_line + j = rect[j].line when i < j
}

} //  verus!
