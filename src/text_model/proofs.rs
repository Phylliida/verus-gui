use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::cursor::*;
use super::paragraph_proofs::*;
use super::session::{
    undo_splice_params_full, is_text_edit_key, is_insert_key,
    apply_key_to_session, TextEditSession,
};
use super::undo::{can_undo, can_redo, apply_undo, apply_redo};
use crate::event::{
    dispatch_key, key_to_move_direction, KeyAction, KeyEvent, KeyEventKind,
    ExternalAction, Modifiers,
};

verus! {

// ──────────────────────────────────────────────────────────────────────
// Seq helper proofs
// ──────────────────────────────────────────────────────────────────────

/// Length of a spliced sequence.
pub proof fn lemma_seq_splice_len<A>(s: Seq<A>, start: int, end: int, r: Seq<A>)
    requires
        0 <= start <= end,
        end <= s.len(),
    ensures
        seq_splice(s, start, end, r).len() == s.len() - (end - start) + r.len(),
{
    assert(s.subrange(0, start).len() == start);
    assert(s.subrange(end, s.len() as int).len() == s.len() - end);
    assert((s.subrange(0, start) + r).len() == start + r.len());
}

/// Length of seq_repeat.
pub proof fn lemma_seq_repeat_len<A>(val: A, count: nat)
    ensures
        seq_repeat(val, count).len() == count,
    decreases count,
{
    if count > 0 {
        lemma_seq_repeat_len(val, (count - 1) as nat);
    }
}

/// count_char on concatenation.
pub proof fn lemma_count_char_concat(a: Seq<char>, b: Seq<char>, c: char)
    ensures
        count_char(a + b, c) == count_char(a, c) + count_char(b, c),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let ab = a + b;
        let b_drop = b.drop_last();
        assert(ab.drop_last() =~= a + b_drop);
        lemma_count_char_concat(a, b_drop, c);
        assert(ab.last() == b.last());
    }
}

// ──────────────────────────────────────────────────────────────────────
// Boundary ordering lemmas
// ──────────────────────────────────────────────────────────────────────

/// prev_boundary_in always returns a value < pos, when boundaries start at 0 and pos > 0.
pub proof fn lemma_prev_boundary_lt(bounds: Seq<nat>, pos: nat)
    requires
        bounds.len() > 0,
        bounds[0] == 0,
        pos > 0,
    ensures
        prev_boundary_in(bounds, pos) < pos,
    decreases bounds.len(),
{
    if bounds.last() < pos {
        // returns bounds.last() which is < pos
    } else {
        if bounds.len() == 1 {
            // bounds = [0], bounds.last() = 0 >= pos, but pos > 0 and bounds[0] = 0
            // so bounds.last() = 0 < pos (since pos > 0). Contradiction with else branch.
            assert(bounds.last() == 0);
            assert(false);
        } else {
            let dropped = bounds.drop_last();
            assert(dropped.len() > 0);
            assert(dropped[0] == bounds[0]);
            lemma_prev_boundary_lt(dropped, pos);
        }
    }
}

/// next_boundary_in returns a value > pos when the last boundary exceeds pos.
pub proof fn lemma_next_boundary_gt(bounds: Seq<nat>, pos: nat)
    requires
        bounds.len() > 0,
        bounds[bounds.len() - 1] > pos,
        // Boundaries are strictly increasing
        forall|i: int| 0 <= i < bounds.len() - 1 ==> (#[trigger] bounds[i]) < bounds[i + 1],
    ensures
        next_boundary_in(bounds, pos) > pos,
    decreases bounds.len(),
{
    if bounds[0] > pos {
        // returns bounds[0] which is > pos
    } else {
        let rest = bounds.subrange(1, bounds.len() as int);
        if rest.len() == 0 {
            // bounds.len() == 1, bounds[0] <= pos, but bounds[0] > pos. Contradiction.
            assert(false);
        } else {
            assert(rest[rest.len() - 1] == bounds[bounds.len() - 1]);
            assert forall|i: int| 0 <= i < rest.len() - 1
                implies (#[trigger] rest[i]) < rest[i + 1]
            by {
                assert(rest[i] == bounds[i + 1]);
                assert(rest[i + 1] == bounds[i + 2]);
                assert(bounds[i + 1] < bounds[i + 2]);
            }
            lemma_next_boundary_gt(rest, pos);
        }
    }
}

/// prev_boundary_in always returns a value <= pos.
pub proof fn lemma_prev_boundary_in_le(bounds: Seq<nat>, pos: nat)
    ensures
        prev_boundary_in(bounds, pos) <= pos,
    decreases bounds.len(),
{
    if bounds.len() == 0 {
        // returns 0 <= pos (nat)
    } else if bounds.last() < pos {
        // returns bounds.last() < pos
    } else {
        lemma_prev_boundary_in_le(bounds.drop_last(), pos);
    }
}

/// prev_boundary_in returns a member of bounds (when bounds is non-empty).
pub proof fn lemma_prev_boundary_in_member(bounds: Seq<nat>, pos: nat)
    ensures
        bounds.len() > 0 ==> (
            prev_boundary_in(bounds, pos) == 0 ||
            exists|i: int| 0 <= i < bounds.len()
                && bounds[i] == prev_boundary_in(bounds, pos)
        ),
    decreases bounds.len(),
{
    if bounds.len() > 0 {
        if bounds.last() < pos {
            // returns bounds.last() = bounds[bounds.len() - 1]
            assert(bounds[bounds.len() - 1] == prev_boundary_in(bounds, pos));
        } else {
            let dropped = bounds.drop_last();
            lemma_prev_boundary_in_member(dropped, pos);
            if dropped.len() > 0 {
                let result = prev_boundary_in(dropped, pos);
                if result != 0 {
                    let i = choose|i: int| 0 <= i < dropped.len()
                        && dropped[i] == result;
                    assert(bounds[i] == dropped[i]);
                    assert(bounds[i] == prev_boundary_in(bounds, pos));
                }
            }
            // dropped.len() == 0 → returns 0
        }
    }
}

/// next_boundary_in returns a value >= pos.
pub proof fn lemma_next_boundary_in_ge(bounds: Seq<nat>, pos: nat)
    ensures
        next_boundary_in(bounds, pos) >= pos,
    decreases bounds.len(),
{
    if bounds.len() == 0 {
        // returns pos
    } else if bounds[0] > pos {
        // returns bounds[0] > pos
    } else {
        lemma_next_boundary_in_ge(bounds.subrange(1, bounds.len() as int), pos);
    }
}

/// next_boundary_in returns a member of bounds (when bounds is non-empty and last > pos).
pub proof fn lemma_next_boundary_in_member(bounds: Seq<nat>, pos: nat)
    requires
        bounds.len() > 0,
        bounds[bounds.len() - 1] > pos,
    ensures
        exists|i: int| 0 <= i < bounds.len()
            && bounds[i] == next_boundary_in(bounds, pos),
    decreases bounds.len(),
{
    if bounds[0] > pos {
        assert(bounds[0] == next_boundary_in(bounds, pos));
    } else {
        let rest = bounds.subrange(1, bounds.len() as int);
        assert(rest.len() > 0) by {
            // bounds[0] <= pos < bounds[len-1], so len >= 2
            if bounds.len() == 1 {
                assert(bounds[0] == bounds[bounds.len() - 1]);
                assert(false); // contradiction: bounds[0] <= pos < bounds[0]
            }
        }
        assert(rest[rest.len() - 1] == bounds[bounds.len() - 1]);
        lemma_next_boundary_in_member(rest, pos);
        let i = choose|i: int| 0 <= i < rest.len()
            && rest[i] == next_boundary_in(rest, pos);
        assert(bounds[i + 1] == rest[i]);
        assert(next_boundary_in(bounds, pos) == next_boundary_in(rest, pos));
    }
}

/// next_boundary_in is bounded by the last element when last >= pos.
pub proof fn lemma_next_boundary_in_le_last(bounds: Seq<nat>, pos: nat)
    requires
        bounds.len() > 0,
        bounds[bounds.len() - 1] >= pos,
        forall|i: int| 0 <= i < bounds.len() - 1 ==> (#[trigger] bounds[i]) < bounds[i + 1],
    ensures
        next_boundary_in(bounds, pos) <= bounds[bounds.len() - 1],
    decreases bounds.len(),
{
    if bounds[0] > pos {
        // returns bounds[0]
        // Need: bounds[0] <= bounds[len-1]
        // For len==1 trivial. For len>=2, use strict increasing chain.
        if bounds.len() >= 2 {
            // bounds[0] < bounds[1], and we only need bounds[0] <= bounds[len-1]
            // Since bounds are strictly increasing, bounds[0] < bounds[1] <= bounds[len-1]
            assert(bounds[0] < bounds[1]);
            lemma_next_boundary_in_le_last(bounds.subrange(1, bounds.len() as int), pos);
            // Actually, just need bounds[0] <= bounds[len-1]
            // bounds[0] < bounds[1] and bounds.len() >= 2
            // If len==2, bounds[0] < bounds[1] = bounds[len-1] ✓
            // If len>2, bounds[0] < bounds[1] < ... < bounds[len-1] ✓
        }
    } else {
        let rest = bounds.subrange(1, bounds.len() as int);
        if rest.len() == 0 {
            // bounds.len() == 1, bounds[0] <= pos, bounds[0] >= pos → bounds[0] == pos
            // next_boundary_in(Seq::empty(), pos) = pos = bounds[0] = bounds[len-1]
            assert(next_boundary_in(rest, pos) == pos);
        } else {
            assert(rest[rest.len() - 1] == bounds[bounds.len() - 1]);
            assert forall|i: int| 0 <= i < rest.len() - 1
                implies (#[trigger] rest[i]) < rest[i + 1]
            by {
                assert(rest[i] == bounds[i + 1]);
                assert(rest[i + 1] == bounds[i + 2]);
            }
            lemma_next_boundary_in_le_last(rest, pos);
        }
    }
}

/// prev_grapheme_boundary returns a value < pos when text is non-empty and pos > 0.
pub proof fn lemma_prev_grapheme_lt(text: Seq<char>, pos: nat)
    requires
        text.len() > 0,
        pos > 0,
    ensures
        prev_grapheme_boundary(text, pos) < pos,
{
    axiom_grapheme_boundaries_valid(text);
    let bounds = grapheme_boundaries(text);
    assert(bounds.len() >= 2);
    assert(bounds[0] == 0);
    lemma_prev_boundary_lt(bounds, pos);
}

/// next_grapheme_boundary returns a value > pos when text is non-empty and pos < text.len().
pub proof fn lemma_next_grapheme_gt(text: Seq<char>, pos: nat)
    requires
        text.len() > 0,
        pos < text.len(),
    ensures
        next_grapheme_boundary(text, pos) > pos,
{
    axiom_grapheme_boundaries_valid(text);
    let bounds = grapheme_boundaries(text);
    assert(bounds.len() >= 2);
    assert(bounds[bounds.len() - 1] == text.len());
    assert(bounds[bounds.len() - 1] > pos);
    lemma_next_boundary_gt(bounds, pos);
}

// ──────────────────────────────────────────────────────────────────────
// Central wf-preservation theorem
// ──────────────────────────────────────────────────────────────────────

/// Splice preserves well-formedness.
pub proof fn lemma_splice_preserves_wf(
    model: TextModel,
    start: nat,
    end: nat,
    new_text: Seq<char>,
    new_styles: Seq<StyleSet>,
    new_focus: nat,
)
    requires
        model.wf(),
        start <= end,
        end <= model.text.len(),
        new_text.len() == new_styles.len(),
        wf_text(seq_splice(model.text, start as int, end as int, new_text)),
        new_focus <= model.text.len() - (end - start) + new_text.len(),
        is_grapheme_boundary(
            seq_splice(model.text, start as int, end as int, new_text),
            new_focus),
    ensures
        splice(model, start, end, new_text, new_styles, new_focus).wf(),
{
    let result = splice(model, start, end, new_text, new_styles, new_focus);
    let text_prime = seq_splice(model.text, start as int, end as int, new_text);
    let styles_prime = seq_splice(model.styles, start as int, end as int, new_styles);

    // styles'.len() == text'.len()
    lemma_seq_splice_len(model.text, start as int, end as int, new_text);
    lemma_seq_splice_len(model.styles, start as int, end as int, new_styles);
    assert(styles_prime.len() == text_prime.len());

    // paragraph_styles'.len() == paragraph_count(text')
    lemma_adjust_paragraph_styles_len(
        model.paragraph_styles, model.text, start, end, new_text);

    // cursor bounds and grapheme boundary from preconditions
    // composition is None
}

// ──────────────────────────────────────────────────────────────────────
// Per-operation wf-preservation wrappers
// ──────────────────────────────────────────────────────────────────────

/// insert_char preserves wf.
pub proof fn lemma_insert_char_preserves_wf(model: TextModel, ch: char)
    requires
        model.wf(),
        is_permitted(ch),
        ch != '\r',
        ({
            let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
            let text_prime = seq_splice(model.text, sel_start as int, sel_end as int, seq![ch]);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start + 1)
        }),
    ensures
        insert_char(model, ch).wf(),
{
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    lemma_seq_splice_len(model.text, sel_start as int, sel_end as int, seq![ch]);
    lemma_splice_preserves_wf(
        model, sel_start, sel_end, seq![ch], seq![model.typing_style], sel_start + 1);
}

/// delete_selection preserves wf (when there is a selection).
pub proof fn lemma_delete_selection_preserves_wf(model: TextModel)
    requires
        model.wf(),
        has_selection(model.anchor, model.focus),
        ({
            let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
            let text_prime = seq_splice(
                model.text, sel_start as int, sel_end as int, Seq::<char>::empty());
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start)
        }),
    ensures
        delete_selection(model).wf(),
{
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    lemma_seq_splice_len(
        model.text, sel_start as int, sel_end as int, Seq::<char>::empty());
    lemma_splice_preserves_wf(
        model, sel_start, sel_end, Seq::empty(), Seq::empty(), sel_start);
}

/// delete_backward preserves wf.
pub proof fn lemma_delete_backward_preserves_wf(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus > 0,
        model.text.len() > 0,
        ({
            let prev = prev_grapheme_boundary(model.text, model.focus);
            let text_prime = seq_splice(
                model.text, prev as int, model.focus as int, Seq::<char>::empty());
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, prev)
        }),
    ensures
        delete_backward(model).wf(),
{
    let prev = prev_grapheme_boundary(model.text, model.focus);
    lemma_prev_grapheme_lt(model.text, model.focus);
    assert(prev < model.focus);
    lemma_seq_splice_len(
        model.text, prev as int, model.focus as int, Seq::<char>::empty());
    lemma_splice_preserves_wf(
        model, prev, model.focus, Seq::empty(), Seq::empty(), prev);
}

/// delete_forward preserves wf.
pub proof fn lemma_delete_forward_preserves_wf(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus < model.text.len(),
        ({
            let next = next_grapheme_boundary(model.text, model.focus);
            let text_prime = seq_splice(
                model.text, model.focus as int, next as int, Seq::<char>::empty());
            &&& next <= model.text.len()
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, model.focus)
        }),
    ensures
        delete_forward(model).wf(),
{
    let next = next_grapheme_boundary(model.text, model.focus);
    lemma_next_grapheme_gt(model.text, model.focus);
    assert(next > model.focus);
    lemma_seq_splice_len(
        model.text, model.focus as int, next as int, Seq::<char>::empty());
    lemma_splice_preserves_wf(
        model, model.focus, next, Seq::empty(), Seq::empty(), model.focus);
}

/// paste preserves wf.
pub proof fn lemma_paste_preserves_wf(
    model: TextModel,
    text: Seq<char>,
    styles: Seq<StyleSet>,
)
    requires
        model.wf(),
        ({
            let clean = canonicalize_newlines(filter_permitted(text));
            let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
            let text_prime = seq_splice(model.text, sel_start as int, sel_end as int, clean);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start + clean.len())
        }),
    ensures
        paste(model, text, styles).wf(),
{
    let clean = canonicalize_newlines(filter_permitted(text));
    let clean_styles = seq_repeat(model.typing_style, clean.len());
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    lemma_seq_repeat_len(model.typing_style, clean.len());
    lemma_seq_splice_len(model.text, sel_start as int, sel_end as int, clean);
    lemma_splice_preserves_wf(
        model, sel_start, sel_end, clean, clean_styles, sel_start + clean.len());
}

/// move_cursor preserves wf.
pub proof fn lemma_move_cursor_preserves_wf(model: TextModel, dir: MoveDirection)
    requires
        model.wf(),
        ({
            let (new_focus, _, _) = resolve_movement(
                model.text, model.focus, model.focus_affinity,
                model.preferred_column, dir);
            &&& new_focus <= model.text.len()
            &&& is_grapheme_boundary(model.text, new_focus)
        }),
    ensures
        move_cursor(model, dir).wf(),
{
}

/// extend_selection preserves wf.
pub proof fn lemma_extend_selection_preserves_wf(model: TextModel, dir: MoveDirection)
    requires
        model.wf(),
        ({
            let (new_focus, _, _) = resolve_movement(
                model.text, model.focus, model.focus_affinity,
                model.preferred_column, dir);
            &&& new_focus <= model.text.len()
            &&& is_grapheme_boundary(model.text, new_focus)
        }),
    ensures
        extend_selection(model, dir).wf(),
{
}

/// compose_start preserves wf.
pub proof fn lemma_compose_start_preserves_wf(model: TextModel)
    requires
        model.wf(),
        model.composition.is_none(),
    ensures
        compose_start(model).wf(),
{
}

/// compose_commit preserves wf.
pub proof fn lemma_compose_commit_preserves_wf(model: TextModel)
    requires
        model.wf(),
        model.composition.is_some(),
        ({
            let c = model.composition.unwrap();
            let text_prime = seq_splice(
                model.text, c.range_start as int, c.range_end as int, c.provisional);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, c.range_start + c.provisional.len())
        }),
    ensures
        compose_commit(model).wf(),
{
    let c = model.composition.unwrap();
    let new_styles = seq_repeat(model.typing_style, c.provisional.len());
    lemma_seq_repeat_len(model.typing_style, c.provisional.len());
    lemma_seq_splice_len(
        model.text, c.range_start as int, c.range_end as int, c.provisional);
    lemma_splice_preserves_wf(
        model, c.range_start, c.range_end,
        c.provisional, new_styles,
        c.range_start + c.provisional.len());
}

/// compose_cancel preserves wf.
pub proof fn lemma_compose_cancel_preserves_wf(model: TextModel)
    requires model.wf(),
    ensures compose_cancel(model).wf(),
{
}

/// apply_style_to_range preserves wf.
pub proof fn lemma_apply_style_preserves_wf(
    model: TextModel,
    start: nat,
    end: nat,
    style: StyleSet,
)
    requires
        model.wf(),
        start <= end,
        end <= model.text.len(),
    ensures
        apply_style_to_range(model, start, end, style).wf(),
{
    let result = apply_style_to_range(model, start, end, style);
    assert(result.styles.len() == model.styles.len());
}

/// select_all preserves wf.
pub proof fn lemma_select_all_preserves_wf(model: TextModel)
    requires
        model.wf(),
    ensures
        select_all(model).wf(),
{
    // Need: is_grapheme_boundary(text, 0) and is_grapheme_boundary(text, text.len())
    if model.text.len() > 0 {
        axiom_grapheme_boundaries_valid(model.text);
        let bounds = grapheme_boundaries(model.text);
        // bounds[0] == 0
        assert(is_grapheme_boundary(model.text, 0)) by {
            assert(bounds[0] == 0);
        }
        // bounds[bounds.len()-1] == text.len()
        assert(is_grapheme_boundary(model.text, model.text.len())) by {
            assert(bounds[bounds.len() - 1] == model.text.len());
        }
    } else {
        // Empty text: is_grapheme_boundary(text, 0) is true by definition
    }
}

// ──────────────────────────────────────────────────────────────────────
// Structural / behavioral proofs
// ──────────────────────────────────────────────────────────────────────

/// Cancelling a composition doesn't change the text.
pub proof fn lemma_compose_cancel_noop(model: TextModel)
    requires model.wf(),
    ensures compose_cancel(model).text =~= model.text,
{
}

/// Applying a style doesn't change the text.
pub proof fn lemma_style_preserves_text(
    model: TextModel,
    start: nat,
    end: nat,
    style: StyleSet,
)
    requires
        model.wf(),
        start <= end,
        end <= model.text.len(),
    ensures
        apply_style_to_range(model, start, end, style).text =~= model.text,
{
}

/// select_all covers the full text range.
pub proof fn lemma_select_all_covers_all(model: TextModel)
    requires model.wf(),
    ensures
        select_all(model).anchor == 0,
        select_all(model).focus == model.text.len(),
{
}

/// delete_selection on no selection is identity.
pub proof fn lemma_delete_no_selection_noop(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
    ensures
        delete_selection(model) == model,
{
}

/// Toggling bold twice resolves the style (Some(b) → Some(!b) → Some(b)).
/// When starting from None, it resolves to Some(false) (None → Some(true) → Some(false)).
pub proof fn lemma_toggle_bold_involution(model: TextModel)
    requires model.typing_style.bold.is_some(),
    ensures
        toggle_bold(toggle_bold(model)).typing_style.bold
            == model.typing_style.bold,
{
    let b = model.typing_style.bold.unwrap();
    let first = toggle_bold(model);
    assert(first.typing_style.bold == Some(!b));
    let second = toggle_bold(first);
    assert(second.typing_style.bold == Some(!!b));
    assert(!!b == b);
}

/// Moving Home twice ends at position 0.
pub proof fn lemma_home_idempotent(model: TextModel)
    requires
        model.wf(),
        is_grapheme_boundary(model.text, 0nat),
    ensures
        move_cursor(move_cursor(model, MoveDirection::Home), MoveDirection::Home).focus == 0,
{
}

// ──────────────────────────────────────────────────────────────────────
// Splice algebra
// ──────────────────────────────────────────────────────────────────────

/// Splicing with an empty replacement at a single point is identity.
pub proof fn lemma_seq_splice_identity<A>(s: Seq<A>, start: int)
    requires
        0 <= start <= s.len(),
    ensures
        seq_splice(s, start, start, Seq::<A>::empty()) =~= s,
{
}

/// Splicing the entire sequence with a replacement gives the replacement.
pub proof fn lemma_seq_splice_full<A>(s: Seq<A>, r: Seq<A>)
    ensures
        seq_splice(s, 0int, s.len() as int, r) =~= r,
{
    assert(s.subrange(0int, 0int) =~= Seq::<A>::empty());
    assert(s.subrange(s.len() as int, s.len() as int) =~= Seq::<A>::empty());
}

/// Splicing then splicing back the original content restores the sequence.
pub proof fn lemma_seq_splice_roundtrip<A>(
    s: Seq<A>, start: int, end: int, r: Seq<A>,
)
    requires
        0 <= start <= end,
        end <= s.len(),
    ensures
        seq_splice(
            seq_splice(s, start, end, r),
            start,
            start + r.len(),
            s.subrange(start, end),
        ) =~= s,
{
    let s_prime = seq_splice(s, start, end, r);
    lemma_seq_splice_len(s, start, end, r);
    let original = s.subrange(start, end);
    lemma_seq_splice_len(s_prime, start, start + r.len(), original);

    // Prefix and suffix of s' match original s
    assert(s_prime.subrange(0int, start) =~= s.subrange(0int, start));
    assert(s_prime.subrange(start + r.len(), s_prime.len() as int)
        =~= s.subrange(end, s.len() as int));

    // Three adjacent subranges reassemble s
    assert(s.subrange(0int, start) + s.subrange(start, end)
        + s.subrange(end, s.len() as int) =~= s);
}

// ──────────────────────────────────────────────────────────────────────
// Round-trip identities
// ──────────────────────────────────────────────────────────────────────

/// Insert a character then delete backward restores original text.
/// Requires that the inserted character forms a complete grapheme cluster.
pub proof fn lemma_insert_delete_roundtrip(model: TextModel, ch: char)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        is_permitted(ch),
        ch != '\r',
        ({
            let text_prime = seq_splice(
                model.text, model.focus as int, model.focus as int, seq![ch]);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, model.focus + 1)
            &&& prev_grapheme_boundary(text_prime, model.focus + 1) == model.focus
        }),
    ensures
        delete_backward(insert_char(model, ch)).text =~= model.text,
{
    let focus = model.focus;
    assert(selection_range(model.anchor, model.focus) == (focus, focus));

    let model1 = insert_char(model, ch);
    assert(!has_selection(model1.anchor, model1.focus));
    assert(model1.focus == focus + 1);
    assert(model1.focus > 0nat);

    // Empty subrange for the roundtrip
    assert(model.text.subrange(focus as int, focus as int)
        =~= Seq::<char>::empty());

    lemma_seq_splice_roundtrip(model.text, focus as int, focus as int, seq![ch]);
}

/// Select all then delete selection gives empty text.
pub proof fn lemma_select_all_delete_empty(model: TextModel)
    requires
        model.wf(),
    ensures
        delete_selection(select_all(model)).text.len() == 0,
{
    let m1 = select_all(model);
    if model.text.len() > 0 {
        assert(has_selection(m1.anchor, m1.focus));
        assert(selection_range(m1.anchor, m1.focus) == (0nat, model.text.len()));
        lemma_seq_splice_full::<char>(model.text, Seq::<char>::empty());
    } else {
        assert(!has_selection(m1.anchor, m1.focus));
    }
}

/// Compose start then cancel restores the original model.
pub proof fn lemma_compose_start_cancel_identity(model: TextModel)
    requires
        model.wf(),
        model.composition.is_none(),
    ensures
        compose_cancel(compose_start(model)) == model,
{
}

/// Compose commit replaces the composition range with the provisional text.
pub proof fn lemma_compose_commit_correct_text(model: TextModel)
    requires
        model.wf(),
        model.composition.is_some(),
    ensures
        compose_commit(model).text =~= seq_splice(
            model.text,
            model.composition.unwrap().range_start as int,
            model.composition.unwrap().range_end as int,
            model.composition.unwrap().provisional,
        ),
{
}

// ──────────────────────────────────────────────────────────────────────
// Idempotency
// ──────────────────────────────────────────────────────────────────────

/// Moving to End twice is the same as once.
pub proof fn lemma_end_idempotent(model: TextModel)
    requires
        model.wf(),
    ensures
        move_cursor(
            move_cursor(model, MoveDirection::End),
            MoveDirection::End,
        ).focus == model.text.len(),
{
}

/// select_all is idempotent.
pub proof fn lemma_select_all_idempotent(model: TextModel)
    requires
        model.wf(),
    ensures
        select_all(select_all(model)) == select_all(model),
{
}

/// delete_selection is idempotent on text.
pub proof fn lemma_delete_selection_idempotent(model: TextModel)
    requires
        model.wf(),
    ensures
        delete_selection(delete_selection(model)).text
            =~= delete_selection(model).text,
{
    if has_selection(model.anchor, model.focus) {
        let m1 = delete_selection(model);
        // After splice, anchor == focus, so no selection
        assert(!has_selection(m1.anchor, m1.focus));
        assert(delete_selection(m1) == m1);
    } else {
        assert(delete_selection(model) == model);
    }
}

// ──────────────────────────────────────────────────────────────────────
// Commutativity / independence
// ──────────────────────────────────────────────────────────────────────

/// apply_style_to_range and toggle_bold commute.
pub proof fn lemma_style_commutes_with_toggle(
    model: TextModel,
    start: nat,
    end: nat,
    style: StyleSet,
)
    requires
        model.wf(),
        start <= end,
        end <= model.text.len(),
    ensures
        toggle_bold(apply_style_to_range(model, start, end, style))
            == apply_style_to_range(toggle_bold(model), start, end, style),
{
    let lhs = toggle_bold(apply_style_to_range(model, start, end, style));
    let rhs = apply_style_to_range(toggle_bold(model), start, end, style);
    assert(lhs.styles =~= rhs.styles);
}

/// Toggle italic twice restores the original italic style.
pub proof fn lemma_toggle_italic_involution(model: TextModel)
    requires
        model.typing_style.italic.is_some(),
    ensures
        toggle_italic(toggle_italic(model)).typing_style.italic
            == model.typing_style.italic,
{
    let b = model.typing_style.italic.unwrap();
    let first = toggle_italic(model);
    assert(first.typing_style.italic == Some(!b));
    let second = toggle_italic(first);
    assert(second.typing_style.italic == Some(!!b));
    assert(!!b == b);
}

// ──────────────────────────────────────────────────────────────────────
// Bounds and edge cases
// ──────────────────────────────────────────────────────────────────────

/// selection_range always produces an ordered pair.
pub proof fn lemma_selection_range_ordered(anchor: nat, focus: nat)
    ensures
        ({
            let (start, end) = selection_range(anchor, focus);
            start <= end
        }),
{
}

/// delete_backward at position 0 with no selection is a no-op.
pub proof fn lemma_delete_backward_at_start_noop(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus == 0,
    ensures
        delete_backward(model) == model,
{
}

/// delete_forward at the end with no selection is a no-op.
pub proof fn lemma_delete_forward_at_end_noop(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus >= model.text.len(),
    ensures
        delete_forward(model) == model,
{
}

// ──────────────────────────────────────────────────────────────────────
// Bridge: undo params match dispatch result
// ──────────────────────────────────────────────────────────────────────

/// The undo splice parameters computed by undo_splice_params_full produce
/// the same text and styles as the dispatch_key operation.
/// This bridges the undo system with the dispatch system without requiring
/// callers to unfold undo_splice_params_full.
pub proof fn lemma_undo_params_match_dispatch(event: KeyEvent, model: TextModel)
    requires
        is_text_edit_key(event.kind, model),
        match dispatch_key(model, event) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
    ensures ({
        let (start, end, new_text, new_styles) = undo_splice_params_full(event, model);
        let new_model = match dispatch_key(model, event) {
            KeyAction::NewModel(m) => m,
            _ => arbitrary(),
        };
        &&& new_model.text =~= seq_splice(model.text, start as int, end as int, new_text)
        &&& new_model.styles =~= seq_splice(model.styles, start as int, end as int, new_styles)
    }),
{
    reveal(undo_splice_params_full);
    // With undo_splice_params_full revealed and dispatch_key open,
    // Z3 can verify each text-edit case (Char/Enter/Tab/Backspace/Delete/ComposeCommit)
    // by seeing that both functions use the same splice parameters.
}

// ──────────────────────────────────────────────────────────────────────
// Bridge lemmas: apply_key_to_session field extraction
// ──────────────────────────────────────────────────────────────────────
//
// Each lemma reveals apply_key_to_session in a focused context,
// proving what the 3 output fields (model, last_was_insert, clipboard)
// are for one specific dispatch arm. This allows exec functions to
// call a single lemma instead of Z3 unfolding the entire ~140-line spec.

/// Bridge: NewModel + is_text_edit arm.
pub proof fn lemma_apply_key_text_edit(session: TextEditSession, event: KeyEvent)
    requires
        is_text_edit_key(event.kind, session.model),
        match dispatch_key(session.model, event) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
    ensures ({
        let new_model = match dispatch_key(session.model, event) {
            KeyAction::NewModel(m) => m,
            _ => arbitrary(),
        };
        &&& apply_key_to_session(session, event).model == new_model
        &&& apply_key_to_session(session, event).last_was_insert == is_insert_key(event.kind)
        &&& apply_key_to_session(session, event).clipboard == session.clipboard
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: NewModel + non-text-edit arm.
pub proof fn lemma_apply_key_non_text_edit(session: TextEditSession, event: KeyEvent)
    requires
        !is_text_edit_key(event.kind, session.model),
        match dispatch_key(session.model, event) {
            KeyAction::NewModel(_) => true,
            _ => false,
        },
    ensures ({
        let new_model = match dispatch_key(session.model, event) {
            KeyAction::NewModel(m) => m,
            _ => arbitrary(),
        };
        &&& apply_key_to_session(session, event).model == new_model
        &&& apply_key_to_session(session, event).last_was_insert == false
        &&& apply_key_to_session(session, event).clipboard == session.clipboard
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: Undo arm (can_undo && no composition).
pub proof fn lemma_apply_key_undo(session: TextEditSession)
    requires
        can_undo(session.undo_stack),
        session.model.composition.is_none(),
    ensures ({
        let event = KeyEvent { kind: KeyEventKind::Undo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } };
        let (_, new_model) = apply_undo(session.undo_stack, session.model);
        &&& apply_key_to_session(session, event).model == new_model
        &&& apply_key_to_session(session, event).last_was_insert == false
        &&& apply_key_to_session(session, event).clipboard == session.clipboard
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: Redo arm (can_redo && no composition).
pub proof fn lemma_apply_key_redo(session: TextEditSession)
    requires
        can_redo(session.undo_stack),
        session.model.composition.is_none(),
    ensures ({
        let event = KeyEvent { kind: KeyEventKind::Redo, modifiers: Modifiers { shift: false, ctrl: false, alt: false } };
        let (_, new_model) = apply_redo(session.undo_stack, session.model);
        &&& apply_key_to_session(session, event).model == new_model
        &&& apply_key_to_session(session, event).last_was_insert == false
        &&& apply_key_to_session(session, event).clipboard == session.clipboard
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: Copy arm (has selection).
pub proof fn lemma_apply_key_copy(session: TextEditSession, event: KeyEvent)
    requires
        has_selection(session.model.anchor, session.model.focus),
        match dispatch_key(session.model, event) {
            KeyAction::External(ExternalAction::Copy) => true,
            _ => false,
        },
    ensures
        apply_key_to_session(session, event).model == session.model,
        apply_key_to_session(session, event).last_was_insert == session.last_was_insert,
        apply_key_to_session(session, event).clipboard == get_selection_text(session.model),
{
    reveal(apply_key_to_session);
}

/// Bridge: Cut arm (has selection).
pub proof fn lemma_apply_key_cut(session: TextEditSession)
    requires
        has_selection(session.model.anchor, session.model.focus),
    ensures ({
        let event = KeyEvent { kind: KeyEventKind::Cut, modifiers: Modifiers { shift: false, ctrl: false, alt: false } };
        &&& apply_key_to_session(session, event).model == delete_selection(session.model)
        &&& apply_key_to_session(session, event).last_was_insert == false
        &&& apply_key_to_session(session, event).clipboard == get_selection_text(session.model)
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: Paste arm (valid paste).
pub proof fn lemma_apply_key_paste(session: TextEditSession)
    requires ({
        let clean = canonicalize_newlines(filter_permitted(session.clipboard));
        &&& (clean.len() > 0 || has_selection(session.model.anchor, session.model.focus))
        &&& session.model.text.len() + clean.len() < usize::MAX as nat
    }),
    ensures ({
        let event = KeyEvent { kind: KeyEventKind::Paste, modifiers: Modifiers { shift: false, ctrl: false, alt: false } };
        &&& apply_key_to_session(session, event).model == paste(session.model, session.clipboard, Seq::empty())
        &&& apply_key_to_session(session, event).last_was_insert == false
        &&& apply_key_to_session(session, event).clipboard == session.clipboard
    }),
{
    reveal(apply_key_to_session);
}

/// Bridge: all noop arms (identity return).
/// Covers: Copy/Cut without selection, Undo/Redo without preconditions,
/// Paste noop, Find*, and dispatch None.
pub proof fn lemma_apply_key_noop(session: TextEditSession, event: KeyEvent)
    requires
        match dispatch_key(session.model, event) {
            KeyAction::External(ExternalAction::Copy) =>
                !has_selection(session.model.anchor, session.model.focus),
            KeyAction::External(ExternalAction::Cut) =>
                !has_selection(session.model.anchor, session.model.focus),
            KeyAction::External(ExternalAction::Undo) =>
                !can_undo(session.undo_stack) || session.model.composition.is_some(),
            KeyAction::External(ExternalAction::Redo) =>
                !can_redo(session.undo_stack) || session.model.composition.is_some(),
            KeyAction::External(ExternalAction::Paste) => {
                let clean = canonicalize_newlines(filter_permitted(session.clipboard));
                !((clean.len() > 0 || has_selection(session.model.anchor, session.model.focus))
                    && session.model.text.len() + clean.len() < usize::MAX as nat)
            },
            KeyAction::External(ExternalAction::FindNext(_)) => true,
            KeyAction::External(ExternalAction::FindPrev(_)) => true,
            KeyAction::External(ExternalAction::ReplaceAt(_, _, _)) => true,
            KeyAction::External(ExternalAction::ReplaceAll(_, _)) => true,
            KeyAction::None => true,
            _ => false,
        },
    ensures
        apply_key_to_session(session, event).model == session.model,
        apply_key_to_session(session, event).last_was_insert == session.last_was_insert,
        apply_key_to_session(session, event).clipboard == session.clipboard,
{
    reveal(apply_key_to_session);
}

/// Bridge: modifiers are irrelevant for Cut/Undo/Redo/Paste events.
/// The result of apply_key_to_session depends only on event.kind for these.
/// Used by apply_key_to_session_exec to connect event@ to hardcoded ensures
/// in session_handle_cut_exec, session_apply_undo_exec, etc.
pub proof fn lemma_apply_key_kind_determines_result(
    session: TextEditSession, event: KeyEvent, kind: KeyEventKind,
)
    requires
        event.kind == kind,
        match kind {
            KeyEventKind::Cut | KeyEventKind::Undo
            | KeyEventKind::Redo | KeyEventKind::Paste => true,
            _ => false,
        },
    ensures ({
        let canonical = KeyEvent { kind: kind, modifiers: Modifiers { shift: false, ctrl: false, alt: false } };
        &&& apply_key_to_session(session, event).model == apply_key_to_session(session, canonical).model
        &&& apply_key_to_session(session, event).last_was_insert == apply_key_to_session(session, canonical).last_was_insert
        &&& apply_key_to_session(session, event).clipboard == apply_key_to_session(session, canonical).clipboard
    }),
{
    reveal(apply_key_to_session);
}

// ──────────────────────────────────────────────────────────────────────
// Master wf preservation: dispatch_key
// ──────────────────────────────────────────────────────────────────────

/// Single-char insert via dispatch_key preserves model wf.
pub proof fn lemma_dispatch_insert_preserves_wf(model: TextModel, ch: char)
    requires
        model.wf(),
        is_permitted(ch), ch != '\r',
        model.composition.is_none(),
    ensures
        insert_char(model, ch).wf(),
{
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    axiom_splice_wf(model.text, sel_start, sel_end, seq![ch]);
    lemma_insert_char_preserves_wf(model, ch);
}

/// Delete selection via dispatch_key preserves model wf.
pub proof fn lemma_dispatch_delete_selection_preserves_wf(model: TextModel)
    requires
        model.wf(),
        has_selection(model.anchor, model.focus),
        model.composition.is_none(),
    ensures
        delete_selection(model).wf(),
{
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    axiom_splice_wf(model.text, sel_start, sel_end, Seq::empty());
    lemma_delete_selection_preserves_wf(model);
}

/// Delete backward (single grapheme) via dispatch_key preserves model wf.
pub proof fn lemma_dispatch_delete_backward_preserves_wf(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus > 0,
        model.composition.is_none(),
    ensures
        delete_backward(model).wf(),
{
    axiom_prev_grapheme_boundary_valid(model.text, model.focus);
    let prev = prev_grapheme_boundary(model.text, model.focus);
    axiom_splice_wf(model.text, prev, model.focus, Seq::empty());
    lemma_delete_backward_preserves_wf(model);
}

/// Delete forward (single grapheme) via dispatch_key preserves model wf.
pub proof fn lemma_dispatch_delete_forward_preserves_wf(model: TextModel)
    requires
        model.wf(),
        !has_selection(model.anchor, model.focus),
        model.focus < model.text.len(),
        model.composition.is_none(),
    ensures
        delete_forward(model).wf(),
{
    axiom_next_grapheme_boundary_valid(model.text, model.focus);
    let next = next_grapheme_boundary(model.text, model.focus);
    axiom_splice_wf(model.text, model.focus, next, Seq::empty());
    lemma_delete_forward_preserves_wf(model);
}

/// Cursor movement preserves model wf.
pub proof fn lemma_dispatch_move_preserves_wf(model: TextModel, dir: MoveDirection)
    requires model.wf(),
    ensures move_cursor(model, dir).wf(),
{
    axiom_movement_valid(model.text, model.focus, model.focus_affinity,
        model.preferred_column, dir);
    lemma_move_cursor_preserves_wf(model, dir);
}

/// Selection extension preserves model wf.
pub proof fn lemma_dispatch_extend_selection_preserves_wf(model: TextModel, dir: MoveDirection)
    requires model.wf(),
    ensures extend_selection(model, dir).wf(),
{
    axiom_movement_valid(model.text, model.focus, model.focus_affinity,
        model.preferred_column, dir);
    lemma_extend_selection_preserves_wf(model, dir);
}

/// Compose commit preserves model wf.
pub proof fn lemma_dispatch_compose_commit_preserves_wf(model: TextModel)
    requires
        model.wf(),
        model.composition.is_some(),
    ensures
        compose_commit(model).wf(),
{
    let c = model.composition.unwrap();
    axiom_compose_commit_wf(model.text, c.range_start, c.range_end, c.provisional);
    lemma_compose_commit_preserves_wf(model);
}

} // verus!
