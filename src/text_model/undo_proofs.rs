use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::undo::*;
use super::proofs::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Stack well-formedness
// ──────────────────────────────────────────────────────────────────────

/// An empty stack is well-formed.
pub proof fn lemma_empty_stack_wf()
    ensures
        undo_stack_wf(empty_undo_stack()),
{
}

/// An empty stack cannot undo.
pub proof fn lemma_empty_stack_cannot_undo()
    ensures
        !can_undo(empty_undo_stack()),
{
}

/// An empty stack cannot redo.
pub proof fn lemma_empty_stack_cannot_redo()
    ensures
        !can_redo(empty_undo_stack()),
{
}

/// push_undo preserves well-formedness.
pub proof fn lemma_push_preserves_wf(stack: UndoStack, entry: UndoEntry)
    requires
        undo_stack_wf(stack),
        undo_entry_wf(entry),
    ensures
        undo_stack_wf(push_undo(stack, entry)),
{
    let result = push_undo(stack, entry);
    let truncated = stack.entries.subrange(0, stack.position as int);
    assert forall|i: int| 0 <= i < result.entries.len()
        implies undo_entry_wf(#[trigger] result.entries[i])
    by {
        if i < truncated.len() {
            assert(result.entries[i] == truncated[i]);
            assert(truncated[i] == stack.entries[i]);
        } else {
            assert(result.entries[i] == entry);
        }
    }
}

/// After push_undo, we can undo.
pub proof fn lemma_push_enables_undo(stack: UndoStack, entry: UndoEntry)
    requires
        undo_stack_wf(stack),
    ensures
        can_undo(push_undo(stack, entry)),
{
}

/// push_undo truncates redo entries.
pub proof fn lemma_push_truncates_redo(stack: UndoStack, entry: UndoEntry)
    requires
        undo_stack_wf(stack),
    ensures
        !can_redo(push_undo(stack, entry)),
{
    let result = push_undo(stack, entry);
    let truncated = stack.entries.subrange(0, stack.position as int);
    assert(result.entries.len() == truncated.len() + 1);
    assert(result.position == stack.position + 1);
    assert(result.position == result.entries.len());
}

// ──────────────────────────────────────────────────────────────────────
// Undo/redo position tracking
// ──────────────────────────────────────────────────────────────────────

/// apply_undo preserves stack well-formedness.
pub proof fn lemma_undo_preserves_wf(stack: UndoStack, model: TextModel)
    requires
        undo_stack_wf(stack),
        can_undo(stack),
    ensures
        undo_stack_wf(apply_undo(stack, model).0),
{
    let (new_stack, _) = apply_undo(stack, model);
    assert forall|i: int| 0 <= i < new_stack.entries.len()
        implies undo_entry_wf(#[trigger] new_stack.entries[i])
    by {
        assert(new_stack.entries[i] == stack.entries[i]);
    }
}

/// apply_redo preserves stack well-formedness.
pub proof fn lemma_redo_preserves_wf(stack: UndoStack, model: TextModel)
    requires
        undo_stack_wf(stack),
        can_redo(stack),
    ensures
        undo_stack_wf(apply_redo(stack, model).0),
{
    let (new_stack, _) = apply_redo(stack, model);
    assert forall|i: int| 0 <= i < new_stack.entries.len()
        implies undo_entry_wf(#[trigger] new_stack.entries[i])
    by {
        assert(new_stack.entries[i] == stack.entries[i]);
    }
}

/// After undo, we can redo (the entry we just undid).
pub proof fn lemma_undo_enables_redo(stack: UndoStack, model: TextModel)
    requires
        undo_stack_wf(stack),
        can_undo(stack),
    ensures
        can_redo(apply_undo(stack, model).0),
{
    let (new_stack, _) = apply_undo(stack, model);
    assert(new_stack.position < new_stack.entries.len());
}

/// After redo, we can undo (the entry we just redid).
pub proof fn lemma_redo_enables_undo(stack: UndoStack, model: TextModel)
    requires
        undo_stack_wf(stack),
        can_redo(stack),
    ensures
        can_undo(apply_redo(stack, model).0),
{
}

// ──────────────────────────────────────────────────────────────────────
// Core undo correctness: undo restores original text
// ──────────────────────────────────────────────────────────────────────

/// After an edit (splice), undoing restores the original text.
pub proof fn lemma_undo_restores_text(
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
    ensures
        ({
            let entry = undo_entry_for_splice(
                model, start, end, new_text, new_styles, new_focus);
            let model_after = splice(
                model, start, end, new_text, new_styles, new_focus);
            let stack = push_undo(empty_undo_stack(), entry);
            let (_, model_undone) = apply_undo(stack, model_after);
            model_undone.text =~= model.text
        }),
{
    lemma_seq_splice_roundtrip(
        model.text, start as int, end as int, new_text);
}

// ──────────────────────────────────────────────────────────────────────
// Undo-redo cancel: undo then redo restores edited text
// ──────────────────────────────────────────────────────────────────────

/// After edit → undo → redo, the text matches the edited version.
pub proof fn lemma_undo_redo_cancel(
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
    ensures
        ({
            let entry = undo_entry_for_splice(
                model, start, end, new_text, new_styles, new_focus);
            let model_after = splice(
                model, start, end, new_text, new_styles, new_focus);
            let stack = push_undo(empty_undo_stack(), entry);
            let (stack2, model_undone) = apply_undo(stack, model_after);
            let (_, model_redone) = apply_redo(stack2, model_undone);
            model_redone.text =~= model_after.text
        }),
{
    let entry = undo_entry_for_splice(
        model, start, end, new_text, new_styles, new_focus);
    let model_after = splice(
        model, start, end, new_text, new_styles, new_focus);
    let stack = push_undo(empty_undo_stack(), entry);
    let (stack2, model_undone) = apply_undo(stack, model_after);

    // After undo, model_undone.text =~= model.text (by roundtrip)
    lemma_seq_splice_roundtrip(
        model.text, start as int, end as int, new_text);
    assert(model_undone.text =~= model.text);

    // Redo: splice(model_undone, start, start + removed.len(), inserted, ...)
    // entry.removed_text = model.text[start..end), so removed.len() = end - start
    assert(entry.removed_text.len() == end - start);
    // So start + removed.len() == end
    // redo text = seq_splice(model_undone.text, start, end, new_text)
    //           = seq_splice(model.text, start, end, new_text)
    //           = model_after.text

    // Help Z3 see the subrange length
    assert(model.text.subrange(start as int, end as int).len() == end - start);

    let (_, model_redone) = apply_redo(stack2, model_undone);

    // The redo splice uses start + removed_text.len() as the end,
    // which equals start + (end - start) = end
    lemma_seq_splice_roundtrip(
        model_undone.text,
        start as int,
        (start + entry.removed_text.len()) as int,
        new_text,
    );
}

/// After redo → undo, the text is restored to pre-redo state.
pub proof fn lemma_redo_undo_cancel(
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
    ensures
        ({
            let entry = undo_entry_for_splice(
                model, start, end, new_text, new_styles, new_focus);
            let model_after = splice(
                model, start, end, new_text, new_styles, new_focus);
            let stack = push_undo(empty_undo_stack(), entry);
            let (stack2, model_undone) = apply_undo(stack, model_after);
            let (stack3, model_redone) = apply_redo(stack2, model_undone);
            let (_, model_reundone) = apply_undo(stack3, model_redone);
            model_reundone.text =~= model_undone.text
        }),
{
    let entry = undo_entry_for_splice(
        model, start, end, new_text, new_styles, new_focus);
    let model_after = splice(
        model, start, end, new_text, new_styles, new_focus);
    let stack = push_undo(empty_undo_stack(), entry);
    let (stack2, model_undone) = apply_undo(stack, model_after);

    // After undo, model_undone.text =~= model.text
    lemma_seq_splice_roundtrip(
        model.text, start as int, end as int, new_text);
    assert(model_undone.text =~= model.text);

    let (stack3, model_redone) = apply_redo(stack2, model_undone);

    // entry.removed_text = model.text[start..end)
    assert(entry.removed_text.len() == end - start);
    assert(model.text.subrange(start as int, end as int).len() == end - start);

    // Redo: splice(model_undone, start, start + removed.len(), inserted)
    // = splice(model_undone, start, end, new_text)

    // Undo again: splice(model_redone, start, start + inserted.len(), removed)
    // This is the roundtrip on model_undone.text
    lemma_seq_splice_roundtrip(
        model_undone.text,
        start as int,
        (start + entry.removed_text.len()) as int,
        entry.inserted_text,
    );
}

// ──────────────────────────────────────────────────────────────────────
// Merge well-formedness
// ──────────────────────────────────────────────────────────────────────

/// merge_entries preserves undo_entry_wf.
pub proof fn lemma_merge_entry_wf(e1: UndoEntry, e2: UndoEntry)
    requires
        undo_entry_wf(e1),
        undo_entry_wf(e2),
        can_merge_entries(e1, e2),
    ensures
        undo_entry_wf(merge_entries(e1, e2)),
{
    let merged = merge_entries(e1, e2);
    // removed_text/styles are empty → len 0 == 0 ✓
    // inserted_text = e1.inserted_text + e2.inserted_text
    // inserted_styles = e1.inserted_styles + e2.inserted_styles
    // len(a + b) = len(a) + len(b) for both
    assert(merged.inserted_text.len() == e1.inserted_text.len() + e2.inserted_text.len());
    assert(merged.inserted_styles.len() == e1.inserted_styles.len() + e2.inserted_styles.len());
}

/// push_undo_or_merge preserves stack well-formedness.
pub proof fn lemma_push_or_merge_preserves_wf(
    stack: UndoStack, entry: UndoEntry, merge: bool,
)
    requires
        undo_stack_wf(stack),
        undo_entry_wf(entry),
    ensures
        undo_stack_wf(push_undo_or_merge(stack, entry, merge)),
{
    let result = push_undo_or_merge(stack, entry, merge);
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        let top = stack.entries[(stack.position - 1) as int];
        let merged = merge_entries(top, entry);
        lemma_merge_entry_wf(top, entry);
        let truncated = stack.entries.subrange(0, (stack.position - 1) as int);
        assert forall|i: int| 0 <= i < result.entries.len()
            implies undo_entry_wf(#[trigger] result.entries[i])
        by {
            if i < truncated.len() {
                assert(result.entries[i] == truncated[i]);
                assert(truncated[i] == stack.entries[i]);
            } else {
                assert(result.entries[i] == merged);
            }
        }
    } else {
        lemma_push_preserves_wf(stack, entry);
    }
}

/// push_undo_or_merge always allows undo (at least one entry).
pub proof fn lemma_push_or_merge_enables_undo(
    stack: UndoStack, entry: UndoEntry, merge: bool,
)
    requires
        undo_stack_wf(stack),
        undo_entry_wf(entry),
    ensures
        can_undo(push_undo_or_merge(stack, entry, merge)),
{
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        let result = push_undo_or_merge(stack, entry, merge);
        // position unchanged, and position > 0 (from can_undo(stack))
        assert(result.position == stack.position);
        assert(result.position > 0);
    } else {
        lemma_push_enables_undo(stack, entry);
    }
}

/// Undoing a merged entry removes the full concatenated insertion.
pub proof fn lemma_merged_undo_correctness(
    model: TextModel,
    start1: nat,
    ch1: char,
    ch2: char,
    style1: StyleSet,
    style2: StyleSet,
)
    requires
        model.wf(),
        start1 + 2 <= model.text.len(),
        // The two chars were inserted at start1, start1+1
        model.text[start1 as int] == ch1,
        model.text[(start1 + 1) as int] == ch2,
    ensures
        ({
            // Construct what the merged entry looks like
            let e1 = UndoEntry {
                start: start1,
                removed_text: Seq::empty(),
                removed_styles: Seq::empty(),
                inserted_text: seq![ch1],
                inserted_styles: seq![style1],
                anchor_before: start1,
                focus_before: start1,
                focus_after: start1 + 1,
            };
            let e2 = UndoEntry {
                start: start1 + 1,
                removed_text: Seq::empty(),
                removed_styles: Seq::empty(),
                inserted_text: seq![ch2],
                inserted_styles: seq![style2],
                anchor_before: start1 + 1,
                focus_before: start1 + 1,
                focus_after: start1 + 2,
            };
            &&& can_merge_entries(e1, e2)
            &&& merge_entries(e1, e2).inserted_text =~= seq![ch1, ch2]
            &&& merge_entries(e1, e2).start == start1
        }),
{
    // Trivially follows from definitions
}

// ──────────────────────────────────────────────────────────────────────
// Undo history consistency proofs
// ──────────────────────────────────────────────────────────────────────

/// An empty stack with a single history entry is valid.
pub proof fn lemma_empty_history_valid(text: Seq<char>)
    ensures
        undo_history_valid(empty_undo_stack(), seq![text]),
{
}

/// From history validity and can_undo, extract apply_undo_exec's preconditions.
pub proof fn lemma_undo_preconditions_from_history(
    stack: UndoStack, history: Seq<Seq<char>>, current_text: Seq<char>,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_undo(stack),
        current_text =~= history[stack.position as int],
    ensures ({
        let entry = stack.entries[(stack.position - 1) as int];
        let undo_end = entry.start + entry.inserted_text.len();
        &&& undo_end <= current_text.len()
        &&& entry.focus_before <= current_text.len()
            - entry.inserted_text.len() + entry.removed_text.len()
        &&& current_text.len() - entry.inserted_text.len()
            + entry.removed_text.len() < usize::MAX
        &&& wf_text(seq_splice(current_text, entry.start as int,
                undo_end as int, entry.removed_text))
        &&& is_grapheme_boundary(
                seq_splice(current_text, entry.start as int,
                    undo_end as int, entry.removed_text),
                entry.focus_before)
    }),
{
    let pos = stack.position;
    let idx = (pos - 1) as int;
    let entry = stack.entries[idx];

    // entry_describes_transition(entry, history[pos-1], history[pos])
    // history[pos] =~= current_text
    // history[pos] =~= seq_splice(history[pos-1], entry.start, entry.start + entry.removed_text.len(), entry.inserted_text)
    // So current_text =~= seq_splice(history[pos-1], ...)
    let before = history[idx];
    let after = history[idx + 1];
    assert(entry_describes_transition(entry, before, after));

    // after =~= seq_splice(before, start, start + removed.len(), inserted)
    // So undo_end = entry.start + entry.inserted_text.len()
    // after.len() = before.len() - removed.len() + inserted.len()
    lemma_seq_splice_len(before, entry.start as int,
        (entry.start + entry.removed_text.len()) as int, entry.inserted_text);
    assert(after.len() == before.len() - entry.removed_text.len() + entry.inserted_text.len());

    // after =~= current_text, so undo_end <= current_text.len()
    // undo_end = start + inserted.len()
    // We need: start + inserted.len() <= after.len()
    // after = splice(before, start, start+removed.len(), inserted)
    // after.len() = before.len() - removed.len() + inserted.len()
    // start + removed.len() <= before.len() (from entry_describes_transition)
    // So start <= before.len() - removed.len()
    // start + inserted.len() <= before.len() - removed.len() + inserted.len() = after.len()

    // focus_before <= before.len()
    // We need: focus_before <= current_text.len() - inserted.len() + removed.len()
    //        = after.len() - inserted.len() + removed.len()
    //        = before.len()
    // That's exactly what entry_describes_transition gives us.

    // The undo splice = seq_splice(after, start, start+inserted.len(), removed)
    // By roundtrip, this =~= before
    lemma_seq_splice_roundtrip(before, entry.start as int,
        (entry.start + entry.removed_text.len()) as int, entry.inserted_text);
    // seq_splice(after, start, start+inserted.len(), removed) =~= before

    // before has wf_text, grapheme_boundary at focus_before, len < usize::MAX
}

/// From history validity and can_redo, extract apply_redo_exec's preconditions.
pub proof fn lemma_redo_preconditions_from_history(
    stack: UndoStack, history: Seq<Seq<char>>, current_text: Seq<char>,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_redo(stack),
        current_text =~= history[stack.position as int],
    ensures ({
        let entry = stack.entries[stack.position as int];
        let redo_end = entry.start + entry.removed_text.len();
        &&& redo_end <= current_text.len()
        &&& entry.focus_after <= current_text.len()
            - entry.removed_text.len() + entry.inserted_text.len()
        &&& current_text.len() - entry.removed_text.len()
            + entry.inserted_text.len() < usize::MAX
        &&& wf_text(seq_splice(current_text, entry.start as int,
                redo_end as int, entry.inserted_text))
        &&& is_grapheme_boundary(
                seq_splice(current_text, entry.start as int,
                    redo_end as int, entry.inserted_text),
                entry.focus_after)
    }),
{
    let pos = stack.position;
    let entry = stack.entries[pos as int];

    // entry_describes_transition(entry, history[pos], history[pos+1])
    let before = history[pos as int];
    let after = history[(pos + 1) as int];
    assert(entry_describes_transition(entry, before, after));

    // before =~= current_text
    // The redo splice = seq_splice(before, start, start+removed.len(), inserted)
    // = after (by entry_describes_transition)
    lemma_seq_splice_len(before, entry.start as int,
        (entry.start + entry.removed_text.len()) as int, entry.inserted_text);

    // after has wf_text, grapheme_boundary at focus_after, len < usize::MAX
}

/// push_undo preserves history validity when given a valid new transition.
pub proof fn lemma_push_undo_history_valid(
    stack: UndoStack, history: Seq<Seq<char>>,
    entry: UndoEntry, after_text: Seq<char>,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        entry_describes_transition(entry, history[stack.position as int], after_text),
    ensures
        undo_history_valid(
            push_undo(stack, entry),
            history.subrange(0, stack.position as int + 1).push(after_text)),
{
    let new_stack = push_undo(stack, entry);
    let new_history = history.subrange(0, stack.position as int + 1).push(after_text);

    // new_stack.entries = stack.entries[0..pos].push(entry), len = pos + 1
    // new_history.len() = pos + 1 + 1 = pos + 2 = new_stack.entries.len() + 1 ✓

    assert forall|i: int| 0 <= i < new_stack.entries.len()
        implies entry_describes_transition(
            #[trigger] new_stack.entries[i], new_history[i], new_history[i + 1])
    by {
        if i < stack.position as int {
            // Old entries: unchanged
            let truncated = stack.entries.subrange(0, stack.position as int);
            assert(new_stack.entries[i] == truncated[i]);
            assert(truncated[i] == stack.entries[i]);
            assert(new_history[i] == history[i]);
            assert(new_history[i + 1] == history[i + 1]);
            assert(entry_describes_transition(stack.entries[i], history[i], history[i + 1]));
        } else {
            // i == pos: the new entry
            assert(i == stack.position as int);
            assert(new_stack.entries[i] == entry);
            assert(new_history[i] == history[stack.position as int]);
            assert(new_history[i + 1] == after_text);
        }
    }
}

/// Two adjacent pure insertions compose into one.
pub proof fn lemma_seq_splice_insert_compose<A>(
    s: Seq<A>, start: int, text1: Seq<A>, text2: Seq<A>,
)
    requires 0 <= start <= s.len(),
    ensures
        seq_splice(
            seq_splice(s, start, start, text1),
            start + text1.len(), start + text1.len(), text2,
        ) =~= seq_splice(s, start, start, text1 + text2),
{
    let s1 = seq_splice(s, start, start, text1);
    lemma_seq_splice_len(s, start, start, text1);
    // s1.len() = s.len() + text1.len()
    // start + text1.len() <= s1.len()

    let s2 = seq_splice(s1, start + text1.len(), start + text1.len(), text2);
    lemma_seq_splice_len(s1, start + text1.len(), start + text1.len(), text2);

    let s3 = seq_splice(s, start, start, text1 + text2);
    lemma_seq_splice_len(s, start, start, text1 + text2);
    // Both s2 and s3 have the same length

    // Show elementwise equality
    assert(s2 =~= s3);
}

/// Merged entry describes the composed transition.
pub proof fn lemma_merge_describes_composed_transition(
    e1: UndoEntry, e2: UndoEntry,
    text_before: Seq<char>, text_middle: Seq<char>, text_after: Seq<char>,
)
    requires
        entry_describes_transition(e1, text_before, text_middle),
        entry_describes_transition(e2, text_middle, text_after),
        can_merge_entries(e1, e2),
    ensures
        entry_describes_transition(merge_entries(e1, e2), text_before, text_after),
{
    let merged = merge_entries(e1, e2);
    // e1: pure insertion at e1.start (removed_text empty)
    // e2: pure insertion at e1.start + e1.inserted_text.len() (removed_text empty)

    // text_middle = seq_splice(text_before, e1.start, e1.start, e1.inserted_text)
    // text_after = seq_splice(text_middle, e2.start, e2.start, e2.inserted_text)
    //            = seq_splice(text_middle, e1.start + e1.inserted.len(), ..., e2.inserted)

    // By compose lemma:
    lemma_seq_splice_insert_compose(
        text_before, e1.start as int, e1.inserted_text, e2.inserted_text);
    // seq_splice(seq_splice(text_before, start, start, ins1), start+ins1.len(), start+ins1.len(), ins2)
    // =~= seq_splice(text_before, start, start, ins1 + ins2)

    // merged.start = e1.start
    // merged.removed_text = Seq::empty(), len = 0
    // merged.inserted_text = e1.inserted_text + e2.inserted_text
    // remove_end = e1.start + 0 = e1.start

    // So we need: text_after =~= seq_splice(text_before, e1.start, e1.start, ins1 + ins2)
    // Which is what the compose lemma gives us.
    assert(text_after =~= seq_splice(text_before, e1.start as int, e1.start as int,
        e1.inserted_text + e2.inserted_text));

    // merged.removed_text = empty, so subrange check is trivial
    assert(text_before.subrange(e1.start as int, e1.start as int) =~= Seq::<char>::empty());
    assert(merged.removed_text =~= Seq::<char>::empty());

    // focus_before = e1.focus_before <= text_before.len() ✓
    // focus_after = e2.focus_after <= text_after.len() ✓

    // merged text length
    lemma_seq_splice_len(text_before, e1.start as int, e1.start as int,
        e1.inserted_text + e2.inserted_text);
    assert(text_after.len() == text_before.len() + e1.inserted_text.len() + e2.inserted_text.len());

    // wf_text, grapheme_boundary: from e1 (before) and e2 (after)
}

/// push_undo_or_merge preserves history validity.
pub proof fn lemma_push_or_merge_history_valid(
    stack: UndoStack, history: Seq<Seq<char>>,
    entry: UndoEntry, after_text: Seq<char>, merge: bool,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        entry_describes_transition(entry, history[stack.position as int], after_text),
        undo_entry_wf(entry),
    ensures ({
        let new_stack = push_undo_or_merge(stack, entry, merge);
        let new_history = if merge && can_undo(stack)
            && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
        {
            history.subrange(0, stack.position as int).push(after_text)
        } else {
            history.subrange(0, stack.position as int + 1).push(after_text)
        };
        undo_history_valid(new_stack, new_history)
    }),
{
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        // Merge path
        let pos = stack.position;
        let top = stack.entries[(pos - 1) as int];
        let merged = merge_entries(top, entry);
        let new_stack = push_undo_or_merge(stack, entry, merge);
        let new_history = history.subrange(0, pos as int).push(after_text);

        // new_stack.entries = stack.entries[0..pos-1].push(merged), len = pos
        // new_history.len() = pos + 1 = new_stack.entries.len() + 1 ✓

        // top describes transition from history[pos-1] to history[pos]
        // entry describes transition from history[pos] to after_text
        // merged describes transition from history[pos-1] to after_text
        lemma_merge_describes_composed_transition(
            top, entry, history[(pos - 1) as int], history[pos as int], after_text);

        assert forall|i: int| 0 <= i < new_stack.entries.len()
            implies entry_describes_transition(
                #[trigger] new_stack.entries[i], new_history[i], new_history[i + 1])
        by {
            if i < (pos - 1) as int {
                let truncated = stack.entries.subrange(0, (pos - 1) as int);
                assert(new_stack.entries[i] == truncated[i]);
                assert(truncated[i] == stack.entries[i]);
                assert(new_history[i] == history[i]);
                assert(new_history[i + 1] == history[i + 1]);
                assert(entry_describes_transition(stack.entries[i], history[i], history[i + 1]));
            } else {
                // i == pos - 1: the merged entry
                assert(i == (pos - 1) as int);
                assert(new_stack.entries[i] == merged);
                assert(new_history[i] == history[(pos - 1) as int]);
                assert(new_history[i + 1] == after_text);
            }
        }
    } else {
        // Push path
        lemma_push_undo_history_valid(stack, history, entry, after_text);
    }
}

/// After undo, history validity is preserved (entries and history unchanged).
pub proof fn lemma_undo_maintains_history(
    stack: UndoStack, history: Seq<Seq<char>>,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_undo(stack),
    ensures ({
        let new_stack = UndoStack {
            position: (stack.position - 1) as nat,
            ..stack
        };
        undo_history_valid(new_stack, history)
    }),
{
    // Entries unchanged, history unchanged, just position decrements.
    // All entry_describes_transition facts still hold.
    let new_stack = UndoStack {
        position: (stack.position - 1) as nat,
        ..stack
    };
    assert forall|i: int| 0 <= i < new_stack.entries.len()
        implies entry_describes_transition(
            #[trigger] new_stack.entries[i], history[i], history[i + 1])
    by {
        assert(new_stack.entries[i] == stack.entries[i]);
    }
}

/// After redo, history validity is preserved (entries and history unchanged).
pub proof fn lemma_redo_maintains_history(
    stack: UndoStack, history: Seq<Seq<char>>,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_redo(stack),
    ensures ({
        let new_stack = UndoStack {
            position: stack.position + 1,
            ..stack
        };
        undo_history_valid(new_stack, history)
    }),
{
    let new_stack = UndoStack {
        position: stack.position + 1,
        ..stack
    };
    assert forall|i: int| 0 <= i < new_stack.entries.len()
        implies entry_describes_transition(
            #[trigger] new_stack.entries[i], history[i], history[i + 1])
    by {
        assert(new_stack.entries[i] == stack.entries[i]);
    }
}

/// The history at the new position after undo matches the undo result text.
pub proof fn lemma_undo_history_position(
    stack: UndoStack, history: Seq<Seq<char>>, model: TextModel,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_undo(stack),
        model.text =~= history[stack.position as int],
    ensures ({
        let (new_stack, new_model) = apply_undo(stack, model);
        new_model.text =~= history[new_stack.position as int]
    }),
{
    let pos = stack.position;
    let entry = stack.entries[(pos - 1) as int];
    let before = history[(pos - 1) as int];
    let after = history[pos as int];
    assert(entry_describes_transition(entry, before, after));

    // after =~= model.text =~= seq_splice(before, start, start+removed.len(), inserted)
    // undo splice = seq_splice(after, start, start+inserted.len(), removed) =~= before
    lemma_seq_splice_roundtrip(before, entry.start as int,
        (entry.start + entry.removed_text.len()) as int, entry.inserted_text);
}

/// The history at the new position after redo matches the redo result text.
pub proof fn lemma_redo_history_position(
    stack: UndoStack, history: Seq<Seq<char>>, model: TextModel,
)
    requires
        undo_stack_wf(stack),
        undo_history_valid(stack, history),
        can_redo(stack),
        model.text =~= history[stack.position as int],
    ensures ({
        let (new_stack, new_model) = apply_redo(stack, model);
        new_model.text =~= history[new_stack.position as int]
    }),
{
    let pos = stack.position;
    let entry = stack.entries[pos as int];
    let before = history[pos as int];
    let after = history[(pos + 1) as int];
    assert(entry_describes_transition(entry, before, after));
    // redo splice = seq_splice(before, start, start+removed.len(), inserted) =~= after
}

} // verus!
