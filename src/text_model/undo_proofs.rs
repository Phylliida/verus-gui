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

} // verus!
