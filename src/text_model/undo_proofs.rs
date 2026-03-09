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

} // verus!
