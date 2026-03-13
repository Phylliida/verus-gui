use vstd::prelude::*;
use super::*;
use super::operations::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Undo entry
// ──────────────────────────────────────────────────────────────────────

/// A single undo entry capturing both directions of a splice operation.
/// Stores enough information to reverse (undo) and replay (redo) the edit.
pub struct UndoEntry {
    /// Start position of the splice.
    pub start: nat,
    /// Text that was removed by the splice (original content).
    pub removed_text: Seq<char>,
    /// Styles that were removed by the splice.
    pub removed_styles: Seq<StyleSet>,
    /// Text that was inserted by the splice (new content).
    pub inserted_text: Seq<char>,
    /// Styles that were inserted by the splice.
    pub inserted_styles: Seq<StyleSet>,
    /// Anchor position before the edit.
    pub anchor_before: nat,
    /// Focus position before the edit.
    pub focus_before: nat,
    /// Focus position after the edit.
    pub focus_after: nat,
}

// ──────────────────────────────────────────────────────────────────────
// Undo stack
// ──────────────────────────────────────────────────────────────────────

/// A stack of undo/redo entries with a current position.
/// Entries `[0..position)` are undo-able; entries `[position..len)` are redo-able.
pub struct UndoStack {
    pub entries: Seq<UndoEntry>,
    pub position: nat,
}

/// Well-formedness of an undo entry.
pub open spec fn undo_entry_wf(entry: UndoEntry) -> bool {
    &&& entry.removed_text.len() == entry.removed_styles.len()
    &&& entry.inserted_text.len() == entry.inserted_styles.len()
}

/// Well-formedness of an undo stack.
pub open spec fn undo_stack_wf(stack: UndoStack) -> bool {
    &&& stack.position <= stack.entries.len()
    &&& forall|i: int| 0 <= i < stack.entries.len() ==>
        undo_entry_wf(#[trigger] stack.entries[i])
}

/// An empty undo stack.
pub open spec fn empty_undo_stack() -> UndoStack {
    UndoStack {
        entries: Seq::empty(),
        position: 0,
    }
}

/// Whether the stack has entries to undo.
pub open spec fn can_undo(stack: UndoStack) -> bool {
    stack.position > 0
}

/// Whether the stack has entries to redo.
pub open spec fn can_redo(stack: UndoStack) -> bool {
    stack.position < stack.entries.len()
}

// ──────────────────────────────────────────────────────────────────────
// Entry construction
// ──────────────────────────────────────────────────────────────────────

/// Create an undo entry capturing the inverse of
/// `splice(model, start, end, new_text, new_styles, new_focus)`.
pub open spec fn undo_entry_for_splice(
    model: TextModel,
    start: nat,
    end: nat,
    new_text: Seq<char>,
    new_styles: Seq<StyleSet>,
    new_focus: nat,
) -> UndoEntry {
    UndoEntry {
        start,
        removed_text: model.text.subrange(start as int, end as int),
        removed_styles: model.styles.subrange(start as int, end as int),
        inserted_text: new_text,
        inserted_styles: new_styles,
        anchor_before: model.anchor,
        focus_before: model.focus,
        focus_after: new_focus,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Push / truncate
// ──────────────────────────────────────────────────────────────────────

/// Push an undo entry, truncating any redo entries beyond the current position.
pub open spec fn push_undo(stack: UndoStack, entry: UndoEntry) -> UndoStack {
    UndoStack {
        entries: stack.entries.subrange(0, stack.position as int).push(entry),
        position: stack.position + 1,
    }
}

/// Convenience: record an edit by creating and pushing an undo entry.
pub open spec fn record_edit(
    stack: UndoStack,
    model: TextModel,
    start: nat,
    end: nat,
    new_text: Seq<char>,
    new_styles: Seq<StyleSet>,
    new_focus: nat,
) -> UndoStack {
    push_undo(
        stack,
        undo_entry_for_splice(model, start, end, new_text, new_styles, new_focus),
    )
}

// ──────────────────────────────────────────────────────────────────────
// Apply undo / redo
// ──────────────────────────────────────────────────────────────────────

/// Apply undo: splice the inverse of the most recent edit.
/// Returns (new_stack, new_model).
pub open spec fn apply_undo(
    stack: UndoStack,
    model: TextModel,
) -> (UndoStack, TextModel)
    recommends can_undo(stack),
{
    let entry = stack.entries[(stack.position - 1) as int];
    let new_model = splice(
        model,
        entry.start,
        entry.start + entry.inserted_text.len(),
        entry.removed_text,
        entry.removed_styles,
        entry.focus_before,
    );
    let new_stack = UndoStack {
        position: (stack.position - 1) as nat,
        ..stack
    };
    (new_stack, new_model)
}

/// Apply redo: replay the edit at the current position.
/// Returns (new_stack, new_model).
pub open spec fn apply_redo(
    stack: UndoStack,
    model: TextModel,
) -> (UndoStack, TextModel)
    recommends can_redo(stack),
{
    let entry = stack.entries[stack.position as int];
    let new_model = splice(
        model,
        entry.start,
        entry.start + entry.removed_text.len(),
        entry.inserted_text,
        entry.inserted_styles,
        entry.focus_after,
    );
    let new_stack = UndoStack {
        position: stack.position + 1,
        ..stack
    };
    (new_stack, new_model)
}

// ──────────────────────────────────────────────────────────────────────
// Undo merge
// ──────────────────────────────────────────────────────────────────────

/// Whether two entries can be merged (adjacent pure insertions).
/// Both must be pure insertions (removed_text empty), and e2 must start
/// where e1's insertion ends.
pub open spec fn can_merge_entries(e1: UndoEntry, e2: UndoEntry) -> bool {
    &&& e1.removed_text.len() == 0
    &&& e2.removed_text.len() == 0
    &&& e2.start == e1.start + e1.inserted_text.len()
}

/// Merge two adjacent insertion entries into one.
pub open spec fn merge_entries(e1: UndoEntry, e2: UndoEntry) -> UndoEntry {
    UndoEntry {
        start: e1.start,
        removed_text: Seq::empty(),
        removed_styles: Seq::empty(),
        inserted_text: e1.inserted_text + e2.inserted_text,
        inserted_styles: e1.inserted_styles + e2.inserted_styles,
        anchor_before: e1.anchor_before,
        focus_before: e1.focus_before,
        focus_after: e2.focus_after,
    }
}

/// Push an undo entry, optionally merging with the top entry.
/// If `merge` is true and the top entry is merge-compatible, replace top with merged.
/// Otherwise, normal push.
pub open spec fn push_undo_or_merge(
    stack: UndoStack, entry: UndoEntry, merge: bool,
) -> UndoStack {
    if merge && can_undo(stack)
        && can_merge_entries(stack.entries[(stack.position - 1) as int], entry)
    {
        let top = stack.entries[(stack.position - 1) as int];
        let merged = merge_entries(top, entry);
        UndoStack {
            entries: stack.entries.subrange(0, (stack.position - 1) as int).push(merged),
            position: stack.position,
        }
    } else {
        push_undo(stack, entry)
    }
}

} // verus!
