use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::node::Node;
use crate::hit_test::{hit_test, path_valid, point_in_node,
    lemma_hit_test_path_valid, lemma_hit_test_point_in_node};
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;

verus! {

// ── Event types ────────────────────────────────────────────────────

pub enum PointerEventKind {
    Down,
    Up,
    Move,
}

/// A pointer event with coordinates.
pub struct PointerEvent<T: OrderedRing> {
    pub kind: PointerEventKind,
    pub x: T,
    pub y: T,
}

// ── Dispatch ───────────────────────────────────────────────────────

/// Dispatch a pointer event: find the target path using hit_test.
pub open spec fn dispatch_pointer<T: OrderedRing>(
    root: Node<T>,
    event: PointerEvent<T>,
    fuel: nat,
) -> Option<Seq<nat>> {
    hit_test(root, event.x, event.y, fuel)
}

// ── Focus state ────────────────────────────────────────────────────

/// Focus tracks which path was last clicked (PointerDown).
pub struct FocusState {
    pub focused_path: Option<Seq<nat>>,
}

pub open spec fn initial_focus() -> FocusState {
    FocusState { focused_path: None }
}

pub open spec fn update_focus<T: OrderedRing>(
    state: FocusState,
    root: Node<T>,
    event: PointerEvent<T>,
    fuel: nat,
) -> FocusState {
    match event.kind {
        PointerEventKind::Down => FocusState {
            focused_path: hit_test(root, event.x, event.y, fuel),
        },
        _ => state,
    }
}

// ── Dispatch soundness proofs ──────────────────────────────────────

/// Dispatch always returns valid paths.
pub proof fn lemma_dispatch_path_valid<T: OrderedRing>(
    root: Node<T>,
    event: PointerEvent<T>,
    fuel: nat,
)
    requires
        dispatch_pointer(root, event, fuel) is Some,
    ensures
        path_valid(root, dispatch_pointer(root, event, fuel).unwrap()),
{
    lemma_hit_test_path_valid(root, event.x, event.y, fuel);
}

/// Dispatch target is within root bounds.
pub proof fn lemma_dispatch_in_bounds<T: OrderedRing>(
    root: Node<T>,
    event: PointerEvent<T>,
    fuel: nat,
)
    requires
        dispatch_pointer(root, event, fuel) is Some,
    ensures
        point_in_node(root, event.x, event.y),
{
    lemma_hit_test_point_in_node(root, event.x, event.y, fuel);
}

// ── Bubble path ────────────────────────────────────────────────────

/// The sequence of ancestor paths from the target to the root.
/// bubble_path([2,1,0]) = [[2,1,0], [2,1], [2], []]
pub open spec fn bubble_path(path: Seq<nat>) -> Seq<Seq<nat>>
    decreases path.len(),
{
    if path.len() == 0 {
        seq![Seq::<nat>::empty()]
    } else {
        seq![path].add(bubble_path(path.subrange(0, path.len() as int - 1)))
    }
}

// ── Bubble + focus proofs ──────────────────────────────────────────

/// Bubble path has length = original path length + 1 (includes root).
pub proof fn lemma_bubble_path_len(path: Seq<nat>)
    ensures
        bubble_path(path).len() == path.len() + 1,
    decreases path.len(),
{
    if path.len() > 0 {
        lemma_bubble_path_len(path.subrange(0, path.len() as int - 1));
    }
}

/// path_valid is prefix-closed: valid path -> any prefix is valid.
pub proof fn lemma_path_valid_prefix<T: OrderedRing>(
    root: Node<T>,
    path: Seq<nat>,
    k: nat,
)
    requires
        path_valid(root, path),
        k <= path.len(),
    ensures
        path_valid(root, path.subrange(0, k as int)),
    decreases path.len(),
{
    if k == 0 {
        // empty path is always valid
    } else if path.len() == 0 {
        // k <= 0, so k == 0, handled above
    } else {
        // path_valid(root, path) implies:
        //   path[0] < root.children.len()
        //   path_valid(root.children[path[0]], path.subrange(1, path.len()))
        let idx = path[0];
        let child = root.children[idx as int];
        let rest = path.subrange(1, path.len() as int);
        // We need path_valid(root, path.subrange(0, k))
        // path.subrange(0, k) = seq![idx] + path.subrange(1, k)
        assert(path.subrange(0, k as int)[0] == idx);
        assert(path.subrange(0, k as int).subrange(1, k as int) =~= path.subrange(1, k as int));
        // Need: path_valid(child, path.subrange(1, k))
        // By IH: path_valid(child, rest) and (k-1) <= rest.len()
        //   → path_valid(child, rest.subrange(0, k-1))
        // rest.subrange(0, k-1) = path.subrange(1, k)
        lemma_path_valid_prefix(child, rest, (k - 1) as nat);
        assert(rest.subrange(0, (k - 1) as int) =~= path.subrange(1, k as int));
    }
}

/// Each bubble path entry is a valid prefix of the original.
pub proof fn lemma_bubble_paths_valid<T: OrderedRing>(
    root: Node<T>,
    path: Seq<nat>,
)
    requires
        path_valid(root, path),
    ensures
        forall|i: nat| i < bubble_path(path).len() ==>
            path_valid(root, #[trigger] bubble_path(path)[i as int]),
    decreases path.len(),
{
    lemma_bubble_path_len(path);
    if path.len() == 0 {
        // bubble_path([]) = [[]], only entry is empty path which is valid
    } else {
        // bubble_path(path) = [path] ++ bubble_path(path[0..n-1])
        let prefix = path.subrange(0, path.len() as int - 1);
        // path is valid → prefix is valid
        lemma_path_valid_prefix(root, path, (path.len() - 1) as nat);
        assert(prefix =~= path.subrange(0, path.len() as int - 1));
        // Recurse on prefix
        lemma_bubble_paths_valid(root, prefix);

        // Entry 0 is path itself (valid by precondition)
        assert(bubble_path(path)[0] =~= path);

        // Entries 1..n+1 come from bubble_path(prefix)
        assert forall|i: nat| i < bubble_path(path).len() implies
            path_valid(root, #[trigger] bubble_path(path)[i as int])
        by {
            if i == 0 {
                assert(bubble_path(path)[0] =~= path);
            } else {
                // bubble_path(path)[i] = bubble_path(prefix)[i-1]
                assert(bubble_path(path)[i as int] =~= bubble_path(prefix)[(i - 1) as int]);
            }
        };
    }
}

/// Focus is stable on non-Down events.
pub proof fn lemma_focus_stable_on_move<T: OrderedRing>(
    state: FocusState,
    root: Node<T>,
    event: PointerEvent<T>,
    fuel: nat,
)
    requires
        !matches!(event.kind, PointerEventKind::Down),
    ensures
        update_focus(state, root, event, fuel) === state,
{
}

// ── Keyboard event types ──────────────────────────────────────────

/// Modifier key state.
pub struct Modifiers {
    pub shift: bool,
    pub ctrl: bool,
    pub alt: bool,
}

/// Kind of keyboard event.
pub enum KeyEventKind {
    Char(char),
    Backspace,
    Delete,
    Left,
    Right,
    Up,
    Down,
    Home,
    End,
    Enter,
    Tab,
    SelectAll,
    Undo,
    Redo,
    Cut,
    Copy,
}

/// A keyboard event with modifiers.
pub struct KeyEvent {
    pub kind: KeyEventKind,
    pub modifiers: Modifiers,
}

// ── Key to move direction ────────────────────────────────────────

/// Map arrow/home/end key events to move directions.
pub open spec fn key_to_move_direction(event: KeyEvent) -> Option<MoveDirection> {
    match event.kind {
        KeyEventKind::Left => if event.modifiers.ctrl {
            Some(MoveDirection::WordLeft)
        } else {
            Some(MoveDirection::Left)
        },
        KeyEventKind::Right => if event.modifiers.ctrl {
            Some(MoveDirection::WordRight)
        } else {
            Some(MoveDirection::Right)
        },
        KeyEventKind::Up => Some(MoveDirection::Up),
        KeyEventKind::Down => Some(MoveDirection::Down),
        KeyEventKind::Home => if event.modifiers.ctrl {
            Some(MoveDirection::Home)
        } else {
            Some(MoveDirection::LineStart)
        },
        KeyEventKind::End => if event.modifiers.ctrl {
            Some(MoveDirection::End)
        } else {
            Some(MoveDirection::LineEnd)
        },
        _ => None,
    }
}

/// Result of dispatching a key event.
pub enum KeyAction {
    /// A text model operation that produces a new model.
    NewModel(TextModel),
    /// An undo/redo/clipboard action handled at a higher level.
    External(ExternalAction),
    /// Key event not handled.
    None,
}

/// Actions that must be handled externally (undo stack, clipboard).
pub enum ExternalAction {
    Undo,
    Redo,
    Cut,
    Copy,
}

/// Dispatch a keyboard event to a text model operation.
pub open spec fn dispatch_key(model: TextModel, event: KeyEvent) -> KeyAction {
    match event.kind {
        KeyEventKind::Char(ch) => {
            if is_permitted(ch) && ch != '\r' {
                KeyAction::NewModel(insert_char(model, ch))
            } else {
                KeyAction::None
            }
        },
        KeyEventKind::Enter => {
            KeyAction::NewModel(insert_char(model, '\n'))
        },
        KeyEventKind::Tab => {
            KeyAction::NewModel(insert_char(model, '\t'))
        },
        KeyEventKind::Backspace => {
            if event.modifiers.ctrl {
                KeyAction::NewModel(delete_word_backward(model))
            } else {
                KeyAction::NewModel(delete_backward(model))
            }
        },
        KeyEventKind::Delete => {
            if event.modifiers.ctrl {
                KeyAction::NewModel(delete_word_forward(model))
            } else {
                KeyAction::NewModel(delete_forward(model))
            }
        },
        KeyEventKind::SelectAll => {
            KeyAction::NewModel(select_all(model))
        },
        KeyEventKind::Undo => KeyAction::External(ExternalAction::Undo),
        KeyEventKind::Redo => KeyAction::External(ExternalAction::Redo),
        KeyEventKind::Cut => KeyAction::External(ExternalAction::Cut),
        KeyEventKind::Copy => KeyAction::External(ExternalAction::Copy),
        _ => {
            // Arrow/Home/End keys
            match key_to_move_direction(event) {
                Some(dir) => {
                    if event.modifiers.shift {
                        KeyAction::NewModel(extend_selection(model, dir))
                    } else {
                        KeyAction::NewModel(move_cursor(model, dir))
                    }
                },
                None => KeyAction::None,
            }
        },
    }
}

} // verus!
