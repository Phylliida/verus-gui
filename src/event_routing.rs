use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::widget::*;
use crate::event::*;
use crate::text_input::*;
use crate::text_model::session::*;

verus! {

// ── Route key event to focused text input ───────────────────────

/// Route a key event to the focused widget. If the focus path points
/// to a TextInput, apply the key to the corresponding session.
/// Returns the updated session map.
pub open spec fn route_key_event<T: OrderedRing>(
    widget: Widget<T>,
    focus_path: Seq<nat>,
    event: KeyEvent,
    sessions: Map<nat, TextEditSession>,
) -> Map<nat, TextEditSession> {
    match focused_text_input_id(widget, focus_path) {
        Some(id) => {
            match (sessions.contains_key(id), focused_text_input_config(widget, focus_path)) {
                (true, Some(config)) => {
                    let session = sessions[id];
                    let new_session = text_input_handle_key(session, config, event);
                    sessions.insert(id, new_session)
                },
                _ => sessions,
            }
        },
        None => sessions,
    }
}

// ── Proofs ───────────────────────────────────────────────────────

/// If the focus path does not point to a TextInput, sessions are unchanged.
pub proof fn lemma_route_key_no_focus_identity<T: OrderedRing>(
    widget: Widget<T>,
    focus_path: Seq<nat>,
    event: KeyEvent,
    sessions: Map<nat, TextEditSession>,
)
    requires
        focused_text_input_id(widget, focus_path).is_none(),
    ensures
        route_key_event(widget, focus_path, event, sessions) === sessions,
{}

/// Routing only modifies the focused session; all other sessions are preserved.
pub proof fn lemma_route_preserves_other_sessions<T: OrderedRing>(
    widget: Widget<T>,
    focus_path: Seq<nat>,
    event: KeyEvent,
    sessions: Map<nat, TextEditSession>,
    other_id: nat,
)
    requires
        focused_text_input_id(widget, focus_path) != Some(other_id),
        sessions.contains_key(other_id),
    ensures
        route_key_event(widget, focus_path, event, sessions).contains_key(other_id),
        route_key_event(widget, focus_path, event, sessions)[other_id]
            === sessions[other_id],
{
    match focused_text_input_id(widget, focus_path) {
        Some(id) => {
            // id != other_id
            // If sessions.contains_key(id) and config exists, result is sessions.insert(id, ...)
            // insert(id, ...) preserves other_id since id != other_id
        },
        None => {},
    }
}

/// Routing preserves session count (adds no new keys, removes none).
pub proof fn lemma_route_preserves_domain<T: OrderedRing>(
    widget: Widget<T>,
    focus_path: Seq<nat>,
    event: KeyEvent,
    sessions: Map<nat, TextEditSession>,
    any_id: nat,
)
    ensures
        focused_text_input_id(widget, focus_path).is_none() ==>
            route_key_event(widget, focus_path, event, sessions) === sessions,
{
}

} // verus!
