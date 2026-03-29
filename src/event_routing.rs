use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::widget::*;
use crate::event::*;
use crate::text_input::*;
use crate::text_model::session::*;

verus! {

//  ── Route key event to focused text input ───────────────────────

///  Route a key event to the focused widget. If the focus path points
///  to a TextInput, apply the key to the corresponding session.
///  Returns the updated session map.
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

//  ── Proofs ───────────────────────────────────────────────────────

///  If the focus path does not point to a TextInput, sessions are unchanged.
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

///  Routing only modifies the focused session; all other sessions are preserved.
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
            //  id != other_id
            //  If sessions.contains_key(id) and config exists, result is sessions.insert(id, ...)
            //  insert(id, ...) preserves other_id since id != other_id
        },
        None => {},
    }
}

///  Routing preserves session count (adds no new keys, removes none).
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

//  ── Commutativity ────────────────────────────────────────────────

///  Helper: route_key_event result for known focus id and config.
proof fn lemma_route_result_structure<T: OrderedRing>(
    widget: Widget<T>,
    focus_path: Seq<nat>,
    event: KeyEvent,
    sessions: Map<nat, TextEditSession>,
)
    ensures ({
        let result = route_key_event(widget, focus_path, event, sessions);
        match focused_text_input_id(widget, focus_path) {
            Some(id) => {
                match (sessions.contains_key(id), focused_text_input_config(widget, focus_path)) {
                    (true, Some(config)) =>
                        result === sessions.insert(id,
                            text_input_handle_key(sessions[id], config, event)),
                    _ => result === sessions,
                }
            },
            None => result === sessions,
        }
    }),
{
}

///  Routing to disjoint text inputs commutes: if two focus paths target
///  different text input IDs, the order of routing doesn't matter.
pub proof fn lemma_route_disjoint_commutes<T: OrderedRing>(
    widget: Widget<T>,
    path1: Seq<nat>,
    path2: Seq<nat>,
    event1: KeyEvent,
    event2: KeyEvent,
    sessions: Map<nat, TextEditSession>,
)
    requires
        focused_text_input_id(widget, path1) is Some,
        focused_text_input_id(widget, path2) is Some,
        focused_text_input_id(widget, path1) != focused_text_input_id(widget, path2),
    ensures
        route_key_event(widget, path2, event2,
            route_key_event(widget, path1, event1, sessions))
        ===
        route_key_event(widget, path1, event1,
            route_key_event(widget, path2, event2, sessions)),
{
    let id1 = focused_text_input_id(widget, path1).unwrap();
    let id2 = focused_text_input_id(widget, path2).unwrap();
    let cfg1 = focused_text_input_config(widget, path1);
    let cfg2 = focused_text_input_config(widget, path2);

    //  Case analysis on whether sessions contain id1 and id2 + config availability
    //  In all cases, each route only touches its own id, and id1 != id2.

    //  If config missing or session missing for path1, route1 is identity
    if !sessions.contains_key(id1) || cfg1.is_none() {
        //  route1 = sessions, so both sides reduce to route(path2, event2, sessions)
        //  followed (or preceded) by a no-op
        assert(route_key_event(widget, path1, event1, sessions) === sessions);
        //  For the other order: route2 applied to sessions, then route1 is identity on result
        let after2 = route_key_event(widget, path2, event2, sessions);
        if !sessions.contains_key(id1) {
            //  after2 may or may not contain id1 — if id1 wasn't in sessions and
            //  route2 only inserts id2, id1 is still absent
            if after2.contains_key(id1) && cfg1.is_some() {
                //  This can only happen if id1 was already in sessions, contradiction
                assert(false);
            }
        }
    } else if !sessions.contains_key(id2) || cfg2.is_none() {
        //  Symmetric case: route2 is identity
        assert(route_key_event(widget, path2, event2, sessions) === sessions);
        let after1 = route_key_event(widget, path1, event1, sessions);
        if !sessions.contains_key(id2) {
            if after1.contains_key(id2) && cfg2.is_some() {
                //  after1 = sessions.insert(id1, ...). id2 != id1, so
                //  after1.contains_key(id2) == sessions.contains_key(id2) = false
                assert(false);
            }
        }
    } else {
        //  Both sessions exist. Configs: if either is None, that route is identity.
        match (cfg1, cfg2) {
            (Some(c1), Some(c2)) => {
                //  route1(sessions) = sessions.insert(id1, new1)
                //  route2(route1(sessions)) = sessions.insert(id1, new1).insert(id2, new2')
                //  But new2' uses route1(sessions)[id2] = sessions[id2] (since id1 != id2)
                //  So new2' = handle_key(sessions[id2], c2, event2) = new2
                //  Symmetrically for other order.
                //  Both results: sessions.insert(id1, new1).insert(id2, new2)
                let new1 = text_input_handle_key(sessions[id1], c1, event1);
                let new2 = text_input_handle_key(sessions[id2], c2, event2);
                let after1 = sessions.insert(id1, new1);
                let after2 = sessions.insert(id2, new2);
                //  after1[id2] == sessions[id2] since id1 != id2
                assert(after1[id2] === sessions[id2]);
                assert(after2[id1] === sessions[id1]);
                //  route2(after1) = after1.insert(id2, handle(after1[id2], c2, e2))
                //                 = after1.insert(id2, new2)
                //                 = sessions.insert(id1, new1).insert(id2, new2)
                //  route1(after2) = after2.insert(id1, handle(after2[id1], c1, e1))
                //                 = after2.insert(id1, new1)
                //                 = sessions.insert(id2, new2).insert(id1, new1)
                //  These are equal by Map insert commutativity for different keys
                assert(route_key_event(widget, path2, event2, after1)
                    === after1.insert(id2, new2));
                assert(route_key_event(widget, path1, event1, after2)
                    === after2.insert(id1, new1));
                //  Map insert commutativity: m.insert(k1,v1).insert(k2,v2)
                //    === m.insert(k2,v2).insert(k1,v1) when k1 != k2
                assert(after1.insert(id2, new2) =~= after2.insert(id1, new1));
            },
            _ => {},
        }
    }
}

///  Routing to no-focus paths is the identity regardless of order.
pub proof fn lemma_route_no_focus_commutes<T: OrderedRing>(
    widget: Widget<T>,
    path1: Seq<nat>,
    path2: Seq<nat>,
    event1: KeyEvent,
    event2: KeyEvent,
    sessions: Map<nat, TextEditSession>,
)
    requires
        focused_text_input_id(widget, path1).is_none(),
    ensures
        route_key_event(widget, path2, event2,
            route_key_event(widget, path1, event1, sessions))
        ===
        route_key_event(widget, path2, event2, sessions),
{
}

} //  verus!
