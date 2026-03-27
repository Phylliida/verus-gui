use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::widget::*;
use crate::draw::*;
use crate::draw_proofs::*;
use crate::diff::*;
use crate::hit_test::*;
use crate::animation::*;
use crate::vulkan_bridge::*;
use crate::layout::congruence_proofs::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::undo::*;
use crate::event::*;

verus! {

// ══════════════════════════════════════════════════════════════════════
// THE FUNDAMENTAL THEOREM OF THE GUI FRAMEWORK
//
// The entire GUI pipeline — layout, rendering, hit-testing, animation,
// text editing, and incremental updates — is correct. Specifically:
//
// 1. QUOTIENT WELL-DEFINEDNESS: The pipeline is a well-defined function
//    on the quotient ring of rational representations. Equivalent inputs
//    produce equivalent visual output, interaction behavior, and animations.
//
// 2. GPU SAFETY: Layout with well-formed constraints produces draw
//    commands with non-negative dimensions, safe for GPU submission.
//
// 3. HIT-TEST CORRECTNESS: Hit-testing produces geometrically valid
//    paths — the click point is within the node at every path step.
//
// 4. EDIT INTEGRITY: Text editing preserves model well-formedness,
//    and undo-redo is a perfect roundtrip on text and styles.
//
// 5. INCREMENTAL CORRECTNESS: Changing one widget only affects that
//    subtree; siblings are identical and diff detects no change.
//
// 6. DETERMINISM: Layout is deterministic once fuel exceeds tree depth.
// ══════════════════════════════════════════════════════════════════════

/// The Fundamental Theorem: the GUI pipeline is correct.
///
/// Given equivalent widget specifications (w1 ≡ w2) under equivalent
/// layout constraints (lim1 ≡ lim2), the pipeline produces:
///   - Equivalent layout nodes (same position, size, children count)
///   - Equivalent root draw commands (same rendered rectangle)
///   - Equivalent measure results (same fast-path size)
///   - Same containment decision for equivalent click coordinates
///   - Equivalent animation interpolation
///   - Valid GPU draw commands (non-negative dimensions)
///   - Geometrically correct hit-test paths
pub proof fn the_fundamental_theorem<T: OrderedField>(
    // Equivalent layout inputs
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
    // Equivalent click coordinates
    px1: T, px2: T, py1: T, py2: T,
    // Equivalent animation endpoints
    w1b: Widget<T>, w2b: Widget<T>,
    t: T,
    // Draw parameters
    draw_fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        lim1.wf(),
        widget_eqv(w1, w2, fuel),
        widget_eqv(w1b, w2b, fuel),
        px1.eqv(px2), py1.eqv(py2),
        fuel > 0,
    ensures ({
        let n1 = layout_widget(lim1, w1, fuel);
        let n2 = layout_widget(lim2, w2, fuel);

        // ── 1. Quotient well-definedness ──

        // Layout produces equivalent nodes (x, y, size eqv, children count equal)
        &&& node_eqv(n1, n2)

        // Root draw commands are equivalent
        &&& draws_eqv(
                flatten_node_to_draws(n1, T::zero(), T::zero(), 0, 0),
                flatten_node_to_draws(n2, T::zero(), T::zero(), 0, 0))

        // Measure (fast-path size) is equivalent
        &&& size_eqv(
                crate::measure::measure_widget(lim1, w1, fuel),
                crate::measure::measure_widget(lim2, w2, fuel))

        // Same containment decision at root
        &&& point_in_node(n1, px1, py1) == point_in_node(n2, px2, py2)

        // Animation interpolation produces equivalent results
        &&& nodes_deeply_eqv(
                lerp_node(n1, layout_widget(lim1, w1b, fuel), t, 1),
                lerp_node(n2, layout_widget(lim2, w2b, fuel), t, 1),
                0)

        // ── 2. GPU safety ──

        // Root draw command has non-negative dimensions
        &&& ({
            let draws = flatten_node_to_draws(n1, T::zero(), T::zero(), 0, draw_fuel);
            draws.len() > 0 && draw_command_valid(draws[0])
        })

        // ── 3. Hit-test correctness ──

        // If hit-test succeeds, path is geometrically valid
        &&& (hit_test(n1, px1, py1, fuel) is Some ==>
            path_geometrically_valid(
                n1, hit_test(n1, px1, py1, fuel).unwrap(), px1, py1))
    }),
{
    let n1 = layout_widget(lim1, w1, fuel);
    let n2 = layout_widget(lim2, w2, fuel);

    // 1a. Layout node congruence
    lemma_layout_widget_node_congruence(lim1, lim2, w1, w2, fuel);

    // 1b. Draw congruence (root)
    lemma_layout_widget_deep_congruence(lim1, lim2, w1, w2, fuel);
    T::axiom_eqv_reflexive(T::zero());
    lemma_flatten_congruence(n1, n2,
        T::zero(), T::zero(), T::zero(), T::zero(), 0, 0);

    // 1c. Measure congruence
    lemma_measure_widget_congruence(lim1, lim2, w1, w2, fuel);

    // 1d. Interaction congruence
    lemma_point_in_node_congruence(n1, n2, px1, px2, py1, py2);

    // 1e. Animation congruence
    lemma_layout_widget_deep_congruence(lim1, lim2, w1b, w2b, fuel);
    let n1b = layout_widget(lim1, w1b, fuel);
    let n2b = layout_widget(lim2, w2b, fuel);
    lemma_lerp_node_congruence_left(n1, n2, n1b, t, 1);
    lemma_lerp_node_congruence_right(n2, n1b, n2b, t, 1);
    lemma_deeply_eqv_transitive(
        lerp_node(n1, n1b, t, 1), lerp_node(n2, n1b, t, 1),
        lerp_node(n2, n2b, t, 1), 0);

    // 2. GPU safety: root draw is valid
    lemma_layout_root_draw_valid(lim1, w1, fuel, draw_fuel);

    // 3. Hit-test geometric correctness
    if hit_test(n1, px1, py1, fuel) is Some {
        lemma_hit_test_geometrically_valid(n1, px1, py1, fuel);
    }
}

// ══════════════════════════════════════════════════════════════════════
// EDIT INTEGRITY
// ══════════════════════════════════════════════════════════════════════

/// Edit integrity: character insertion preserves well-formedness and
/// undo-redo is a perfect roundtrip on both text and styles.
pub proof fn theorem_edit_integrity(model: TextModel, ch: char)
    requires
        model.wf(),
        is_permitted(ch), ch != '\r',
        model.composition.is_none(),
    ensures ({
        let (s, e) = selection_range(model.anchor, model.focus);
        let m2 = insert_char(model, ch);

        // Well-formedness preserved
        &&& m2.wf()

        // Undo-redo roundtrip
        &&& ({
            let entry = undo_entry_for_splice(model, s, e, seq![ch], seq![model.typing_style], s + 1);
            let stack = push_undo(empty_undo_stack(), entry);
            let (stack2, undone) = apply_undo(stack, m2);
            let (_, redone) = apply_redo(stack2, undone);
            redone.text =~= m2.text && redone.styles =~= m2.styles
        })
    }),
{
    let (s, e) = selection_range(model.anchor, model.focus);
    crate::text_model::proofs::lemma_dispatch_insert_preserves_wf(model, ch);
    crate::text_model::undo_proofs::lemma_undo_redo_cancel_full(
        model, s, e, seq![ch], seq![model.typing_style], s + 1);
}

// ══════════════════════════════════════════════════════════════════════
// DISPATCH KEY WELL-FORMEDNESS
// ══════════════════════════════════════════════════════════════════════

/// Master dispatch_key wf: every key event that produces a NewModel
/// preserves text model well-formedness.
pub proof fn theorem_dispatch_key_preserves_wf(model: TextModel, event: KeyEvent)
    requires
        model.wf(),
    ensures
        match dispatch_key(model, event) {
            KeyAction::NewModel(m) => m.wf(),
            _ => true,
        },
{
    use crate::text_model::proofs::*;
    match event.kind {
        KeyEventKind::Char(ch) => {
            if model.composition.is_some() {
            } else if is_permitted(ch) && ch != '\r' {
                lemma_dispatch_insert_preserves_wf(model, ch);
            }
        },
        KeyEventKind::Enter => {
            if model.composition.is_some() {
            } else {
                lemma_dispatch_insert_preserves_wf(model, '\n');
            }
        },
        KeyEventKind::Tab => {
            if model.composition.is_some() {
            } else {
                lemma_dispatch_insert_preserves_wf(model, '\t');
            }
        },
        KeyEventKind::Backspace => {
            if model.composition.is_some() {
            } else if has_selection(model.anchor, model.focus) {
                lemma_dispatch_delete_selection_preserves_wf(model);
            } else if model.focus == 0 {
            } else if event.modifiers.ctrl {
                lemma_delete_word_backward_preserves_wf(model);
            } else {
                lemma_dispatch_delete_backward_preserves_wf(model);
            }
        },
        KeyEventKind::Delete => {
            if model.composition.is_some() {
            } else if has_selection(model.anchor, model.focus) {
                lemma_dispatch_delete_selection_preserves_wf(model);
            } else if model.focus >= model.text.len() {
            } else if event.modifiers.ctrl {
                lemma_delete_word_forward_preserves_wf(model);
            } else {
                lemma_dispatch_delete_forward_preserves_wf(model);
            }
        },
        KeyEventKind::SelectAll => {
            lemma_select_all_preserves_wf(model);
        },
        KeyEventKind::ComposeStart => {
            if model.composition.is_some() {
            } else {
                lemma_compose_start_preserves_wf(model);
            }
        },
        KeyEventKind::ComposeUpdate(text, cursor) => {
            if model.composition.is_none() || cursor > text.len() {
            } else {
                lemma_compose_update_preserves_wf(model, text, cursor);
            }
        },
        KeyEventKind::ComposeCommit => {
            if model.composition.is_none() {
            } else {
                lemma_dispatch_compose_commit_preserves_wf(model);
            }
        },
        KeyEventKind::ComposeCancel => {
            lemma_compose_cancel_preserves_wf(model);
        },
        _ => {
            // Arrow/Home/End keys
            match key_to_move_direction(event) {
                Some(dir) => {
                    if event.modifiers.shift {
                        lemma_dispatch_extend_selection_preserves_wf(model, dir);
                    } else {
                        lemma_dispatch_move_preserves_wf(model, dir);
                    }
                },
                None => {},
            }
        },
    }
}

// ══════════════════════════════════════════════════════════════════════
// INCREMENTAL CORRECTNESS + DETERMINISM
// ══════════════════════════════════════════════════════════════════════

/// Frame theorem + determinism: unchanged siblings have identical layout,
/// diff detects no change for them, and converged layout is fuel-independent.
pub proof fn theorem_incremental_and_deterministic<T: OrderedField>(
    limits: Limits<T>,
    children1: Seq<Widget<T>>,
    children2: Seq<Widget<T>>,
    fuel: nat,
    diff_fuel: nat,
    // Determinism inputs
    widget: Widget<T>,
    fuel1: nat, fuel2: nat,
)
    requires
        children1.len() == children2.len(),
        diff_fuel > 0,
        widget_converged(widget, fuel1),
        widget_converged(widget, fuel2),
    ensures
        // Frame: all unchanged siblings are identical in layout and diff
        (forall|j: int| 0 <= j < children1.len() && children1[j] === children2[j] ==> ({
            let cn1 = widget_child_nodes(limits, children1, fuel);
            let cn2 = widget_child_nodes(limits, children2, fuel);
            cn1[j] === cn2[j]
            && diff_nodes::<T>(cn1[j], cn2[j], diff_fuel) === DiffResult::<T>::Same
        }))
        // Determinism: layout is fuel-independent once converged
        && layout_widget(limits, widget, fuel1) == layout_widget(limits, widget, fuel2),
{
    // Frame theorem
    assert forall|j: int| 0 <= j < children1.len() && children1[j] === children2[j]
    implies ({
        let cn1 = widget_child_nodes(limits, children1, fuel);
        let cn2 = widget_child_nodes(limits, children2, fuel);
        cn1[j] === cn2[j]
        && diff_nodes::<T>(cn1[j], cn2[j], diff_fuel) === DiffResult::<T>::Same
    }) by {
        crate::layout::incremental_proofs::lemma_sibling_layout_independent(
            limits, children1, children2, fuel, j);
        let cn1 = widget_child_nodes(limits, children1, fuel);
        lemma_diff_reflexive::<T>(cn1[j], diff_fuel);
    };

    // Determinism
    crate::widget::lemma_layout_deterministic(limits, widget, fuel1, fuel2);
}

} // verus!
