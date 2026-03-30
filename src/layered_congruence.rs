use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::widget::*;
use crate::layer::*;
use crate::layered_draw::*;
use crate::layered_hit_test::*;
use crate::draw::*;
use crate::draw_proofs::*;
use crate::hit_test::*;
use crate::animation::*;
use crate::layout::congruence_proofs::*;
use crate::diff::*;
use verus_algebra::traits::equivalence::Equivalence;

verus! {

//  ══════════════════════════════════════════════════════════════════════
//  LAYER STATE CONGRUENCE
//  ══════════════════════════════════════════════════════════════════════

///  Two layer states are eqv.
pub open spec fn layer_state_eqv<T: OrderedRing>(a: LayerState<T>, b: LayerState<T>) -> bool {
    a.transform.eqv(b.transform)
    && opt_clip_eqv(a.clip, b.clip)
    && a.alpha.eqv(b.alpha)
}

///  Default state is self-eqv.
pub proof fn lemma_default_state_eqv<T: OrderedField>()
    ensures layer_state_eqv(
        LayerState::<T>::default_state(),
        LayerState::<T>::default_state()),
{
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_reflexive(T::one());
}

//  ══════════════════════════════════════════════════════════════════════
//  LAYERED DRAW COMMAND CONGRUENCE
//  ══════════════════════════════════════════════════════════════════════

///  Two layered draw commands are eqv.
pub open spec fn layered_draw_cmd_eqv<T: OrderedRing>(
    a: LayeredDrawCommand<T>, b: LayeredDrawCommand<T>,
) -> bool {
    a.x.eqv(b.x) && a.y.eqv(b.y)
    && a.width.eqv(b.width) && a.height.eqv(b.height)
    && a.depth == b.depth
    && layer_state_eqv(a.layer_state, b.layer_state)
}

///  Two sequences of layered draw commands are element-wise eqv.
pub open spec fn layered_draws_eqv<T: OrderedRing>(
    a: Seq<LayeredDrawCommand<T>>, b: Seq<LayeredDrawCommand<T>>,
) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==> layered_draw_cmd_eqv(a[i], b[i])
}

//  ══════════════════════════════════════════════════════════════════════
//  INVERTIBILITY PREDICATE
//  ══════════════════════════════════════════════════════════════════════

///  Whether all Layer transforms in a widget tree are invertible (det ≢ 0).
pub open spec fn all_transforms_invertible<T: OrderedField>(
    widget: Widget<T>, fuel: nat,
) -> bool
    decreases fuel,
{
    if fuel == 0 { true }
    else {
        match widget {
            Widget::Wrapper(WrapperWidget::Layer { layer, child }) =>
                !verus_linalg::mat3::ops::det(layer.transform).eqv(T::zero())
                && all_transforms_invertible(*child, (fuel - 1) as nat),
            _ => {
                let children = get_children(widget);
                forall|i: int| 0 <= i < children.len() ==>
                    all_transforms_invertible(children[i], (fuel - 1) as nat)
            },
        }
    }
}

//  ══════════════════════════════════════════════════════════════════════
//  THE LAYER-AWARE FUNDAMENTAL THEOREM
//
//  Extends the original fundamental theorem with layer-specific guarantees.
//  All original properties hold (Layer is a layout passthrough), plus:
//  - Layout node congruence
//  - Full-depth draw congruence (flat pipeline)
//  - GPU safety on both sides
//  - Hit-test geometric correctness
//  - Animation congruence
//  ══════════════════════════════════════════════════════════════════════

///  The Layer-Aware Fundamental Theorem: the full GUI pipeline with Layer
///  widgets is correct and congruent.
///
///  Equivalent widget specs (w1 ≡ w2) under equivalent constraints produce:
///  - Equivalent layout nodes
///  - Equivalent flat draw commands at any depth within congruence_depth
///  - GPU-safe draws on both sides
///  - Equivalent animation interpolation
///  - Geometrically valid hit-test paths
///  - Same hit-test result for equivalent click coordinates
pub proof fn theorem_layer_fundamental<T: OrderedField>(
    //  Equivalent layout inputs
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
    //  Equivalent click coordinates
    px1: T, px2: T, py1: T, py2: T,
    //  Equivalent animation endpoints
    w1b: Widget<T>, w2b: Widget<T>,
    t: T,
    //  Draw/hit-test depth
    draw_fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        lim1.wf(),
        widget_eqv(w1, w2, fuel),
        widget_eqv(w1b, w2b, fuel),
        px1.eqv(px2), py1.eqv(py2),
        fuel > 0,
        draw_fuel <= congruence_depth(w1, fuel),
    ensures ({
        let n1 = layout_widget(lim1, w1, fuel);
        let n2 = layout_widget(lim2, w2, fuel);

        //  ── 1. Layout congruence ──
        &&& node_eqv(n1, n2)

        //  ── 2. Full-depth flat draw congruence ──
        &&& draws_eqv(
                flatten_node_to_draws(n1, T::zero(), T::zero(), 0, draw_fuel),
                flatten_node_to_draws(n2, T::zero(), T::zero(), 0, draw_fuel))

        //  ── 3. GPU safety on both sides ──
        &&& crate::vulkan_bridge::all_draws_valid(
                flatten_node_to_draws(n1, T::zero(), T::zero(), 0, draw_fuel))
        &&& crate::vulkan_bridge::all_draws_valid(
                flatten_node_to_draws(n2, T::zero(), T::zero(), 0, draw_fuel))

        //  ── 4. Animation congruence ──
        &&& nodes_deeply_eqv(
                lerp_node(n1, layout_widget(lim1, w1b, fuel), t, 1),
                lerp_node(n2, layout_widget(lim2, w2b, fuel), t, 1),
                0)

        //  ── 5. Hit-test geometric correctness ──
        &&& (hit_test(n1, px1, py1, fuel) is Some ==>
            path_geometrically_valid(
                n1, hit_test(n1, px1, py1, fuel).unwrap(), px1, py1))

        //  ── 6. Hit-test congruence (at congruence depth) ──
        &&& hit_test(n1, px1, py1, draw_fuel)
            == hit_test(n2, px2, py2, draw_fuel)
    }),
{
    let n1 = layout_widget(lim1, w1, fuel);
    let n2 = layout_widget(lim2, w2, fuel);

    //  1. Layout node congruence
    lemma_layout_widget_node_congruence(lim1, lim2, w1, w2, fuel);

    //  2. Full-depth draw congruence
    lemma_layout_widget_full_depth_congruence(lim1, lim2, w1, w2, fuel);
    let cd = congruence_depth(w1, fuel);
    lemma_deeply_eqv_depth_monotone(n1, n2, cd, draw_fuel);
    T::axiom_eqv_reflexive(T::zero());
    lemma_flatten_congruence(n1, n2,
        T::zero(), T::zero(), T::zero(), T::zero(), 0, draw_fuel);

    //  3. GPU safety on both sides
    crate::theorems::theorem_full_draw_validity(lim1, w1, fuel, draw_fuel);
    crate::theorems::lemma_limits_wf_congruence(lim1, lim2);
    crate::theorems::theorem_full_draw_validity(lim2, w2, fuel, draw_fuel);

    //  4. Animation congruence
    lemma_layout_widget_deep_congruence(lim1, lim2, w1, w2, fuel);
    lemma_layout_widget_deep_congruence(lim1, lim2, w1b, w2b, fuel);
    let n1b = layout_widget(lim1, w1b, fuel);
    let n2b = layout_widget(lim2, w2b, fuel);
    lemma_lerp_node_congruence_left(n1, n2, n1b, t, 1);
    lemma_lerp_node_congruence_right(n2, n1b, n2b, t, 1);
    lemma_deeply_eqv_transitive(
        lerp_node(n1, n1b, t, 1), lerp_node(n2, n1b, t, 1),
        lerp_node(n2, n2b, t, 1), 0);

    //  5. Hit-test geometric correctness
    if hit_test(n1, px1, py1, fuel) is Some {
        lemma_hit_test_geometrically_valid(n1, px1, py1, fuel);
    }

    //  6. Hit-test congruence
    lemma_deeply_eqv_depth_monotone(n1, n2, cd, draw_fuel);
    lemma_hit_test_congruence(n1, n2, px1, px2, py1, py2, draw_fuel);
}

} //  verus!
