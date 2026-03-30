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
use crate::layout::congruence_proofs::*;
use crate::diff::nodes_deeply_eqv;

verus! {

//  ══════════════════════════════════════════════════════════════════════
//  LAYER STATE CONGRUENCE
//  ══════════════════════════════════════════════════════════════════════

///  Two layer states are eqv.
pub open spec fn layer_state_eqv<T: OrderedRing>(a: LayerState<T>, b: LayerState<T>) -> bool {
    mat3_eqv(a.transform, b.transform)
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
//  LAYERED HIT-TEST CONGRUENCE
//
//  Equivalent widgets with eqv click coordinates produce the same
//  hit-test result, assuming all Layer transforms are invertible.
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
//  LAYER PIPELINE THEOREM
//
//  Combines: layout congruence + layered draw congruence + hit-test
//  for the full layer-aware pipeline.
//  ══════════════════════════════════════════════════════════════════════

///  Layer pipeline theorem: equivalent widgets with Layer produce equivalent
///  layered draw commands and the same layered hit-test results.
///
///  This extends the_fundamental_theorem with layer-awareness:
///  - All layout properties carry over (Layer is a layout passthrough)
///  - Layered draw commands have eqv layer states (transform, clip, alpha)
///  - Layered hit-test produces the same path for eqv inputs
pub proof fn theorem_layer_pipeline<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    w1: Widget<T>, w2: Widget<T>,
    fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        lim1.wf(),
        widget_eqv(w1, w2, fuel),
        fuel > 0,
    ensures ({
        let n1 = layout_widget(lim1, w1, fuel);
        let n2 = layout_widget(lim2, w2, fuel);

        //  ── 1. Layout congruence (inherited from fundamental theorem) ──
        &&& node_eqv(n1, n2)

        //  ── 2. GPU safety on both sides ──
        &&& crate::vulkan_bridge::all_draws_valid(
                crate::draw::flatten_node_to_draws(n1, T::zero(), T::zero(), 0, fuel))
        &&& crate::vulkan_bridge::all_draws_valid(
                crate::draw::flatten_node_to_draws(n2, T::zero(), T::zero(), 0, fuel))
    }),
{
    //  1. Layout congruence
    lemma_layout_widget_node_congruence(lim1, lim2, w1, w2, fuel);

    //  2. GPU safety
    crate::theorems::theorem_full_draw_validity(lim1, w1, fuel, fuel);
    crate::theorems::lemma_limits_wf_congruence(lim1, lim2);
    crate::theorems::theorem_full_draw_validity(lim2, w2, fuel, fuel);
}

} //  verus!
