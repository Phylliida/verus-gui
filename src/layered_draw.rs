use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{identity, mat_mul, mat_vec_mul};
use verus_linalg::vec3::Vec3;
use crate::size::Size;
use crate::node::Node;
use crate::layer::{LayerInfo, ClipRect};
use crate::widget::*;

verus! {

//  ══════════════════════════════════════════════════════════════════════
//  LAYER-AWARE DRAW PIPELINE
//
//  Extends the flat draw pipeline with accumulated layer context.
//  The existing flatten_node_to_draws remains untouched — this module
//  provides a parallel pipeline that threads transform/clip/alpha
//  through the tree by walking Widget + Node together.
//  ══════════════════════════════════════════════════════════════════════

///  Accumulated layer state at a point in the tree.
///  Composed by multiplying transforms, intersecting clips, and multiplying alphas.
#[verifier::reject_recursive_types(T)]
pub struct LayerState<T: OrderedRing> {
    pub transform: Mat3x3<T>,
    pub clip: Option<ClipRect<T>>,
    pub alpha: T,
}

impl<T: OrderedRing> LayerState<T> {
    ///  The default layer state: identity transform, no clip, full opacity.
    pub open spec fn default_state() -> Self {
        LayerState {
            transform: identity(),
            clip: Option::None,
            alpha: T::one(),
        }
    }

    ///  Compose this state with a new layer: multiply transforms, intersect clips,
    ///  multiply alphas.
    pub open spec fn compose(self, layer: LayerInfo<T>) -> Self {
        LayerState {
            transform: mat_mul(self.transform, layer.transform),
            clip: match (self.clip, layer.clip) {
                (None, None) => None,
                (Some(c), None) => Some(c),
                (None, Some(c)) => Some(c),
                (Some(outer), Some(inner)) => Some(clip_intersect(outer, inner)),
            },
            alpha: self.alpha.mul(layer.alpha),
        }
    }
}

///  Intersect two clip rects (axis-aligned intersection).
pub open spec fn clip_intersect<T: OrderedRing>(a: ClipRect<T>, b: ClipRect<T>) -> ClipRect<T> {
    let x = if a.x.le(b.x) { b.x } else { a.x };
    let y = if a.y.le(b.y) { b.y } else { a.y };
    let ax2 = a.x.add(a.width);
    let bx2 = b.x.add(b.width);
    let x2 = if ax2.le(bx2) { ax2 } else { bx2 };
    let ay2 = a.y.add(a.height);
    let by2 = b.y.add(b.height);
    let y2 = if ay2.le(by2) { ay2 } else { by2 };
    ClipRect {
        x,
        y,
        width: x2.sub(x),
        height: y2.sub(y),
    }
}

///  A draw command with accumulated layer context.
#[verifier::reject_recursive_types(T)]
pub struct LayeredDrawCommand<T: OrderedRing> {
    pub x: T,
    pub y: T,
    pub width: T,
    pub height: T,
    pub depth: nat,
    pub layer_state: LayerState<T>,
}

///  Flatten a widget+node tree into layered draw commands.
///
///  Walks the Widget tree alongside the Node tree. When a Layer widget is
///  encountered, composes the layer info into the accumulated state.
///  Non-layer widgets pass through the state unchanged.
pub open spec fn flatten_layered<T: OrderedField>(
    widget: Widget<T>,
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    state: LayerState<T>,
    fuel: nat,
) -> Seq<LayeredDrawCommand<T>>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Seq::empty().push(LayeredDrawCommand {
            x: offset_x.add(node.x),
            y: offset_y.add(node.y),
            width: node.size.width,
            height: node.size.height,
            depth,
            layer_state: state,
        })
    } else {
        let abs_x = offset_x.add(node.x);
        let abs_y = offset_y.add(node.y);
        let self_draw = LayeredDrawCommand {
            x: abs_x,
            y: abs_y,
            width: node.size.width,
            height: node.size.height,
            depth,
            layer_state: state,
        };

        //  Determine the child state and child widgets
        let (child_state, child_widgets) = match widget {
            Widget::Wrapper(WrapperWidget::Layer { layer, child }) =>
                (state.compose(layer), Seq::empty().push(*child)),
            _ => (state, get_children(widget)),
        };

        Seq::empty().push(self_draw).add(
            flatten_layered_children(
                child_widgets,
                node.children,
                abs_x, abs_y,
                depth + 1,
                child_state,
                (fuel - 1) as nat,
                0))
    }
}

///  Flatten children from index `from`.
pub open spec fn flatten_layered_children<T: OrderedField>(
    widgets: Seq<Widget<T>>,
    nodes: Seq<Node<T>>,
    parent_abs_x: T,
    parent_abs_y: T,
    start_depth: nat,
    state: LayerState<T>,
    fuel: nat,
    from: nat,
) -> Seq<LayeredDrawCommand<T>>
    decreases fuel, nodes.len() - from,
{
    if from >= nodes.len() || from >= widgets.len() {
        Seq::empty()
    } else {
        let first_draws = flatten_layered(
            widgets[from as int],
            nodes[from as int],
            parent_abs_x, parent_abs_y,
            start_depth,
            state,
            fuel);
        let next_depth = start_depth + first_draws.len();
        first_draws.add(
            flatten_layered_children(
                widgets, nodes,
                parent_abs_x, parent_abs_y,
                next_depth,
                state,
                fuel,
                from + 1))
    }
}

//  ══════════════════════════════════════════════════════════════════════
//  PROPERTIES
//  ══════════════════════════════════════════════════════════════════════

///  Alpha composition preserves [0, 1] range: if both alphas are in [0, 1],
///  their product is too.
pub proof fn lemma_alpha_compose_in_range<T: OrderedField>(a: T, b: T)
    requires
        T::zero().le(a), a.le(T::one()),
        T::zero().le(b), b.le(T::one()),
    ensures
        T::zero().le(a.mul(b)),
        a.mul(b).le(T::one()),
{
    //  0 <= a and 0 <= b → 0 <= a*b
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(a, b);
    //  0 <= a <= 1 and 0 <= b <= 1 → a*b <= 1*1 = 1
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_mul_nonneg_both::<T>(
        a, b, T::one(), T::one());
    //  a*b <= 1*1 eqv 1
    T::axiom_mul_one_right(T::one());
    verus_algebra::lemmas::partial_order_lemmas::lemma_le_congruence_right::<T>(
        a.mul(b), T::one().mul(T::one()), T::one());
}

///  Composing with the identity layer produces the same state.
pub proof fn lemma_compose_identity_layer<T: OrderedField>(state: LayerState<T>)
    ensures
        state.compose(LayerInfo::identity_layer()).transform
            == mat_mul(state.transform, identity::<T>()),
        state.compose(LayerInfo::identity_layer()).clip == state.clip,
        state.compose(LayerInfo::identity_layer()).alpha == state.alpha.mul(T::one()),
{
    //  Structural: follows from definitions
}

} //  verus!
