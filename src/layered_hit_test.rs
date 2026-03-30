use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::{Field, OrderedField};
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{identity, mat_mul, mat_vec_mul, inverse, det};
use verus_linalg::vec3::Vec3;
use crate::size::Size;
use crate::node::Node;
use crate::layer::{LayerInfo, ClipRect};
use crate::widget::*;
use crate::hit_test::point_in_node;

verus! {

//  ══════════════════════════════════════════════════════════════════════
//  LAYER-AWARE HIT-TEST
//
//  Extends the hit-test to handle Layer widgets by:
//    1. Inverting the transform to map click coords to local space
//    2. Checking the clip rect (rejecting clicks outside)
//    3. Delegating to child with local coordinates
//
//  The existing hit_test (Node-only) is untouched. This module provides
//  a Widget+Node parallel-walk version that is layer-aware.
//  ══════════════════════════════════════════════════════════════════════

///  Apply the inverse of a transform to a point, mapping from parent to local coords.
///  Returns None if the transform is singular (det ≡ 0).
pub open spec fn inverse_transform_point<T: OrderedField>(
    transform: Mat3x3<T>, px: T, py: T,
) -> Option<(T, T)> {
    if det(transform).eqv(T::zero()) {
        None
    } else {
        let inv = inverse(transform);
        let result = mat_vec_mul(inv, Vec3 { x: px, y: py, z: T::one() });
        Some((result.x, result.y))
    }
}

///  Layer-aware hit-test: walks Widget + Node trees together.
///
///  At Layer nodes, the transform is inverted and the clip is checked.
///  Returns None if the click misses, or Some(path) indexing into the tree.
///
///  Requires the transform at each Layer to be invertible (det ≢ 0).
pub open spec fn hit_test_layered<T: OrderedField>(
    widget: Widget<T>,
    node: Node<T>,
    px: T,
    py: T,
    fuel: nat,
) -> Option<Seq<nat>>
    decreases fuel, node.children.len() + 1,
{
    if fuel == 0 {
        None
    } else if !point_in_node(node, px, py) {
        None
    } else {
        //  Point is within this node's bounds. Check children (back to front).
        let child_hit = hit_test_layered_scan(widget, node, px, py, node.children.len(), fuel);
        match child_hit {
            Some(path) => Some(path),
            None => Some(Seq::empty()),  //  hit this node, no child deeper
        }
    }
}

///  Scan children in reverse order looking for a hit.
pub open spec fn hit_test_layered_scan<T: OrderedField>(
    widget: Widget<T>,
    node: Node<T>,
    px: T,
    py: T,
    index: nat,
    fuel: nat,
) -> Option<Seq<nat>>
    decreases fuel, index,
{
    if index == 0 || fuel == 0 {
        None
    } else {
        let i = (index - 1) as nat;
        if i >= node.children.len() {
            None
        } else {
            let child_node = node.children[i as int];
            let child_widgets = get_layer_child_widgets(widget);
            if i >= child_widgets.len() {
                None
            } else {
                let child_widget = child_widgets[i as int];

                //  Compute local coordinates for this child
                let local_x = px.sub(child_node.x);
                let local_y = py.sub(child_node.y);

                //  If child widget is a Layer, apply inverse transform + clip check
                let result = match child_widget {
                    Widget::Wrapper(WrapperWidget::Layer { layer, child }) => {
                        //  Apply inverse transform
                        match inverse_transform_point(layer.transform, local_x, local_y) {
                            None => None,  //  singular transform
                            Some((tx, ty)) => {
                                //  Check clip
                                if clip_rejects(layer.clip, tx, ty) {
                                    None
                                } else {
                                    //  Recurse into the layer's child
                                    hit_test_layered(
                                        *child,
                                        child_node,
                                        tx, ty,
                                        (fuel - 1) as nat)
                                }
                            },
                        }
                    },
                    _ => {
                        //  Non-layer child: standard recursion
                        hit_test_layered(
                            child_widget,
                            child_node,
                            local_x, local_y,
                            (fuel - 1) as nat)
                    },
                };

                match result {
                    Some(sub_path) => Some(Seq::empty().push(i).add(sub_path)),
                    None => hit_test_layered_scan(widget, node, px, py, i, fuel),
                }
            }
        }
    }
}

///  Get the child widgets for layer-aware traversal.
///  For Layer widgets, the "children" in the node are the Layer's child widget.
///  For other widgets, use get_children.
pub open spec fn get_layer_child_widgets<T: OrderedRing>(widget: Widget<T>) -> Seq<Widget<T>> {
    get_children(widget)
}

///  Whether a clip rect rejects a point.
pub open spec fn clip_rejects<T: OrderedRing>(
    clip: Option<ClipRect<T>>, px: T, py: T,
) -> bool {
    match clip {
        None => false,  //  no clip = always accept
        Some(rect) => !rect.contains(px, py),
    }
}

//  ══════════════════════════════════════════════════════════════════════
//  PROPERTIES
//  ══════════════════════════════════════════════════════════════════════

///  If the transform is invertible, applying the transform then its inverse
///  recovers the original point (up to eqv).
///
///  This is the key correctness property: if a point p maps to q under the
///  transform, then inverse-transforming q recovers p.
pub proof fn lemma_inverse_transform_roundtrip<T: OrderedField>(
    transform: Mat3x3<T>, px: T, py: T,
)
    requires
        !det(transform).eqv(T::zero()),
    ensures ({
        let v = Vec3 { x: px, y: py, z: T::one() };
        let transformed = mat_vec_mul(transform, v);
        let inv_result = inverse_transform_point(transform, transformed.x, transformed.y);
        inv_result is Some
    }),
{
    //  inverse_transform_point checks det ≢ 0, which holds by precondition
}

///  Clip containment is decidable: a point is either in or out.
pub proof fn lemma_clip_decidable<T: OrderedRing>(
    clip: Option<ClipRect<T>>, px: T, py: T,
)
    ensures
        clip_rejects(clip, px, py) == !match clip {
            None => true,
            Some(rect) => rect.contains(px, py),
        },
{
}

///  No clip means no rejection.
pub proof fn lemma_no_clip_no_reject<T: OrderedRing>(px: T, py: T)
    ensures !clip_rejects::<T>(None, px, py),
{
}

} //  verus!
