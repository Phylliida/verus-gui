use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{identity, mat_mul, mat_vec_mul, det};
use verus_linalg::mat3::algebra;
use verus_algebra::traits::equivalence::Equivalence;
use verus_linalg::vec3::Vec3;

verus! {

///  An axis-aligned clip rectangle in local coordinates.
#[verifier::reject_recursive_types(T)]
pub struct ClipRect<T: OrderedRing> {
    pub x: T,
    pub y: T,
    pub width: T,
    pub height: T,
}

impl<T: OrderedRing> ClipRect<T> {
    ///  Whether a point (px, py) is inside this clip rectangle.
    pub open spec fn contains(self, px: T, py: T) -> bool {
        self.x.le(px) && px.le(self.x.add(self.width))
        && self.y.le(py) && py.le(self.y.add(self.height))
    }

    ///  Whether the clip rect has non-negative dimensions.
    pub open spec fn is_valid(self) -> bool {
        T::zero().le(self.width) && T::zero().le(self.height)
    }
}

///  Layer info for rendering composition.
///
///  A layer modifies the visual output of its subtree:
///  - transform: 2D affine transform as a 3x3 matrix (bottom row = [0, 0, 1])
///  - clip: optional clip rectangle in local coordinates
///  - alpha: opacity in [0, 1]
///
///  Layout is unaffected — Layer is a pure visual/interaction modifier.
#[verifier::reject_recursive_types(T)]
pub struct LayerInfo<T: OrderedRing> {
    pub transform: Mat3x3<T>,
    pub clip: Option<ClipRect<T>>,
    pub alpha: T,
}

impl<T: OrderedRing> LayerInfo<T> {
    ///  An identity layer: no transform, no clip, full opacity.
    pub open spec fn identity_layer() -> Self {
        LayerInfo {
            transform: identity(),
            clip: Option::None,
            alpha: T::one(),
        }
    }

    ///  Apply the transform to a 2D point (x, y) via homogeneous coordinates.
    ///  Maps (x, y) -> (result.x / result.z, result.y / result.z) but
    ///  for affine transforms result.z == 1, so just (result.x, result.y).
    pub open spec fn apply_transform(self, x: T, y: T) -> (T, T) {
        let v = Vec3 { x, y, z: T::one() };
        let result = mat_vec_mul(self.transform, v);
        (result.x, result.y)
    }
}

//  ── Equivalence predicates ──────────────────────────────────────────

///  Two clip rects are field-wise eqv.
pub open spec fn clip_rect_eqv<T: OrderedRing>(a: ClipRect<T>, b: ClipRect<T>) -> bool {
    a.x.eqv(b.x) && a.y.eqv(b.y) && a.width.eqv(b.width) && a.height.eqv(b.height)
}

///  Two optional clip rects are eqv (None == None, Some eqv Some).
pub open spec fn opt_clip_eqv<T: OrderedRing>(
    a: Option<ClipRect<T>>, b: Option<ClipRect<T>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(ca), Some(cb)) => clip_rect_eqv(ca, cb),
        _ => false,
    }
}

///  Two LayerInfo are eqv: transform, clip, and alpha all eqv.
///  Uses the Equivalence trait impl on Mat3x3 from verus-linalg.
pub open spec fn layer_info_eqv<T: OrderedRing>(a: LayerInfo<T>, b: LayerInfo<T>) -> bool {
    a.transform.eqv(b.transform)
    && opt_clip_eqv(a.clip, b.clip)
    && a.alpha.eqv(b.alpha)
}

} //  verus!
