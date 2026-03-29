use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::min_max::{min, max};
use crate::size::Size;

verus! {

///  Size constraints: a minimum and maximum bounding box.
pub struct Limits<T: OrderedRing> {
    pub min: Size<T>,
    pub max: Size<T>,
}

impl<T: OrderedRing> Limits<T> {
    ///  Well-formedness: min <= max component-wise, and both are non-negative.
    pub open spec fn wf(self) -> bool {
        self.min.is_nonneg()
        && self.max.is_nonneg()
        && self.min.width.le(self.max.width)
        && self.min.height.le(self.max.height)
    }

    ///  Clamp a single value between lo and hi: max(lo, min(val, hi)).
    pub open spec fn clamp(val: T, lo: T, hi: T) -> T {
        max::<T>(lo, min::<T>(val, hi))
    }

    ///  Resolve a desired size within these limits by clamping each dimension.
    pub open spec fn resolve(self, size: Size<T>) -> Size<T> {
        Size {
            width: Self::clamp(size.width, self.min.width, self.max.width),
            height: Self::clamp(size.height, self.min.height, self.max.height),
        }
    }

    ///  Intersect two limits: max-of-mins for min, clamp max to be >= the new min.
    pub open spec fn intersect(self, other: Limits<T>) -> Limits<T> {
        let new_min_w = max::<T>(self.min.width, other.min.width);
        let new_min_h = max::<T>(self.min.height, other.min.height);
        Limits {
            min: Size { width: new_min_w, height: new_min_h },
            max: Size {
                width: max::<T>(new_min_w, min::<T>(self.max.width, other.max.width)),
                height: max::<T>(new_min_h, min::<T>(self.max.height, other.max.height)),
            },
        }
    }

    ///  Shrink limits by subtracting padding from the max (keeping min unchanged).
    pub open spec fn shrink(self, width: T, height: T) -> Limits<T> {
        Limits {
            min: self.min,
            max: Size {
                width: max::<T>(self.min.width, self.max.width.sub(width)),
                height: max::<T>(self.min.height, self.max.height.sub(height)),
            },
        }
    }
}

} //  verus!
