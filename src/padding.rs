use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;

verus! {

/// Padding around the four edges of a box.
pub struct Padding<T: OrderedRing> {
    pub top: T,
    pub right: T,
    pub bottom: T,
    pub left: T,
}

impl<T: OrderedRing> Padding<T> {
    /// Uniform padding on all sides.
    pub open spec fn uniform(val: T) -> Self {
        Padding { top: val, right: val, bottom: val, left: val }
    }

    /// Zero padding.
    pub open spec fn zero_padding() -> Self {
        Self::uniform(T::zero())
    }

    /// Total horizontal padding (left + right).
    pub open spec fn horizontal(self) -> T {
        self.left.add(self.right)
    }

    /// Total vertical padding (top + bottom).
    pub open spec fn vertical(self) -> T {
        self.top.add(self.bottom)
    }

    /// Whether all four values are non-negative.
    pub open spec fn is_nonneg(self) -> bool {
        T::zero().le(self.top)
        && T::zero().le(self.right)
        && T::zero().le(self.bottom)
        && T::zero().le(self.left)
    }
}

} // verus!
