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

    /// Total main-axis padding: vertical() for Vertical, horizontal() for Horizontal.
    pub open spec fn main_padding(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.vertical(),
            crate::layout::Axis::Horizontal => self.horizontal(),
        }
    }

    /// Total cross-axis padding: horizontal() for Vertical, vertical() for Horizontal.
    pub open spec fn cross_padding(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.horizontal(),
            crate::layout::Axis::Horizontal => self.vertical(),
        }
    }

    /// Main-axis start padding: top for Vertical, left for Horizontal.
    pub open spec fn main_start(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.top,
            crate::layout::Axis::Horizontal => self.left,
        }
    }

    /// Cross-axis start padding: left for Vertical, top for Horizontal.
    pub open spec fn cross_start(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.left,
            crate::layout::Axis::Horizontal => self.top,
        }
    }
}

} // verus!
