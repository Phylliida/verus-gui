use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;

verus! {

///  A two-dimensional size with width and height.
pub struct Size<T: OrderedRing> {
    pub width: T,
    pub height: T,
}

impl<T: OrderedRing> Size<T> {
    ///  Construct a size from width and height.
    pub open spec fn new(width: T, height: T) -> Self {
        Size { width, height }
    }

    ///  The zero size.
    pub open spec fn zero_size() -> Self {
        Size { width: T::zero(), height: T::zero() }
    }

    ///  Whether both dimensions are non-negative.
    pub open spec fn is_nonneg(self) -> bool {
        T::zero().le(self.width) && T::zero().le(self.height)
    }

    ///  Component-wise <=: self.width <= other.width && self.height <= other.height.
    pub open spec fn le(self, other: Self) -> bool {
        self.width.le(other.width) && self.height.le(other.height)
    }

    ///  Main-axis dimension: height for Vertical, width for Horizontal.
    pub open spec fn main_dim(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.height,
            crate::layout::Axis::Horizontal => self.width,
        }
    }

    ///  Cross-axis dimension: width for Vertical, height for Horizontal.
    pub open spec fn cross_dim(self, axis: crate::layout::Axis) -> T {
        match axis {
            crate::layout::Axis::Vertical => self.width,
            crate::layout::Axis::Horizontal => self.height,
        }
    }

    ///  Construct a Size from main-axis and cross-axis values.
    pub open spec fn from_axes(axis: crate::layout::Axis, main: T, cross: T) -> Self {
        match axis {
            crate::layout::Axis::Vertical => Size { width: cross, height: main },
            crate::layout::Axis::Horizontal => Size { width: main, height: cross },
        }
    }
}

} //  verus!
