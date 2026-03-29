use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use crate::size::Size;

verus! {

///  A positioned, sized box in the layout tree.
///
///  Coordinates (x, y) are relative to the parent node.
pub struct Node<T: OrderedRing> {
    pub x: T,
    pub y: T,
    pub size: Size<T>,
    pub children: Seq<Node<T>>,
}

impl<T: OrderedRing> Node<T> {
    ///  A leaf node at a given position with a given size.
    pub open spec fn leaf(x: T, y: T, size: Size<T>) -> Self {
        Node { x, y, size, children: Seq::empty() }
    }

    ///  The right edge: x + width.
    pub open spec fn right(self) -> T {
        self.x.add(self.size.width)
    }

    ///  The bottom edge: y + height.
    pub open spec fn bottom(self) -> T {
        self.y.add(self.size.height)
    }

    ///  Whether all children are positioned within the parent's bounds.
    ///  child.x >= 0, child.y >= 0, child.right() <= width, child.bottom() <= height.
    pub open spec fn children_within_bounds(self) -> bool {
        forall|i: int| 0 <= i < self.children.len() ==> {
            &&& T::zero().le(self.children[i].x)
            &&& T::zero().le(self.children[i].y)
            &&& self.children[i].right().le(self.size.width)
            &&& self.children[i].bottom().le(self.size.height)
        }
    }
}

} //  verus!
