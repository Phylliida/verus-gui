use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;

verus! {

/// Cross-axis alignment strategy.
pub enum Alignment {
    /// Align to the start (left for columns, top for rows).
    Start,
    /// Align to the center. Note: proper centering requires a Field
    /// (division by 2). Over a general OrderedRing this behaves like Start.
    Center,
    /// Align to the end (right for columns, bottom for rows).
    End,
}

/// Compute the cross-axis offset for a child given alignment, available space,
/// and the child's extent along that axis.
///
/// - Start  => 0
/// - Center => 0  (degenerate over OrderedRing; requires Field for true centering)
/// - End    => available - used
pub open spec fn align_offset<T: OrderedRing>(
    alignment: Alignment,
    available: T,
    used: T,
) -> T {
    match alignment {
        Alignment::Start  => T::zero(),
        Alignment::Center => T::zero(),
        Alignment::End    => available.sub(used),
    }
}

} // verus!
