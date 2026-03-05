use vstd::prelude::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::convex::two;

verus! {

/// Cross-axis alignment strategy.
pub enum Alignment {
    /// Align to the start (left for columns, top for rows).
    Start,
    /// Align to the center: (available - used) / 2.
    Center,
    /// Align to the end (right for columns, bottom for rows).
    End,
}

/// Compute the cross-axis offset for a child given alignment, available space,
/// and the child's extent along that axis.
///
/// - Start  => 0
/// - Center => (available - used) / 2
/// - End    => available - used
pub open spec fn align_offset<T: OrderedField>(
    alignment: Alignment,
    available: T,
    used: T,
) -> T {
    match alignment {
        Alignment::Start  => T::zero(),
        Alignment::Center => available.sub(used).div(two::<T>()),
        Alignment::End    => available.sub(used),
    }
}

} // verus!
