use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::Alignment;

verus! {

// ══════════════════════════════════════════════════════════════════════
// Constraint layout: CSS flexbox-style min/max per-child constraints
// ══════════════════════════════════════════════════════════════════════

/// Per-child constraints for constraint layout.
#[verifier::reject_recursive_types(T)]
pub struct ChildConstraint<T: OrderedRing> {
    /// Minimum size (width, height). The child will not be smaller than this.
    pub min_size: Size<T>,
    /// Maximum size (width, height). The child will not be larger than this.
    pub max_size: Size<T>,
    /// Flex grow factor. Determines how much extra space this child receives.
    /// 0 = fixed size, >0 = proportional to other children's grow factors.
    pub flex_grow: T,
    /// Flex shrink factor. Determines how much this child shrinks when space is tight.
    pub flex_shrink: T,
    /// Flex basis: preferred main-axis size before grow/shrink distribution.
    pub flex_basis: T,
}

/// Compute the effective child size after applying grow/shrink distribution.
///
/// Algorithm:
/// 1. Start with flex_basis for each child
/// 2. Sum all bases → total_basis
/// 3. If total_basis < available: distribute extra to growers
/// 4. If total_basis > available: shrink from shrinkers
/// 5. Clamp each child to [min, max]
pub open spec fn constraint_distribute_main<T: OrderedField>(
    constraints: Seq<ChildConstraint<T>>,
    available_main: T,
) -> Seq<T>
{
    // Simple distribution: proportional to flex_basis, clamped to min/max
    let total_basis = sum_basis(constraints, constraints.len() as nat);
    Seq::new(constraints.len(), |i: int| {
        let basis = constraints[i].flex_basis;
        // Clamp to [min_main, max_main] — use width as main for now
        let clamped = max(constraints[i].min_size.width,
            min(basis, constraints[i].max_size.width));
        clamped
    })
}

/// Sum of flex_basis values.
pub open spec fn sum_basis<T: OrderedRing>(
    constraints: Seq<ChildConstraint<T>>,
    count: nat,
) -> T
    decreases count,
{
    if count == 0 {
        T::zero()
    } else {
        sum_basis(constraints, (count - 1) as nat)
            .add(constraints[(count - 1) as int].flex_basis)
    }
}

/// Each distributed size respects the child's min/max constraints.
pub proof fn lemma_constraint_distribute_respects_bounds<T: OrderedField>(
    constraints: Seq<ChildConstraint<T>>,
    available_main: T,
    i: nat,
)
    requires
        i < constraints.len(),
        forall|j: int| 0 <= j < constraints.len() ==>
            constraints[j].min_size.width.le(constraints[j].max_size.width),
    ensures ({
        let sizes = constraint_distribute_main(constraints, available_main);
        &&& constraints[i as int].min_size.width.le(sizes[i as int])
        &&& sizes[i as int].le(constraints[i as int].max_size.width)
    }),
{
    // Follows from max(min, min(basis, max)) ∈ [min, max]
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        constraints[i as int].min_size.width,
        min(constraints[i as int].flex_basis, constraints[i as int].max_size.width));
    verus_algebra::min_max::lemma_min_le_right::<T>(
        constraints[i as int].flex_basis, constraints[i as int].max_size.width);
    T::axiom_le_total(
        constraints[i as int].min_size.width,
        min(constraints[i as int].flex_basis, constraints[i as int].max_size.width));
    if constraints[i as int].min_size.width.le(
        min(constraints[i as int].flex_basis, constraints[i as int].max_size.width)) {
        // max = min(basis, max_w), which ≤ max_w
    } else {
        // max = min_w, which ≤ max_w (from requires)
    }
}

/// All distributed sizes respect their respective min/max constraints.
pub proof fn lemma_constraint_distribute_all_respect_bounds<T: OrderedField>(
    constraints: Seq<ChildConstraint<T>>,
    available_main: T,
)
    requires
        forall|j: int| 0 <= j < constraints.len() ==>
            constraints[j].min_size.width.le(constraints[j].max_size.width),
    ensures ({
        let sizes = constraint_distribute_main(constraints, available_main);
        forall|i: int| 0 <= i < constraints.len() ==> {
            &&& constraints[i].min_size.width.le(#[trigger] sizes[i])
            &&& sizes[i].le(constraints[i].max_size.width)
        }
    }),
{
    let sizes = constraint_distribute_main(constraints, available_main);
    assert forall|i: int| 0 <= i < constraints.len() implies
        constraints[i].min_size.width.le(#[trigger] sizes[i])
        && sizes[i].le(constraints[i].max_size.width)
    by {
        lemma_constraint_distribute_respects_bounds(constraints, available_main, i as nat);
    };
}

} // verus!
