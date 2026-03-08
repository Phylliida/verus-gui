use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::widget::*;
use crate::diff::*;
use crate::layout::*;

verus! {

// ── Theorem 1: Fuel convergence stability ────────────────────────

/// Once a widget has converged at fuel1, the layout result is identical
/// for all fuel2 >= fuel1. Generalizes lemma_layout_widget_fuel_monotone
/// (which only proves fuel → fuel+1) to arbitrary fuel gaps.
pub proof fn lemma_converged_layout_stable<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        widget_converged(widget, fuel1),
        fuel2 >= fuel1,
    ensures
        layout_widget(limits, widget, fuel1) === layout_widget(limits, widget, fuel2),
    decreases fuel2 - fuel1,
{
    if fuel1 == fuel2 {
        // Trivially identical
    } else {
        // fuel1 < fuel2: step through fuel1 → fuel1+1 → ... → fuel2
        // widget_converged(widget, fuel1) implies converged at fuel1+1 too
        // (converged is monotone in fuel — more fuel, still converged)
        lemma_converged_monotone(widget, fuel1);
        lemma_layout_widget_fuel_monotone(limits, widget, fuel1);
        // layout(fuel1) == layout(fuel1+1)
        // widget_converged(widget, fuel1+1)
        // By induction: layout(fuel1+1) === layout(fuel2)
        lemma_converged_layout_stable(limits, widget, fuel1 + 1, fuel2);
    }
}

/// Widget convergence is monotone in fuel: converged at fuel implies converged at fuel+1.
proof fn lemma_converged_monotone<T: OrderedRing>(
    widget: Widget<T>,
    fuel: nat,
)
    requires
        widget_converged(widget, fuel),
    ensures
        widget_converged(widget, fuel + 1),
    decreases fuel,
{
    // widget_converged(widget, fuel) implies fuel >= 1
    assert(fuel >= 1nat);
    let children = get_children(widget);
    if children.len() == 0 {
        // Leaf or similar — always converged at fuel >= 1
    } else {
        // All children converged at fuel-1 → converged at fuel
        assert forall|i: int| 0 <= i < children.len() implies
            widget_converged(children[i], fuel)
        by {
            lemma_converged_monotone(children[i], (fuel - 1) as nat);
        }
    }
}

// ── Theorem 2: Subtree independence ─────────────────────────────

/// Changing sibling widgets doesn't affect the j-th child's layout.
/// Since widget_child_nodes(limits, children, fuel)[j] = layout_widget(limits, children[j], fuel),
/// if children1[j] === children2[j], the j-th result is identical.
pub proof fn lemma_sibling_layout_independent<T: OrderedField>(
    limits: Limits<T>,
    children1: Seq<Widget<T>>,
    children2: Seq<Widget<T>>,
    fuel: nat,
    j: int,
)
    requires
        children1.len() == children2.len(),
        0 <= j < children1.len(),
        children1[j] === children2[j],
    ensures
        widget_child_nodes(limits, children1, fuel)[j]
            === widget_child_nodes(limits, children2, fuel)[j],
{
    // widget_child_nodes = Seq::new(n, |i| layout_widget(limits, children[i], fuel))
    // By Seq::new indexing: result[j] = layout_widget(limits, children[j], fuel)
    // Since children1[j] === children2[j], both sides are identical.
}

// ── Theorem 3: Monotone change propagation ──────────────────────

/// If one child's height grows, the column's content height grows.
/// If child sizes are pointwise monotone (sizes1[i].height ≤ sizes2[i].height),
/// then column_content_height(sizes1, spacing) ≤ column_content_height(sizes2, spacing).
pub proof fn lemma_column_single_child_change_monotone<T: OrderedRing>(
    sizes1: Seq<Size<T>>,
    sizes2: Seq<Size<T>>,
    spacing: T,
)
    requires
        sizes1.len() == sizes2.len(),
        forall|i: int| 0 <= i < sizes1.len() ==>
            sizes1[i].height.le(sizes2[i].height),
    ensures
        column_content_height(sizes1, spacing).le(column_content_height(sizes2, spacing)),
{
    // column_content_height = sum_heights + (n-1)*spacing
    // sum_heights pointwise monotone (already proved in proofs.rs)
    super::proofs::lemma_sum_heights_pointwise_monotone::<T>(sizes1, sizes2, sizes1.len() as nat);
    // Both have same spacing term → content_h1 ≤ content_h2
    if sizes1.len() > 0 {
        T::axiom_le_add_monotone(
            sum_heights(sizes1, sizes1.len() as nat),
            sum_heights(sizes2, sizes2.len() as nat),
            repeated_add(spacing, (sizes1.len() - 1) as nat),
        );
    }
}

// ── Theorem 4: Diff-layout correspondence ───────────────────────

/// If diff_nodes says Same (with fuel > 0), the nodes are deeply equivalent.
/// Convenience wrapper around lemma_diff_same_implies_deeply_eqv.
pub proof fn lemma_same_diff_reusable<T: OrderedRing>(
    old: Node<T>,
    new: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        diff_nodes(old, new, fuel) === DiffResult::Same,
    ensures
        nodes_deeply_eqv(old, new, (fuel - 1) as nat),
{
    lemma_diff_same_implies_deeply_eqv(old, new, fuel);
}

// ── Theorem 5: Diff converged stability ──────────────────────────

/// If a widget has converged at fuel1, then the layouts at fuel1 and fuel2
/// (≥ fuel1) produce identical nodes, hence diff returns Same.
pub proof fn lemma_diff_converged_stability<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        fuel1 > 0,
        fuel2 >= fuel1,
        widget_converged(widget, fuel1),
    ensures
        diff_nodes(
            layout_widget(limits, widget, fuel1),
            layout_widget(limits, widget, fuel2),
            fuel1,
        ) === DiffResult::<T>::Same,
{
    // Converged implies identical layout
    lemma_converged_layout_stable(limits, widget, fuel1, fuel2);
    // layout(fuel1) === layout(fuel2), so diff is reflexive
    lemma_diff_reflexive(layout_widget(limits, widget, fuel1), fuel1);
}

} // verus!
