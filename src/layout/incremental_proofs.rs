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

// ── Theorem 6: Sufficient fuel implies convergence ──────────────

/// Helper: max_child_widget_depth(children, fuel, count) >= widget_depth(children[i], fuel)
/// for all i < count.
proof fn lemma_max_child_depth_bound<T: OrderedRing>(
    children: Seq<Widget<T>>,
    fuel: nat,
    count: nat,
    i: int,
)
    requires
        0 <= i < count,
        count <= children.len(),
    ensures
        max_child_widget_depth(children, fuel, count) >= widget_depth(children[i], fuel),
    decreases count,
{
    if count == 0 {
        // impossible since i < count
    } else if i == (count - 1) as int {
        // widget_depth(children[count-1], fuel) is the cur value
        // max_child_depth = max(prev, cur) >= cur
    } else {
        // i < count - 1, so by IH, prev >= widget_depth(children[i], fuel)
        lemma_max_child_depth_bound::<T>(children, fuel, (count - 1) as nat, i);
        // max_child_depth = max(prev, cur) >= prev >= widget_depth(children[i], fuel)
    }
}

/// If fuel > widget_depth(widget, fuel), then widget_converged(widget, fuel).
///
/// The widget_depth function computes the tree depth within the given fuel budget.
/// When fuel exceeds this depth, all subtrees are fully resolved and the widget
/// has converged.
pub proof fn lemma_sufficient_fuel_converges<T: OrderedRing>(
    widget: Widget<T>,
    fuel: nat,
)
    requires
        fuel > widget_depth(widget, fuel),
    ensures
        widget_converged(widget, fuel),
    decreases fuel,
{
    // fuel > widget_depth >= 0, so fuel >= 1
    let children = get_children(widget);
    if children.len() == 0 {
        // Leaf-like: widget_converged = true for fuel >= 1
    } else {
        // widget_depth(widget, fuel) = 1 + max_child_widget_depth(children, fuel-1, children.len())
        // So fuel > 1 + max_child_depth, i.e., fuel - 1 > max_child_depth
        let max_child_depth = max_child_widget_depth(children, (fuel - 1) as nat, children.len());
        assert forall|i: int| 0 <= i < children.len() implies
            widget_converged(children[i], (fuel - 1) as nat)
        by {
            // max_child_depth >= widget_depth(children[i], fuel-1) by helper
            lemma_max_child_depth_bound::<T>(
                children, (fuel - 1) as nat, children.len() as nat, i,
            );
            // fuel - 1 > max_child_depth >= widget_depth(children[i], fuel-1)
            // By IH: widget_converged(children[i], fuel-1)
            lemma_sufficient_fuel_converges::<T>(children[i], (fuel - 1) as nat);
        };
    }
}

// ── Theorem 7: Fuel-independent layout ──────────────────────────

/// If both fuel1 and fuel2 exceed the widget's depth, the layout results are
/// identical — the layout is independent of fuel choice once sufficient.
///
/// Combines `lemma_sufficient_fuel_converges` and `lemma_converged_layout_stable`
/// into a single easy-to-use theorem.
pub proof fn lemma_layout_stable_beyond_depth<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        fuel1 > widget_depth(widget, fuel1),
        fuel2 > widget_depth(widget, fuel2),
    ensures
        layout_widget(limits, widget, fuel1) === layout_widget(limits, widget, fuel2),
{
    // Both fuels are sufficient → both have converged
    lemma_sufficient_fuel_converges::<T>(widget, fuel1);
    lemma_sufficient_fuel_converges::<T>(widget, fuel2);
    // widget_converged(widget, fuel1) and widget_converged(widget, fuel2)

    if fuel1 <= fuel2 {
        // fuel2 >= fuel1, converged at fuel1 → same layout
        lemma_converged_layout_stable(limits, widget, fuel1, fuel2);
    } else {
        // fuel1 > fuel2, converged at fuel2 → same layout
        lemma_converged_layout_stable(limits, widget, fuel2, fuel1);
    }
}

} // verus!
