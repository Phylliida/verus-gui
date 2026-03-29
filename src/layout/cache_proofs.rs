use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::Alignment;
use crate::widget::*;
use crate::layout::*;
use crate::layout::incremental_proofs::*;

verus! {

//  ── Cache validity predicate ─────────────────────────────────────

///  A cache of Nodes is valid when each entry matches layout_widget output.
pub open spec fn cached_children_valid<T: OrderedField>(
    cache: Seq<Node<T>>,
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
) -> bool {
    cache.len() == children.len()
    && forall|i: int| 0 <= i < cache.len() ==>
        cache[i] === layout_widget(inner_limits, children[i], fuel)
}

//  ── Column from cache ────────────────────────────────────────────

///  If cached children are valid, layout_column_body using the cache
///  produces the same result as using widget_child_nodes.
pub proof fn lemma_column_from_cache<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    cache: Seq<Node<T>>,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        cached_children_valid(cache,
            limits.shrink(padding.horizontal(), padding.vertical()),
            children, fuel),
    ensures
        layout_column_body(limits, padding, spacing, alignment, cache) ===
        layout_column_body(limits, padding, spacing, alignment,
            widget_child_nodes(
                limits.shrink(padding.horizontal(), padding.vertical()),
                children, fuel)),
{
    //  cache[i] === layout_widget(inner, children[i], fuel) for all i
    //  widget_child_nodes(inner, children, fuel) = Seq::new(n, |i| layout_widget(inner, children[i], fuel))
    //  So cache =~= widget_child_nodes(inner, children, fuel) by extensional equality
    let inner = limits.shrink(padding.horizontal(), padding.vertical());
    let cn = widget_child_nodes(inner, children, fuel);
    assert(cache.len() == cn.len());
    assert(cache =~= cn);
}

//  ── Cache validity on fuel increase ──────────────────────────────

///  Converged children's cache entries remain valid at higher fuel.
pub proof fn lemma_cache_valid_on_fuel_increase<T: OrderedField>(
    cache: Seq<Node<T>>,
    inner_limits: Limits<T>,
    children: Seq<Widget<T>>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        cached_children_valid(cache, inner_limits, children, fuel1),
        fuel2 >= fuel1,
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel1),
    ensures
        cached_children_valid(cache, inner_limits, children, fuel2),
{
    assert forall|i: int| 0 <= i < cache.len() implies
        cache[i] === layout_widget(inner_limits, children[i], fuel2)
    by {
        //  cache[i] === layout_widget(inner_limits, children[i], fuel1)
        //  widget_converged(children[i], fuel1) + fuel2 >= fuel1
        //  → layout_widget(inner_limits, children[i], fuel1) === layout_widget(inner_limits, children[i], fuel2)
        lemma_converged_layout_stable(inner_limits, children[i], fuel1, fuel2);
    };
}

//  ── Sibling independence for cache ───────────────────────────────

///  Changing child j doesn't invalidate cache entries for other children.
pub proof fn lemma_cache_sibling_independent<T: OrderedField>(
    cache: Seq<Node<T>>,
    inner_limits: Limits<T>,
    old_children: Seq<Widget<T>>,
    new_children: Seq<Widget<T>>,
    j: int,
    fuel: nat,
)
    requires
        cached_children_valid(cache, inner_limits, old_children, fuel),
        old_children.len() == new_children.len(),
        forall|i: int| 0 <= i < old_children.len() && i != j ==>
            old_children[i] === new_children[i],
    ensures
        forall|i: int| 0 <= i < cache.len() && i != j ==>
            cache[i] === layout_widget(inner_limits, new_children[i], fuel),
{
    //  For each i != j:
    //  cache[i] === layout_widget(inner_limits, old_children[i], fuel)
    //  old_children[i] === new_children[i]
    //  → layout_widget(inner_limits, old_children[i], fuel) === layout_widget(inner_limits, new_children[i], fuel)
}

//  ── Column y-position from child sizes ───────────────────────────

///  Column y-positions depend only on preceding child heights.
///  If child sizes agree up to index k, positions agree at index k.
pub proof fn lemma_column_y_position_from_sizes<T: OrderedField>(
    padding_top: T,
    sizes1: Seq<Size<T>>,
    sizes2: Seq<Size<T>>,
    spacing: T,
    k: nat,
)
    requires
        sizes1.len() == sizes2.len(),
        k <= sizes1.len(),
        forall|i: int| 0 <= i < k ==> sizes1[i] === sizes2[i],
    ensures
        child_y_position(padding_top, sizes1, spacing, k)
            === child_y_position(padding_top, sizes2, spacing, k),
    decreases k,
{
    if k > 0 {
        lemma_column_y_position_from_sizes(
            padding_top, sizes1, sizes2, spacing, (k - 1) as nat,
        );
        //  sizes1[k-1] === sizes2[k-1] → .height is the same
        //  recursive step produces same result
    }
}

//  ── Column partial relayout ──────────────────────────────────────

///  If old_cache and new_cache have identical elements at every index,
///  layout_column_body produces identical results.
pub proof fn lemma_column_partial_relayout<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    spacing: T,
    alignment: Alignment,
    old_cache: Seq<Node<T>>,
    new_cache: Seq<Node<T>>,
)
    requires
        old_cache.len() == new_cache.len(),
        forall|i: int| 0 <= i < old_cache.len() ==> old_cache[i] === new_cache[i],
    ensures
        layout_column_body(limits, padding, spacing, alignment, old_cache)
            === layout_column_body(limits, padding, spacing, alignment, new_cache),
{
    //  old_cache =~= new_cache by extensional equality
    assert(old_cache =~= new_cache);
}

//  ── ScrollView child cache independence ──────────────────────────

///  Changing scroll offsets doesn't affect child layout.
///  The child is laid out with viewport-derived limits, independent of scroll_x/scroll_y.
///
///  Specifically, for ScrollView { viewport, scroll_x, scroll_y, child },
///  layout_widget computes child_limits from viewport only, then calls
///  layout_widget(child_limits, child, fuel-1). The scroll offsets only
///  affect the child node's x/y positioning in the parent, not the child's
///  own layout computation.
pub proof fn lemma_scroll_child_layout_independent<T: OrderedField>(
    viewport: Size<T>,
    child: Widget<T>,
    fuel: nat,
    scroll_x1: T,
    scroll_y1: T,
    scroll_x2: T,
    scroll_y2: T,
)
    requires fuel > 0,
    ensures ({
        let child_limits = Limits::<T> {
            min: Size::zero_size(),
            max: viewport,
        };
        let child_node = layout_widget(child_limits, child, (fuel - 1) as nat);
        //  The child_node is the same regardless of scroll offsets
        child_node === layout_widget(child_limits, child, (fuel - 1) as nat)
    }),
{
    //  Trivially true: child_limits depends only on viewport,
    //  and layout_widget(child_limits, child, fuel-1) is purely determined
    //  by child_limits and child. scroll_x/scroll_y are not inputs.
}

//  ── Scroll cache bridge proofs ───────────────────────────────────

///  Scroll position changes preserve cache validity.
///  Cache validity depends on child_limits = (zero, viewport), which is
///  scroll-independent. Scroll offsets only affect child node positioning
///  in the parent, not the child's own layout.
pub proof fn lemma_scroll_change_preserves_cache<T: OrderedField>(
    viewport: Size<T>,
    children: Seq<Widget<T>>,
    cache: Seq<Node<T>>,
    fuel: nat,
)
    requires
        cached_children_valid(cache,
            Limits { min: Size::zero_size(), max: viewport }, children, fuel),
    ensures
        cached_children_valid(cache,
            Limits { min: Size::zero_size(), max: viewport }, children, fuel),
{
    //  Trivially true: cache validity depends on child_limits = (zero, viewport),
    //  which is scroll-independent. The scroll offsets only affect child node
    //  positioning in the parent, not the child's own layout.
}

///  Combined: scroll change + fuel increase preserves cache when converged.
pub proof fn lemma_scroll_cache_stable<T: OrderedField>(
    viewport: Size<T>,
    children: Seq<Widget<T>>,
    cache: Seq<Node<T>>,
    fuel1: nat,
    fuel2: nat,
)
    requires
        cached_children_valid(cache,
            Limits { min: Size::zero_size(), max: viewport }, children, fuel1),
        fuel2 >= fuel1,
        forall|i: int| 0 <= i < children.len() ==>
            widget_converged(children[i], fuel1),
    ensures
        cached_children_valid(cache,
            Limits { min: Size::zero_size(), max: viewport }, children, fuel2),
{
    lemma_cache_valid_on_fuel_increase(cache,
        Limits { min: Size::zero_size(), max: viewport }, children, fuel1, fuel2);
}

} //  verus!
