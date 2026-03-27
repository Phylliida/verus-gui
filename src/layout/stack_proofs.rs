use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::*;
use crate::size::Size;
use crate::layout::stack::*;
use crate::layout::proofs::{
    lemma_align_offset_nonneg, lemma_align_offset_bounded, lemma_le_add_nonneg,
    lemma_nonneg_sum, lemma_add_comm_le, lemma_shrink_wf, lemma_shrink_max_bound,
    lemma_layout_respects_limits, lemma_resolve_ge_input, lemma_stack_children_len,
    lemma_stack_children_element, lemma_merge_layout_cwb,
};
use crate::alignment::{Alignment, align_offset};
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::widget::*;

verus! {

// ── max_width / max_height non-negativity ───────────────────────────

/// max_width is non-negative when all child widths are non-negative.
pub proof fn lemma_max_width_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].width),
    ensures
        T::zero().le(max_width(sizes, n)),
    decreases n,
{
    reveal(max_width);
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_max_width_nonneg(sizes, (n - 1) as nat);
        // max(prev, sizes[n-1].width) >= prev >= 0
        lemma_max_ge_left::<T>(
            max_width(sizes, (n - 1) as nat),
            sizes[(n - 1) as int].width,
        );
        T::axiom_le_transitive(
            T::zero(),
            max_width(sizes, (n - 1) as nat),
            max::<T>(max_width(sizes, (n - 1) as nat), sizes[(n - 1) as int].width),
        );
    }
}

/// max_height is non-negative when all child heights are non-negative.
pub proof fn lemma_max_height_nonneg<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes.len(),
        forall|i: int| 0 <= i < sizes.len() ==> T::zero().le(sizes[i].height),
    ensures
        T::zero().le(max_height(sizes, n)),
    decreases n,
{
    reveal(max_height);
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_max_height_nonneg(sizes, (n - 1) as nat);
        lemma_max_ge_left::<T>(
            max_height(sizes, (n - 1) as nat),
            sizes[(n - 1) as int].height,
        );
        T::axiom_le_transitive(
            T::zero(),
            max_height(sizes, (n - 1) as nat),
            max::<T>(max_height(sizes, (n - 1) as nat), sizes[(n - 1) as int].height),
        );
    }
}

/// The stack content size is non-negative when all children have non-negative sizes.
pub proof fn lemma_stack_content_size_nonneg<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
)
    requires
        forall|i: int| 0 <= i < child_sizes.len() ==> child_sizes[i].is_nonneg(),
    ensures
        stack_content_size(child_sizes).is_nonneg(),
{
    reveal(stack_content_size);
    lemma_max_width_nonneg(child_sizes, child_sizes.len() as nat);
    lemma_max_height_nonneg(child_sizes, child_sizes.len() as nat);
}

// ── max_width / max_height bound each child ─────────────────────────

/// Each child's width is <= max_width.
pub proof fn lemma_max_width_bounds_child<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].width),
    ensures
        sizes[i as int].width.le(max_width(sizes, sizes.len() as nat)),
    decreases sizes.len() - i,
{
    let n = sizes.len() as nat;
    // sizes[i].width <= max_width(sizes, i+1) <= max_width(sizes, n)
    lemma_max_width_contains(sizes, i);
    lemma_max_width_monotone(sizes, (i + 1) as nat, n);
    T::axiom_le_transitive(
        sizes[i as int].width,
        max_width(sizes, (i + 1) as nat),
        max_width(sizes, n),
    );
}

/// max_width(sizes, i+1) >= sizes[i].width (the latest element is in the max).
proof fn lemma_max_width_contains<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
    ensures
        sizes[i as int].width.le(max_width(sizes, (i + 1) as nat)),
{
    reveal(max_width);
    // max_width(sizes, i+1) = max(max_width(sizes, i), sizes[i].width) >= sizes[i].width
    lemma_max_ge_right::<T>(max_width(sizes, i), sizes[i as int].width);
}

/// max_width is monotone: i <= j implies max_width(sizes, i) <= max_width(sizes, j).
proof fn lemma_max_width_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        max_width(sizes, i).le(max_width(sizes, j)),
    decreases j - i,
{
    reveal(max_width);
    if i == j {
        T::axiom_le_reflexive(max_width(sizes, i));
    } else {
        lemma_max_width_monotone(sizes, i, (j - 1) as nat);
        // max_width(j) = max(max_width(j-1), sizes[j-1].width) >= max_width(j-1)
        lemma_max_ge_left::<T>(max_width(sizes, (j - 1) as nat), sizes[(j - 1) as int].width);
        T::axiom_le_transitive(
            max_width(sizes, i),
            max_width(sizes, (j - 1) as nat),
            max_width(sizes, j),
        );
    }
}

/// Each child's height is <= max_height.
pub proof fn lemma_max_height_bounds_child<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
        forall|j: int| 0 <= j < sizes.len() ==> T::zero().le(sizes[j].height),
    ensures
        sizes[i as int].height.le(max_height(sizes, sizes.len() as nat)),
    decreases sizes.len() - i,
{
    let n = sizes.len() as nat;
    lemma_max_height_contains(sizes, i);
    lemma_max_height_monotone(sizes, (i + 1) as nat, n);
    T::axiom_le_transitive(
        sizes[i as int].height,
        max_height(sizes, (i + 1) as nat),
        max_height(sizes, n),
    );
}

/// max_height(sizes, i+1) >= sizes[i].height.
proof fn lemma_max_height_contains<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
)
    requires
        i < sizes.len(),
    ensures
        sizes[i as int].height.le(max_height(sizes, (i + 1) as nat)),
{
    reveal(max_height);
    lemma_max_ge_right::<T>(max_height(sizes, i), sizes[i as int].height);
}

/// max_height is monotone.
proof fn lemma_max_height_monotone<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i <= j,
        j <= sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        max_height(sizes, i).le(max_height(sizes, j)),
    decreases j - i,
{
    reveal(max_height);
    if i == j {
        T::axiom_le_reflexive(max_height(sizes, i));
    } else {
        lemma_max_height_monotone(sizes, i, (j - 1) as nat);
        lemma_max_ge_left::<T>(max_height(sizes, (j - 1) as nat), sizes[(j - 1) as int].height);
        T::axiom_le_transitive(
            max_height(sizes, i),
            max_height(sizes, (j - 1) as nat),
            max_height(sizes, j),
        );
    }
}

// ── Stack child within bounds ───────────────────────────────────────

/// Each child in a stack fits within the available space.
/// Child x-position >= padding_left and child right edge <= padding_left + available_width.
/// Child y-position >= padding_top and child bottom edge <= padding_top + available_height.
pub proof fn lemma_stack_child_within_bounds<T: OrderedField>(
    padding_left: T,
    padding_top: T,
    h_align: Alignment,
    v_align: Alignment,
    available_width: T,
    available_height: T,
    child_width: T,
    child_height: T,
)
    requires
        child_width.le(available_width),
        child_height.le(available_height),
    ensures
        // x lower bound
        padding_left.le(
            padding_left.add(align_offset(h_align, available_width, child_width))
        ),
        // x upper bound
        padding_left.add(align_offset(h_align, available_width, child_width))
            .add(child_width)
            .le(padding_left.add(available_width)),
        // y lower bound
        padding_top.le(
            padding_top.add(align_offset(v_align, available_height, child_height))
        ),
        // y upper bound
        padding_top.add(align_offset(v_align, available_height, child_height))
            .add(child_height)
            .le(padding_top.add(available_height)),
{
    // x bounds: direct from alignment lemmas
    lemma_align_offset_nonneg(h_align, available_width, child_width);
    lemma_le_add_nonneg(padding_left, align_offset(h_align, available_width, child_width));

    crate::layout::proofs::lemma_column_child_x_upper_bound(
        padding_left, h_align, available_width, child_width,
    );

    // y bounds: direct from alignment lemmas
    lemma_align_offset_nonneg(v_align, available_height, child_height);
    lemma_le_add_nonneg(padding_top, align_offset(v_align, available_height, child_height));

    crate::layout::proofs::lemma_row_child_y_upper_bound(
        padding_top, v_align, available_height, child_height,
    );
}

// ── Stack size commutativity ─────────────────────────────────────

/// Swap two elements in a sequence.
pub open spec fn swap_seq<A>(s: Seq<A>, i: nat, j: nat) -> Seq<A> {
    s.update(i as int, s[j as int]).update(j as int, s[i as int])
}

/// max_width(sizes, n) <= bound when every element width <= bound.
proof fn lemma_max_width_upper_bound<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
    bound: T,
)
    requires
        n <= sizes.len(),
        T::zero().le(bound),
        forall|k: int| 0 <= k < n ==> sizes[k].width.le(bound),
    ensures
        max_width(sizes, n).le(bound),
    decreases n,
{
    reveal(max_width);
    if n == 0 {
    } else {
        lemma_max_width_upper_bound(sizes, (n - 1) as nat, bound);
        // max_width(n) = max(max_width(n-1), sizes[n-1].width)
        // max_width(n-1) <= bound, sizes[n-1].width <= bound
        // max(a, b) <= c when a <= c and b <= c
        T::axiom_le_total(max_width(sizes, (n - 1) as nat), sizes[(n - 1) as int].width);
        if max_width(sizes, (n - 1) as nat).le(sizes[(n - 1) as int].width) {
            // max = sizes[n-1].width <= bound
        } else {
            // max = max_width(n-1) <= bound
        }
    }
}

/// Every element of swap_seq is bounded by max_width of the original.
proof fn lemma_swap_elements_bounded_by_max_width<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        forall|k: int| 0 <= k < sizes.len() as int ==>
            swap_seq(sizes, i, j)[k].width.le(
                max_width(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);
    assert forall|k: int| 0 <= k < sizes.len() as int implies
        t[k].width.le(max_width(sizes, n))
    by {
        if k == j as int {
            // t[j] = sizes[i]
            lemma_max_width_bounds_child(sizes, i);
        } else if k == i as int {
            // t[i] = sizes[j]
            lemma_max_width_bounds_child(sizes, j);
        } else {
            // t[k] = sizes[k]
            lemma_max_width_bounds_child(sizes, k as nat);
        }
    }
}

/// Swapping two children doesn't change max_width.
pub proof fn lemma_max_width_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].width),
    ensures
        max_width(swap_seq(sizes, i, j), sizes.len() as nat).eqv(
            max_width(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);

    // Nonneg bounds for upper_bound preconditions
    lemma_max_width_nonneg(sizes, n);
    // t has same elements, so nonneg widths carry over
    assert forall|k: int| 0 <= k < t.len() implies T::zero().le(t[k].width) by {
        if k == i as int { } else if k == j as int { } else { }
    }
    lemma_max_width_nonneg(t, n);

    // Direction 1: max_width(t, n) <= max_width(s, n)
    lemma_swap_elements_bounded_by_max_width(sizes, i, j);
    lemma_max_width_upper_bound(t, n, max_width(sizes, n));

    // Direction 2: max_width(s, n) <= max_width(t, n)
    assert forall|k: int| 0 <= k < n as int implies
        sizes[k].width.le(max_width(t, n))
    by {
        if k == i as int {
            lemma_max_width_bounds_child(t, j);
        } else if k == j as int {
            lemma_max_width_bounds_child(t, i);
        } else {
            lemma_max_width_bounds_child(t, k as nat);
        }
    }
    lemma_max_width_upper_bound(sizes, n, max_width(t, n));

    T::axiom_le_antisymmetric(
        max_width(t, n),
        max_width(sizes, n),
    );
}

/// Every element of swap_seq is bounded by max_height of the original.
proof fn lemma_swap_elements_bounded_by_max_height<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        forall|k: int| 0 <= k < sizes.len() as int ==>
            swap_seq(sizes, i, j)[k].height.le(
                max_height(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);
    assert forall|k: int| 0 <= k < sizes.len() as int implies
        t[k].height.le(max_height(sizes, n))
    by {
        if k == j as int {
            lemma_max_height_bounds_child(sizes, i);
        } else if k == i as int {
            lemma_max_height_bounds_child(sizes, j);
        } else {
            lemma_max_height_bounds_child(sizes, k as nat);
        }
    }
}

/// max_height(sizes, n) <= bound when every element height <= bound.
proof fn lemma_max_height_upper_bound<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    n: nat,
    bound: T,
)
    requires
        n <= sizes.len(),
        T::zero().le(bound),
        forall|k: int| 0 <= k < n ==> sizes[k].height.le(bound),
    ensures
        max_height(sizes, n).le(bound),
    decreases n,
{
    reveal(max_height);
    if n == 0 {
    } else {
        lemma_max_height_upper_bound(sizes, (n - 1) as nat, bound);
        T::axiom_le_total(max_height(sizes, (n - 1) as nat), sizes[(n - 1) as int].height);
    }
}

/// Swapping two children doesn't change max_height.
pub proof fn lemma_max_height_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> T::zero().le(sizes[k].height),
    ensures
        max_height(swap_seq(sizes, i, j), sizes.len() as nat).eqv(
            max_height(sizes, sizes.len() as nat)),
{
    let n = sizes.len() as nat;
    let t = swap_seq(sizes, i, j);

    // Nonneg bounds for upper_bound preconditions
    lemma_max_height_nonneg(sizes, n);
    assert forall|k: int| 0 <= k < t.len() implies T::zero().le(t[k].height) by {
        if k == i as int { } else if k == j as int { } else { }
    }
    lemma_max_height_nonneg(t, n);

    // Direction 1: max_height(t, n) <= max_height(s, n)
    lemma_swap_elements_bounded_by_max_height(sizes, i, j);
    lemma_max_height_upper_bound(t, n, max_height(sizes, n));

    // Direction 2: max_height(s, n) <= max_height(t, n)
    assert forall|k: int| 0 <= k < n as int implies
        sizes[k].height.le(max_height(t, n))
    by {
        if k == i as int {
            lemma_max_height_bounds_child(t, j);
        } else if k == j as int {
            lemma_max_height_bounds_child(t, i);
        } else {
            lemma_max_height_bounds_child(t, k as nat);
        }
    }
    lemma_max_height_upper_bound(sizes, n, max_height(t, n));

    T::axiom_le_antisymmetric(
        max_height(t, n),
        max_height(sizes, n),
    );
}

/// Stack parent size is invariant under swapping two children.
pub proof fn lemma_stack_content_size_swap<T: OrderedRing>(
    sizes: Seq<Size<T>>,
    i: nat,
    j: nat,
)
    requires
        i < sizes.len(),
        j < sizes.len(),
        forall|k: int| 0 <= k < sizes.len() ==> sizes[k].is_nonneg(),
    ensures
        stack_content_size(swap_seq(sizes, i, j)).width.eqv(
            stack_content_size(sizes).width),
        stack_content_size(swap_seq(sizes, i, j)).height.eqv(
            stack_content_size(sizes).height),
{
    reveal(stack_content_size);
    lemma_max_width_swap(sizes, i, j);
    lemma_max_height_swap(sizes, i, j);
}

// ── Stack children-within-bounds ──────────────────────────────────

/// Stack layout with Start alignment on both axes has children_within_bounds.
/// Each child is at (padding.left, padding.top) and its size fits within
/// the resolved parent bounds.
pub proof fn lemma_stack_start_children_within_bounds<T: OrderedField>(
    limits: Limits<T>,
    padding: Padding<T>,
    children: Seq<Widget<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
    ensures
        layout_widget(limits, Widget::Container(ContainerWidget::Stack {
            padding,
            h_align: Alignment::Start,
            v_align: Alignment::Start,
            children,
        }), fuel).children_within_bounds(),
{
    reveal(stack_layout);
    reveal(stack_content_size);
    reveal(align_offset);
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    let content = stack_content_size(child_sizes);
    let total_w = h.add(content.width);
    let total_h = v.add(content.height);
    let avail_w = limits.max.width.sub(h);
    let avail_h = limits.max.height.sub(v);
    let parent_size = limits.resolve(Size::new(total_w, total_h));

    // h >= 0, v >= 0
    lemma_nonneg_sum(padding.left, padding.right);
    lemma_nonneg_sum(padding.top, padding.bottom);

    // inner.wf()
    lemma_shrink_wf(limits, h, v);

    // Convert: h+min <= max → min+h <= max for shrink_max_bound
    lemma_add_comm_le(h, limits.min.width, limits.max.width);
    lemma_add_comm_le(v, limits.min.height, limits.max.height);
    lemma_shrink_max_bound(limits, h, v);

    // Each child size: min <= size <= max, hence nonneg
    assert forall|k: int| 0 <= k < cn.len() implies
        child_sizes[k].width.le(inner.max.width)
        && child_sizes[k].height.le(inner.max.height)
        && T::zero().le(child_sizes[k].width)
        && T::zero().le(child_sizes[k].height)
    by {
        lemma_layout_respects_limits(inner, children[k], (fuel - 1) as nat);
        T::axiom_le_transitive(T::zero(), inner.min.width, child_sizes[k].width);
        T::axiom_le_transitive(T::zero(), inner.min.height, child_sizes[k].height);
    };

    // content <= inner.max
    lemma_max_width_upper_bound(child_sizes, child_sizes.len() as nat, inner.max.width);
    lemma_max_height_upper_bound(child_sizes, child_sizes.len() as nat, inner.max.height);

    // total_w = h + content.w <= h + inner.max.w = inner.max.w + h <= max.w
    T::axiom_le_add_monotone(content.width, inner.max.width, h);
    lemma_add_comm_le(content.width, h, inner.max.width.add(h));
    T::axiom_le_transitive(total_w, inner.max.width.add(h), limits.max.width);

    // total_h = v + content.h <= max.h (symmetric)
    T::axiom_le_add_monotone(content.height, inner.max.height, v);
    lemma_add_comm_le(content.height, v, inner.max.height.add(v));
    T::axiom_le_transitive(total_h, inner.max.height.add(v), limits.max.height);

    // resolve >= total
    lemma_resolve_ge_input(limits, Size::new(total_w, total_h));

    // stack_children length
    lemma_stack_children_len(
        padding, Alignment::Start, Alignment::Start, child_sizes,
        avail_w, avail_h, 0,
    );

    // Per-child cwb
    let sc = stack_children(
        padding, Alignment::Start, Alignment::Start, child_sizes,
        avail_w, avail_h, 0,
    );
    assert forall|i: int| #![trigger child_sizes[i]] 0 <= i < cn.len() implies
        T::zero().le(sc[i].x)
        && T::zero().le(sc[i].y)
        && sc[i].x.add(child_sizes[i].width).le(parent_size.width)
        && sc[i].y.add(child_sizes[i].height).le(parent_size.height)
    by {
        // Element access: sc[i] = Node::leaf(left+align_offset, top+align_offset, sizes[i])
        lemma_stack_children_element(
            padding, Alignment::Start, Alignment::Start, child_sizes,
            avail_w, avail_h, i as nat,
        );
        // For Start: align_offset(Start, _, _) = T::zero()
        // So sc[i].x = padding.left.add(T::zero()), sc[i].y = padding.top.add(T::zero())

        // 0 <= x: 0 <= left <= left + 0
        T::axiom_le_reflexive(T::zero());
        lemma_le_add_nonneg(padding.left, T::zero());
        T::axiom_le_transitive(T::zero(), padding.left, padding.left.add(T::zero()));
        // 0 <= y: symmetric
        lemma_le_add_nonneg(padding.top, T::zero());
        T::axiom_le_transitive(T::zero(), padding.top, padding.top.add(T::zero()));

        // child.w <= content.w = max_width(sizes, n)
        lemma_max_width_contains(child_sizes, i as nat);
        lemma_max_width_monotone(child_sizes, (i + 1) as nat, child_sizes.len() as nat);
        T::axiom_le_transitive(
            child_sizes[i as int].width,
            max_width(child_sizes, (i + 1) as nat),
            content.width,
        );
        // child.h <= content.h
        lemma_max_height_contains(child_sizes, i as nat);
        lemma_max_height_monotone(child_sizes, (i + 1) as nat, child_sizes.len() as nat);
        T::axiom_le_transitive(
            child_sizes[i as int].height,
            max_height(child_sizes, (i + 1) as nat),
            content.height,
        );

        // left + child.w <= h + content.w = total_w <= parent.w
        lemma_le_add_nonneg(padding.left, padding.right);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            padding.left, h, child_sizes[i as int].width, content.width,
        );
        T::axiom_le_transitive(
            padding.left.add(child_sizes[i as int].width), total_w, parent_size.width,
        );
        // top + child.h <= v + content.h = total_h <= parent.h
        lemma_le_add_nonneg(padding.top, padding.bottom);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            padding.top, v, child_sizes[i as int].height, content.height,
        );
        T::axiom_le_transitive(
            padding.top.add(child_sizes[i as int].height), total_h, parent_size.height,
        );

        // Bridge: right() = (left+0)+child.w, need to show this ≡ left+child.w
        // left+0 ≡ left (add_identity), then (left+0)+w ≡ left+w (add_congruence)
        T::axiom_add_zero_right(padding.left);
        T::axiom_eqv_symmetric(padding.left.add(T::zero()), padding.left);
        T::axiom_eqv_reflexive(child_sizes[i as int].width);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.left, padding.left.add(T::zero()),
            child_sizes[i as int].width, child_sizes[i as int].width,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.left.add(child_sizes[i as int].width),
            padding.left.add(T::zero()).add(child_sizes[i as int].width),
            parent_size.width,
        );
        // Bridge for bottom(): (top+0)+child.h ≡ top+child.h
        T::axiom_add_zero_right(padding.top);
        T::axiom_eqv_symmetric(padding.top.add(T::zero()), padding.top);
        T::axiom_eqv_reflexive(child_sizes[i as int].height);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<T>(
            padding.top, padding.top.add(T::zero()),
            child_sizes[i as int].height, child_sizes[i as int].height,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.top.add(child_sizes[i as int].height),
            padding.top.add(T::zero()).add(child_sizes[i as int].height),
            parent_size.height,
        );
    };

    // Bridge: connect sc[i] facts to merge_layout(stack_layout(...), cn).cwb
    let layout = stack_layout(limits, padding, Alignment::Start, Alignment::Start, child_sizes);

    // Prove merge_layout precondition: layout.children[i] bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        // Trigger the first forall: child_sizes[i] == cn[i].size (definitional)
        assert(child_sizes[i] === cn[i].size);
        // Now Z3 has child_sizes[i] ground term, triggering the sc[i] facts above.
        // layout.children[i] == sc[i] (both from stack_children with same args)
        // layout.size == parent_size (both from limits.resolve with same args)
    };

    lemma_merge_layout_cwb(layout, cn);
}

/// max_width is monotone in inputs: if each width in sizes1 <= sizes2, then
/// max_width(sizes1, n) <= max_width(sizes2, n).
pub proof fn lemma_max_width_le_inputs<T: OrderedRing>(
    sizes1: Seq<Size<T>>,
    sizes2: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes1.len(),
        n <= sizes2.len(),
        forall|i: int| 0 <= i < n as int ==> sizes1[i].width.le(sizes2[i].width),
        forall|i: int| 0 <= i < n as int ==> T::zero().le(sizes2[i].width),
    ensures
        max_width(sizes1, n).le(max_width(sizes2, n)),
    decreases n,
{
    reveal(max_width);
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        let k = (n - 1) as nat;
        // Induction: max_width(sizes1, k) <= max_width(sizes2, k)
        lemma_max_width_le_inputs(sizes1, sizes2, k);

        // sizes1[k].width <= sizes2[k].width (from precondition)
        // max_width(sizes1, n) = max(max_width(sizes1, k), sizes1[k].width)
        // max_width(sizes2, n) = max(max_width(sizes2, k), sizes2[k].width)
        // Both components of the left max are <= some component of the right max.

        // max_width(sizes1, k) <= max_width(sizes2, k) <= max(sizes2, k, sizes2[k].w)
        verus_algebra::min_max::lemma_max_ge_left::<T>(
            max_width(sizes2, k), sizes2[k as int].width,
        );
        T::axiom_le_transitive(
            max_width(sizes1, k), max_width(sizes2, k),
            max::<T>(max_width(sizes2, k), sizes2[k as int].width),
        );

        // sizes1[k].w <= sizes2[k].w <= max(sizes2, k, sizes2[k].w)
        verus_algebra::min_max::lemma_max_ge_right::<T>(
            max_width(sizes2, k), sizes2[k as int].width,
        );
        T::axiom_le_transitive(
            sizes1[k as int].width, sizes2[k as int].width,
            max::<T>(max_width(sizes2, k), sizes2[k as int].width),
        );

        // Both args of max(sizes1) are <= max(sizes2)
        // max(a, b) <= c when a <= c and b <= c
        // Use totality on the two args to show max picks one of them
        T::axiom_le_total(max_width(sizes1, k), sizes1[k as int].width);
    }
}

/// max_height is monotone in inputs: if each height in sizes1 <= sizes2, then
/// max_height(sizes1, n) <= max_height(sizes2, n).
pub proof fn lemma_max_height_le_inputs<T: OrderedRing>(
    sizes1: Seq<Size<T>>,
    sizes2: Seq<Size<T>>,
    n: nat,
)
    requires
        n <= sizes1.len(),
        n <= sizes2.len(),
        forall|i: int| 0 <= i < n as int ==> sizes1[i].height.le(sizes2[i].height),
        forall|i: int| 0 <= i < n as int ==> T::zero().le(sizes2[i].height),
    ensures
        max_height(sizes1, n).le(max_height(sizes2, n)),
    decreases n,
{
    reveal(max_height);
    if n == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        let k = (n - 1) as nat;
        lemma_max_height_le_inputs(sizes1, sizes2, k);

        verus_algebra::min_max::lemma_max_ge_left::<T>(
            max_height(sizes2, k), sizes2[k as int].height,
        );
        T::axiom_le_transitive(
            max_height(sizes1, k), max_height(sizes2, k),
            max::<T>(max_height(sizes2, k), sizes2[k as int].height),
        );

        verus_algebra::min_max::lemma_max_ge_right::<T>(
            max_height(sizes2, k), sizes2[k as int].height,
        );
        T::axiom_le_transitive(
            sizes1[k as int].height, sizes2[k as int].height,
            max::<T>(max_height(sizes2, k), sizes2[k as int].height),
        );

        T::axiom_le_total(max_height(sizes1, k), sizes1[k as int].height);
    }
}

/// stack_layout.children has length cs.len().
pub proof fn lemma_stack_layout_children_len<T: OrderedField>(
    lim: Limits<T>, pad: Padding<T>, ha: Alignment, va: Alignment,
    cs: Seq<Size<T>>,
)
    ensures stack_layout(lim, pad, ha, va, cs).children.len() == cs.len(),
{
    reveal(stack_layout);
    reveal(stack_content_size);
    lemma_stack_children_len(pad, ha, va, cs,
        lim.max.width.sub(pad.horizontal()),
        lim.max.height.sub(pad.vertical()), 0);
}

} // verus!
