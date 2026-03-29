use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::node::Node;
use crate::padding::Padding;
use crate::layout::absolute::*;

verus! {

///  The output of absolute_children has length equal to (child_data.len() - index).
pub proof fn lemma_absolute_children_len<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    index: nat,
)
    requires
        index <= child_data.len(),
    ensures
        absolute_children(padding, child_data, index).len() == child_data.len() - index,
    decreases child_data.len() - index,
{
    if index >= child_data.len() {
        //  base case: empty
    } else {
        lemma_absolute_children_len(padding, child_data, index + 1);
    }
}

///  Element access: absolute_children(padding, child_data, 0)[i] gives the node
///  at position (padding.left + x_i, padding.top + y_i) with the correct size.
pub proof fn lemma_absolute_children_element<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    i: nat,
)
    requires
        i < child_data.len(),
    ensures
        ({
            let children = absolute_children(padding, child_data, 0);
            let (x, y, sz) = child_data[i as int];
            &&& children.len() == child_data.len()
            &&& children[i as int].x == padding.left.add(x)
            &&& children[i as int].y == padding.top.add(y)
            &&& children[i as int].size == sz
            &&& children[i as int].children == Seq::<Node<T>>::empty()
        }),
    decreases i,
{
    lemma_absolute_children_len::<T>(padding, child_data, 0);
    if i == 0 {
        //  Base: first element of push-add is the pushed element
    } else {
        //  Inductive: element i of push-add is element i-1 of the tail
        lemma_absolute_children_len::<T>(padding, child_data, 1);
        lemma_absolute_children_shift::<T>(padding, child_data, 0, i);
    }
}

///  Helper: shifting the start index doesn't change element access when adjusted.
proof fn lemma_absolute_children_shift<T: OrderedField>(
    padding: Padding<T>,
    child_data: Seq<(T, T, Size<T>)>,
    start: nat,
    i: nat,
)
    requires
        start + i < child_data.len(),
        i > 0,
        absolute_children(padding, child_data, start).len() == child_data.len() - start,
    ensures
        ({
            let children = absolute_children(padding, child_data, start);
            let (x, y, sz) = child_data[(start + i) as int];
            &&& children[i as int].x == padding.left.add(x)
            &&& children[i as int].y == padding.top.add(y)
            &&& children[i as int].size == sz
            &&& children[i as int].children == Seq::<Node<T>>::empty()
        }),
    decreases i,
{
    lemma_absolute_children_len::<T>(padding, child_data, start + 1);
    //  absolute_children(start) = push(node_at_start).add(absolute_children(start+1))
    //  Element [0] is node_at_start, elements [1..] come from absolute_children(start+1)
    if i == 1 {
        //  element [1] is element [0] of absolute_children(start+1)
        //  which is the node at start+1
    } else {
        lemma_absolute_children_shift::<T>(padding, child_data, start + 1, (i - 1) as nat);
    }
}

//  ── absolute_max_right/bottom bounds ────────────────────────────────

///  For any i < count, x_i + w_i <= absolute_max_right(child_data, count).
proof fn lemma_absolute_max_right_ge<T: OrderedRing>(
    child_data: Seq<(T, T, Size<T>)>,
    count: nat,
    i: nat,
)
    requires
        i < count,
        count <= child_data.len(),
    ensures
        child_data[i as int].0.add(child_data[i as int].2.width)
            .le(absolute_max_right(child_data, count)),
    decreases count,
{
    if count == 0 {
        //  impossible
    } else if i == (count - 1) as nat {
        //  This element is the last in the max: max(rest, x_i + w_i) >= x_i + w_i
        verus_algebra::min_max::lemma_max_ge_right::<T>(
            absolute_max_right(child_data, (count - 1) as nat),
            child_data[i as int].0.add(child_data[i as int].2.width),
        );
    } else {
        //  Element is in rest: by induction, x_i + w_i <= max_right(count-1) <= max_right(count)
        lemma_absolute_max_right_ge(child_data, (count - 1) as nat, i);
        verus_algebra::min_max::lemma_max_ge_left::<T>(
            absolute_max_right(child_data, (count - 1) as nat),
            child_data[(count - 1) as int].0.add(child_data[(count - 1) as int].2.width),
        );
        T::axiom_le_transitive(
            child_data[i as int].0.add(child_data[i as int].2.width),
            absolute_max_right(child_data, (count - 1) as nat),
            absolute_max_right(child_data, count),
        );
    }
}

///  For any i < count, y_i + h_i <= absolute_max_bottom(child_data, count).
proof fn lemma_absolute_max_bottom_ge<T: OrderedRing>(
    child_data: Seq<(T, T, Size<T>)>,
    count: nat,
    i: nat,
)
    requires
        i < count,
        count <= child_data.len(),
    ensures
        child_data[i as int].1.add(child_data[i as int].2.height)
            .le(absolute_max_bottom(child_data, count)),
    decreases count,
{
    if count == 0 {
        //  impossible
    } else if i == (count - 1) as nat {
        verus_algebra::min_max::lemma_max_ge_right::<T>(
            absolute_max_bottom(child_data, (count - 1) as nat),
            child_data[i as int].1.add(child_data[i as int].2.height),
        );
    } else {
        lemma_absolute_max_bottom_ge(child_data, (count - 1) as nat, i);
        verus_algebra::min_max::lemma_max_ge_left::<T>(
            absolute_max_bottom(child_data, (count - 1) as nat),
            child_data[(count - 1) as int].1.add(child_data[(count - 1) as int].2.height),
        );
        T::axiom_le_transitive(
            child_data[i as int].1.add(child_data[i as int].2.height),
            absolute_max_bottom(child_data, (count - 1) as nat),
            absolute_max_bottom(child_data, count),
        );
    }
}

//  ── Absolute CWB ───────────────────────────────────────────────────

///  Absolute layout has children_within_bounds.
pub proof fn lemma_absolute_children_within_bounds<T: OrderedField>(
    limits: crate::limits::Limits<T>,
    padding: Padding<T>,
    children: Seq<crate::widget::AbsoluteChild<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        //  All offsets are nonneg
        forall|i: int| 0 <= i < children.len() ==>
            T::zero().le(children[i].x) && T::zero().le(children[i].y),
        //  Content fits in limits.max
        crate::layout::proofs::widget_wf_absolute_content_fits(
            limits, padding, children, (fuel - 1) as nat,
        ),
    ensures
        crate::widget::layout_widget(limits, crate::widget::Widget::Container(crate::widget::ContainerWidget::Absolute {
            padding, children,
        }), fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let cn = crate::widget::absolute_widget_child_nodes(
        inner, children, (fuel - 1) as nat,
    );
    //  child_data matching requires (direct from children[i].x/y)
    let child_data = Seq::new(cn.len(), |i: int|
        (children[i].x, children[i].y, cn[i].size));
    let content = absolute_content_size(child_data);
    let total_w = h.add(content.width);
    let total_h = v.add(content.height);

    //  total <= limits.max (from requires)
    assert(total_w.le(limits.max.width));
    assert(total_h.le(limits.max.height));

    //  parent_size >= (h + content_w, v + content_h)
    crate::layout::proofs::lemma_resolve_ge_input(
        limits, Size::new(total_w, total_h),
    );
    let parent_size = limits.resolve(Size::new(total_w, total_h));

    //  child_data matching layout_absolute_body (through offsets)
    let offsets = Seq::new(children.len(), |i: int|
        (children[i].x, children[i].y));
    let child_data_body = Seq::new(cn.len(), |i: int|
        (offsets[i].0, offsets[i].1, cn[i].size));
    //  Bridge: both child_data are extensionally equal
    assert(child_data =~= child_data_body);

    reveal(absolute_layout);
    let layout = absolute_layout(limits, padding, child_data_body);

    //  layout.children.len() == cn.len()
    lemma_absolute_children_len(padding, child_data, 0);

    //  Per-child bounds
    assert forall|idx: int| 0 <= idx < cn.len() implies
        T::zero().le(layout.children[idx].x)
        && T::zero().le(layout.children[idx].y)
        && layout.children[idx].x.add(cn[idx].size.width).le(layout.size.width)
        && layout.children[idx].y.add(cn[idx].size.height).le(layout.size.height)
    by {
        let i = idx as nat;
        lemma_absolute_children_element(padding, child_data, i);
        let (xi, yi, szi) = child_data[idx];

        //  Lower bounds: padding.left + x_i >= 0, padding.top + y_i >= 0
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), padding.left, T::zero(), xi,
        );
        T::axiom_add_zero_right(T::zero());
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().add(T::zero()), T::zero(), padding.left.add(xi),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), padding.top, T::zero(), yi,
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().add(T::zero()), T::zero(), padding.top.add(yi),
        );

        //  Upper X bound: pl + xi + wi <= pl + content_w <= h + content_w <= parent_w
        //  Step 1: xi + wi <= content_w = absolute_max_right(child_data, n)
        lemma_absolute_max_right_ge(child_data, child_data.len() as nat, i);
        //  Step 2: pl + (xi + wi) <= pl + content_w
        T::axiom_le_add_monotone(
            xi.add(szi.width), content.width, padding.left,
        );
        T::axiom_add_commutative(xi.add(szi.width), padding.left);
        T::axiom_add_commutative(content.width, padding.left);
        T::axiom_le_congruence(
            xi.add(szi.width).add(padding.left), padding.left.add(xi.add(szi.width)),
            content.width.add(padding.left), padding.left.add(content.width),
        );
        //  Step 3: (pl + xi) + wi ≡ pl + (xi + wi) via assoc
        T::axiom_add_associative(padding.left, xi, szi.width);
        T::axiom_eqv_symmetric(
            padding.left.add(xi).add(szi.width),
            padding.left.add(xi.add(szi.width)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.left.add(xi.add(szi.width)),
            padding.left.add(xi).add(szi.width),
            padding.left.add(content.width),
        );
        //  Step 4: pl + content_w <= h + content_w (since pl <= h)
        crate::layout::proofs::lemma_le_add_nonneg(padding.left, padding.right);
        T::axiom_le_add_monotone(padding.left, h, content.width);
        T::axiom_add_commutative(padding.left, content.width);
        T::axiom_add_commutative(h, content.width);
        T::axiom_le_congruence(
            padding.left.add(content.width), content.width.add(padding.left),
            h.add(content.width), content.width.add(h),
        );
        //  Step 5: h + content_w <= parent_w (from resolve_ge_input)
        T::axiom_le_transitive(
            padding.left.add(xi).add(szi.width),
            padding.left.add(content.width),
            h.add(content.width),
        );
        T::axiom_le_transitive(
            padding.left.add(xi).add(szi.width),
            h.add(content.width),
            parent_size.width,
        );

        //  Upper Y bound: pt + yi + hi <= pt + content_h <= v + content_h <= parent_h
        lemma_absolute_max_bottom_ge(child_data, child_data.len() as nat, i);
        T::axiom_le_add_monotone(
            yi.add(szi.height), content.height, padding.top,
        );
        T::axiom_add_commutative(yi.add(szi.height), padding.top);
        T::axiom_add_commutative(content.height, padding.top);
        T::axiom_le_congruence(
            yi.add(szi.height).add(padding.top), padding.top.add(yi.add(szi.height)),
            content.height.add(padding.top), padding.top.add(content.height),
        );
        T::axiom_add_associative(padding.top, yi, szi.height);
        T::axiom_eqv_symmetric(
            padding.top.add(yi).add(szi.height),
            padding.top.add(yi.add(szi.height)),
        );
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            padding.top.add(yi.add(szi.height)),
            padding.top.add(yi).add(szi.height),
            padding.top.add(content.height),
        );
        crate::layout::proofs::lemma_le_add_nonneg(padding.top, padding.bottom);
        T::axiom_le_add_monotone(padding.top, v, content.height);
        T::axiom_add_commutative(padding.top, content.height);
        T::axiom_add_commutative(v, content.height);
        T::axiom_le_congruence(
            padding.top.add(content.height), content.height.add(padding.top),
            v.add(content.height), content.height.add(v),
        );
        T::axiom_le_transitive(
            padding.top.add(yi).add(szi.height),
            padding.top.add(content.height),
            v.add(content.height),
        );
        T::axiom_le_transitive(
            padding.top.add(yi).add(szi.height),
            v.add(content.height),
            parent_size.height,
        );
    };

    crate::layout::proofs::lemma_merge_layout_cwb(layout, cn);
}

} //  verus!
