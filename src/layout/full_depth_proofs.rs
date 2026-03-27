use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::padding::Padding;
use crate::alignment::{Alignment, align_offset};
use crate::widget::*;
use crate::layout::*;
use crate::layout::flex::*;
use crate::layout::congruence_proofs::*;

verus! {

/// flex_child_main_size congruence: w.div(tw).mul(av) eqv when all args eqv.
proof fn lemma_flex_child_main_size_congruence<T: OrderedField>(
    w1: T, w2: T, tw1: T, tw2: T, av1: T, av2: T,
)
    requires w1.eqv(w2), tw1.eqv(tw2), av1.eqv(av2), !tw1.eqv(T::zero()),
    ensures flex_child_main_size(w1, tw1, av1).eqv(flex_child_main_size(w2, tw2, av2)),
{
    verus_algebra::quadratic::lemma_div_congruence(w1, w2, tw1, tw2);
    T::axiom_mul_congruence_left(w1.div(tw1), w2.div(tw2), av1);
    verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence_right::<T>(w2.div(tw2), av1, av2);
    T::axiom_eqv_transitive(
        flex_child_main_size(w1, tw1, av1), w2.div(tw2).mul(av1),
        flex_child_main_size(w2, tw2, av2));
}

/// Per-index position congruence for flex_column_children.
proof fn lemma_flex_column_position_eqv_at<T: OrderedField>(
    p1: Padding<T>, p2: Padding<T>, sp1: T, sp2: T, al: Alignment,
    w1s: Seq<T>, w2s: Seq<T>, ccs1: Seq<T>, ccs2: Seq<T>,
    tw1: T, tw2: T, aw1: T, aw2: T, ah1: T, ah2: T, i: nat,
)
    requires
        padding_eqv(p1, p2), sp1.eqv(sp2),
        w1s.len() == w2s.len(), ccs1.len() == ccs2.len(),
        w1s.len() == ccs1.len(),
        forall|j: int| 0 <= j < w1s.len() ==> w1s[j].eqv(w2s[j]),
        forall|j: int| 0 <= j < ccs1.len() ==> ccs1[j].eqv(ccs2[j]),
        tw1.eqv(tw2), !tw1.eqv(T::zero()),
        aw1.eqv(aw2), ah1.eqv(ah2),
        i < w1s.len(),
    ensures ({
        let fc1 = flex_column_children(p1, sp1, al, w1s, ccs1, tw1, aw1, ah1, 0);
        let fc2 = flex_column_children(p2, sp2, al, w2s, ccs2, tw2, aw2, ah2, 0);
        fc1[i as int].x.eqv(fc2[i as int].x)
        && fc1[i as int].y.eqv(fc2[i as int].y)
    }),
{
    crate::layout::flex_proofs::lemma_flex_column_children_element(
        p1, sp1, al, w1s, ccs1, tw1, aw1, ah1, i);
    crate::layout::flex_proofs::lemma_flex_column_children_element(
        p2, sp2, al, w2s, ccs2, tw2, aw2, ah2, i);
    lemma_align_offset_congruence(al, aw1, aw2, ccs1[i as int], ccs2[i as int]);
    T::axiom_add_congruence_left(p1.left, p2.left, align_offset(al, aw1, ccs1[i as int]));
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        p2.left, align_offset(al, aw1, ccs1[i as int]), align_offset(al, aw2, ccs2[i as int]));
    T::axiom_eqv_transitive(
        p1.left.add(align_offset(al, aw1, ccs1[i as int])),
        p2.left.add(align_offset(al, aw1, ccs1[i as int])),
        p2.left.add(align_offset(al, aw2, ccs2[i as int])));
    lemma_flex_column_child_y_congruence(p1.top, p2.top, w1s, w2s, tw1, tw2, ah1, ah2, sp1, sp2, i);
}

/// Flex Column full-depth dispatch.
pub proof fn lemma_flex_column_full_depth_dispatch<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    p1: Padding<T>, sp1: T, al: Alignment, ch1: Seq<FlexItem<T>>,
    w2: Widget<T>, fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(Widget::Container(ContainerWidget::Flex {
            padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Column, children: ch1 }), w2, fuel),
        fuel > 1, ch1.len() > 0,
        T::zero().lt(sum_weights(Seq::new(ch1.len(), |i: int| ch1[i].weight), ch1.len() as nat)),
    ensures crate::diff::nodes_deeply_eqv(
        layout_widget(lim1, Widget::Container(ContainerWidget::Flex {
            padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Column, children: ch1 }), fuel),
        layout_widget(lim2, w2, fuel),
        min_children_congruence_depth(
            Seq::new(ch1.len(), |i: int| ch1[i].child), (fuel - 1) as nat, 0) + 1),
    decreases fuel, 1nat,
{
    if let Widget::Container(ContainerWidget::Flex { padding: p2, spacing: sp2, children: ch2, .. }) = w2 {
        lemma_padding_horizontal_congruence(p1, p2);
        lemma_padding_vertical_congruence(p1, p2);
        lemma_shrink_congruence(lim1, lim2, p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
        let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
        let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
        let w1s = Seq::new(ch1.len(), |i: int| ch1[i].weight);
        let w2s = Seq::new(ch2.len(), |i: int| ch2[i].weight);
        let tw1 = sum_weights(w1s, w1s.len() as nat);
        let tw2 = sum_weights(w2s, w2s.len() as nat);
        // !tw.eqv(zero) from precondition
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), tw1);
        T::axiom_eqv_symmetric(T::zero(), tw1);
        let ts1 = repeated_add(sp1, (ch1.len() - 1) as nat);
        let ts2 = repeated_add(sp2, (ch2.len() - 1) as nat);
        lemma_repeated_add_congruence(sp1, sp2, (ch1.len() - 1) as nat);
        let am1 = inner1.max.height.sub(ts1);
        let am2 = inner2.max.height.sub(ts2);
        lemma_sub_congruence(inner1.max.height, inner2.max.height, ts1, ts2);
        lemma_sum_weights_congruence(w1s, w2s, w1s.len() as nat);
        assert(!tw1.eqv(T::zero()));
        // Children IH
        let cn1 = flex_linear_widget_child_nodes(inner1, ch1, w1s, tw1, am1,
            Axis::Vertical, (fuel - 1) as nat);
        let cn2 = flex_linear_widget_child_nodes(inner2, ch2, w2s, tw2, am2,
            Axis::Vertical, (fuel - 1) as nat);
        let wc1 = Seq::new(ch1.len(), |i: int| ch1[i].child);
        let rd = min_children_congruence_depth(wc1, (fuel - 1) as nat, 0);
        assert forall|i: int| 0 <= i < cn1.len() implies
            crate::diff::nodes_deeply_eqv(#[trigger] cn1[i], cn2[i], rd)
        by {
            lemma_min_children_depth_le::<T>(wc1, (fuel - 1) as nat, 0, i);
            lemma_flex_child_main_size_congruence(w1s[i], w2s[i], tw1, tw2, am1, am2);
            lemma_layout_widget_full_depth_congruence(
                Limits { min: inner1.min, max: Size::new(inner1.max.width, flex_child_main_size(w1s[i], tw1, am1)) },
                Limits { min: inner2.min, max: Size::new(inner2.max.width, flex_child_main_size(w2s[i], tw2, am2)) },
                ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            crate::diff::lemma_deeply_eqv_depth_monotone(cn1[i], cn2[i],
                congruence_depth(ch1[i].child, (fuel - 1) as nat), rd);
        };
        lemma_sizes_eqv_from_deeply_eqv(cn1, cn2, rd);
        // Position congruence
        reveal(flex_column_layout);
        let ccs1 = Seq::new(cn1.len(), |i: int| cn1[i].size.width);
        let ccs2 = Seq::new(cn2.len(), |i: int| cn2[i].size.width);
        let fl1 = flex_column_layout(lim1, p1, sp1, al, w1s, ccs1);
        let fl2 = flex_column_layout(lim2, p2, sp2, al, w2s, ccs2);
        crate::layout::flex_proofs::lemma_flex_column_children_len(p1, sp1, al, w1s, ccs1, tw1, inner1.max.width, inner1.max.height, 0);
        crate::layout::flex_proofs::lemma_flex_column_children_len(p2, sp2, al, w2s, ccs2, tw2, inner2.max.width, inner2.max.height, 0);
        // After reveal: fl1 = flex_column_layout(...) = Node { children: flex_column_children(...) }
        // flex_column_children_len gives len == w1s.len()
        // Z3 should see fl1.children.len() from the revealed definition
        // fl1.children = flex_column_children after reveal
        let fc1 = flex_column_children(p1, sp1, al, w1s, ccs1, tw1, inner1.max.width, inner1.max.height, 0);
        let fc2 = flex_column_children(p2, sp2, al, w2s, ccs2, tw2, inner2.max.width, inner2.max.height, 0);
        assert(fl1.children =~= fc1);
        assert(fl2.children =~= fc2);
        // Position congruence per-index (each gets full rlimit)
        assert forall|i: int| 0 <= i < fc1.len() implies
            fc1[i].x.eqv(fc2[i].x) && fc1[i].y.eqv(fc2[i].y)
        by {
            lemma_flex_column_position_eqv_at(p1, p2, sp1, sp2, al, w1s, w2s, ccs1, ccs2,
                tw1, tw2, inner1.max.width, inner2.max.width, inner1.max.height, inner2.max.height, i as nat);
        };
        lemma_layout_widget_node_congruence(lim1, lim2,
            Widget::Container(ContainerWidget::Flex { padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Column, children: ch1 }), w2, fuel);
        lemma_merge_layout_deep_congruence_plus_one(fl1, fl2, cn1, cn2, rd);
    }
}

} // verus!
