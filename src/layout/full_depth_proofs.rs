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

// NOTE: The Flex dispatch requires !tw.eqv(zero) which comes from widget_wf (not widget_eqv).
// The user must ensure widget_wf for Flex widgets to use full-depth congruence.

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
        // flex_column_layout uses lim.max.width/height.sub(pad) for available dims
        let fw1 = lim1.max.width.sub(p1.horizontal());
        let fw2 = lim2.max.width.sub(p2.horizontal());
        lemma_sub_congruence(lim1.max.width, lim2.max.width, p1.horizontal(), p2.horizontal());
        let fhp1 = lim1.max.height.sub(p1.vertical());
        let fhp2 = lim2.max.height.sub(p2.vertical());
        lemma_sub_congruence(lim1.max.height, lim2.max.height, p1.vertical(), p2.vertical());
        let fh1 = fhp1.sub(ts1);
        let fh2 = fhp2.sub(ts2);
        lemma_sub_congruence(fhp1, fhp2, ts1, ts2);
        crate::layout::flex_proofs::lemma_flex_column_children_len(p1, sp1, al, w1s, ccs1, tw1, fw1, fh1, 0);
        crate::layout::flex_proofs::lemma_flex_column_children_len(p2, sp2, al, w2s, ccs2, tw2, fw2, fh2, 0);
        let fc1 = flex_column_children(p1, sp1, al, w1s, ccs1, tw1, fw1, fh1, 0);
        let fc2 = flex_column_children(p2, sp2, al, w2s, ccs2, tw2, fw2, fh2, 0);
        assert(fl1.children =~= fc1);
        assert(fl2.children =~= fc2);
        // Position congruence per-index (each gets full rlimit)
        assert forall|i: int| 0 <= i < fc1.len() implies
            fc1[i].x.eqv(fc2[i].x) && fc1[i].y.eqv(fc2[i].y)
        by {
            lemma_flex_column_position_eqv_at(p1, p2, sp1, sp2, al, w1s, w2s, ccs1, ccs2,
                tw1, tw2, fw1, fw2, fh1, fh2, i as nat);
        };
        lemma_layout_widget_node_congruence(lim1, lim2,
            Widget::Container(ContainerWidget::Flex { padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Column, children: ch1 }), w2, fuel);
        lemma_merge_layout_deep_congruence_plus_one(fl1, fl2, cn1, cn2, rd);
    }
}

/// Per-index position congruence for flex_row_children.
proof fn lemma_flex_row_position_eqv_at<T: OrderedField>(
    p1: Padding<T>, p2: Padding<T>, sp1: T, sp2: T, al: Alignment,
    w1s: Seq<T>, w2s: Seq<T>, ccs1: Seq<T>, ccs2: Seq<T>,
    tw1: T, tw2: T, aw1: T, aw2: T, ah1: T, ah2: T, i: nat,
)
    requires
        padding_eqv(p1, p2), sp1.eqv(sp2),
        w1s.len() == w2s.len(), ccs1.len() == ccs2.len(), w1s.len() == ccs1.len(),
        forall|j: int| 0 <= j < w1s.len() ==> w1s[j].eqv(w2s[j]),
        forall|j: int| 0 <= j < ccs1.len() ==> ccs1[j].eqv(ccs2[j]),
        tw1.eqv(tw2), !tw1.eqv(T::zero()), aw1.eqv(aw2), ah1.eqv(ah2), i < w1s.len(),
    ensures ({
        let fc1 = flex_row_children(p1, sp1, al, w1s, ccs1, tw1, aw1, ah1, 0);
        let fc2 = flex_row_children(p2, sp2, al, w2s, ccs2, tw2, aw2, ah2, 0);
        fc1[i as int].x.eqv(fc2[i as int].x) && fc1[i as int].y.eqv(fc2[i as int].y)
    }),
{
    crate::layout::flex_proofs::lemma_flex_row_children_element(p1, sp1, al, w1s, ccs1, tw1, aw1, ah1, i);
    crate::layout::flex_proofs::lemma_flex_row_children_element(p2, sp2, al, w2s, ccs2, tw2, aw2, ah2, i);
    lemma_flex_row_child_x_congruence(p1.left, p2.left, w1s, w2s, tw1, tw2, aw1, aw2, sp1, sp2, i);
    lemma_align_offset_congruence(al, ah1, ah2, ccs1[i as int], ccs2[i as int]);
    T::axiom_add_congruence_left(p1.top, p2.top, align_offset(al, ah1, ccs1[i as int]));
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        p2.top, align_offset(al, ah1, ccs1[i as int]), align_offset(al, ah2, ccs2[i as int]));
    T::axiom_eqv_transitive(
        p1.top.add(align_offset(al, ah1, ccs1[i as int])),
        p2.top.add(align_offset(al, ah1, ccs1[i as int])),
        p2.top.add(align_offset(al, ah2, ccs2[i as int])));
}

/// Flex Row full-depth dispatch.
pub proof fn lemma_flex_row_full_depth_dispatch<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    p1: Padding<T>, sp1: T, al: Alignment, ch1: Seq<FlexItem<T>>,
    w2: Widget<T>, fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(Widget::Container(ContainerWidget::Flex {
            padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Row, children: ch1 }), w2, fuel),
        fuel > 1, ch1.len() > 0,
        T::zero().lt(sum_weights(Seq::new(ch1.len(), |i: int| ch1[i].weight), ch1.len() as nat)),
    ensures crate::diff::nodes_deeply_eqv(
        layout_widget(lim1, Widget::Container(ContainerWidget::Flex {
            padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Row, children: ch1 }), fuel),
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
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), tw1);
        T::axiom_eqv_symmetric(T::zero(), tw1);
        let ts1 = repeated_add(sp1, (ch1.len() - 1) as nat);
        let ts2 = repeated_add(sp2, (ch2.len() - 1) as nat);
        lemma_repeated_add_congruence(sp1, sp2, (ch1.len() - 1) as nat);
        let am1 = inner1.max.width.sub(ts1);
        let am2 = inner2.max.width.sub(ts2);
        lemma_sub_congruence(inner1.max.width, inner2.max.width, ts1, ts2);
        lemma_sum_weights_congruence(w1s, w2s, w1s.len() as nat);
        assert(!tw1.eqv(T::zero()));
        let cn1 = flex_linear_widget_child_nodes(inner1, ch1, w1s, tw1, am1, Axis::Horizontal, (fuel - 1) as nat);
        let cn2 = flex_linear_widget_child_nodes(inner2, ch2, w2s, tw2, am2, Axis::Horizontal, (fuel - 1) as nat);
        let wc1 = Seq::new(ch1.len(), |i: int| ch1[i].child);
        let rd = min_children_congruence_depth(wc1, (fuel - 1) as nat, 0);
        assert forall|i: int| 0 <= i < cn1.len() implies
            crate::diff::nodes_deeply_eqv(#[trigger] cn1[i], cn2[i], rd)
        by {
            lemma_min_children_depth_le::<T>(wc1, (fuel - 1) as nat, 0, i);
            lemma_flex_child_main_size_congruence(w1s[i], w2s[i], tw1, tw2, am1, am2);
            lemma_layout_widget_full_depth_congruence(
                Limits { min: inner1.min, max: Size::new(flex_child_main_size(w1s[i], tw1, am1), inner1.max.height) },
                Limits { min: inner2.min, max: Size::new(flex_child_main_size(w2s[i], tw2, am2), inner2.max.height) },
                ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            crate::diff::lemma_deeply_eqv_depth_monotone(cn1[i], cn2[i],
                congruence_depth(ch1[i].child, (fuel - 1) as nat), rd);
        };
        lemma_sizes_eqv_from_deeply_eqv(cn1, cn2, rd);
        reveal(flex_row_layout);
        let ccs1 = Seq::new(cn1.len(), |i: int| cn1[i].size.height);
        let ccs2 = Seq::new(cn2.len(), |i: int| cn2[i].size.height);
        let fl1 = flex_row_layout(lim1, p1, sp1, al, w1s, ccs1);
        let fl2 = flex_row_layout(lim2, p2, sp2, al, w2s, ccs2);
        // flex_row_layout uses: available_width = max.width.sub(pad.horizontal()).sub(total_spacing)
        //                      available_height = max.height.sub(pad.vertical())
        let fwp1 = lim1.max.width.sub(p1.horizontal());
        let fwp2 = lim2.max.width.sub(p2.horizontal());
        lemma_sub_congruence(lim1.max.width, lim2.max.width, p1.horizontal(), p2.horizontal());
        let fw1 = fwp1.sub(ts1);
        let fw2 = fwp2.sub(ts2);
        lemma_sub_congruence(fwp1, fwp2, ts1, ts2);
        let fh1 = lim1.max.height.sub(p1.vertical());
        let fh2 = lim2.max.height.sub(p2.vertical());
        lemma_sub_congruence(lim1.max.height, lim2.max.height, p1.vertical(), p2.vertical());
        crate::layout::flex_proofs::lemma_flex_row_children_len(p1, sp1, al, w1s, ccs1, tw1, fw1, fh1, 0);
        crate::layout::flex_proofs::lemma_flex_row_children_len(p2, sp2, al, w2s, ccs2, tw2, fw2, fh2, 0);
        let fc1 = flex_row_children(p1, sp1, al, w1s, ccs1, tw1, fw1, fh1, 0);
        let fc2 = flex_row_children(p2, sp2, al, w2s, ccs2, tw2, fw2, fh2, 0);
        assert(fl1.children =~= fc1);
        assert(fl2.children =~= fc2);
        assert forall|i: int| 0 <= i < fc1.len() implies
            fc1[i].x.eqv(fc2[i].x) && fc1[i].y.eqv(fc2[i].y)
        by {
            lemma_flex_row_position_eqv_at(p1, p2, sp1, sp2, al, w1s, w2s, ccs1, ccs2,
                tw1, tw2, fw1, fw2, fh1, fh2, i as nat);
        };
        lemma_layout_widget_node_congruence(lim1, lim2,
            Widget::Container(ContainerWidget::Flex { padding: p1, spacing: sp1, alignment: al, direction: FlexDirection::Row, children: ch1 }), w2, fuel);
        lemma_merge_layout_deep_congruence_plus_one(fl1, fl2, cn1, cn2, rd);
    }
}


/// Grid per-index IH helper — separate for rlimit.
proof fn lemma_grid_child_ih_at<T: OrderedField>(
    inner1: Limits<T>, inner2: Limits<T>,
    cw1: Seq<Size<T>>, cw2: Seq<Size<T>>,
    rh1: Seq<Size<T>>, rh2: Seq<Size<T>>,
    ch1: Seq<Widget<T>>, ch2: Seq<Widget<T>>,
    fuel: nat, rd: nat, i: int,
)
    requires
        limits_eqv(inner1, inner2),
        sizes_eqv(cw1, cw2), sizes_eqv(rh1, rh2),
        ch1.len() == ch2.len(),
        ch1.len() == cw1.len() * rh1.len(),
        cw1.len() > 0, rh1.len() > 0,
        fuel > 1, 0 <= i < ch1.len(),
        forall|j: int| 0 <= j < ch1.len() ==> widget_eqv(ch1[j], ch2[j], (fuel - 1) as nat),
        rd == min_children_congruence_depth(ch1, (fuel - 1) as nat, 0),
    ensures ({
        let cn1 = grid_widget_child_nodes(inner1, cw1, rh1, ch1, cw1.len(), (fuel - 1) as nat);
        let cn2 = grid_widget_child_nodes(inner2, cw2, rh2, ch2, cw2.len(), (fuel - 1) as nat);
        crate::diff::nodes_deeply_eqv(cn1[i], cn2[i], rd)
    }),
    decreases fuel, 0nat,
{
    let c = i % cw1.len() as int;
    let r = i / cw1.len() as int;
    assert(c >= 0 && c < cw1.len() as int && r >= 0 && r < rh1.len() as int) by(nonlinear_arith)
        requires cw1.len() > 0, rh1.len() > 0, 0 <= i, i < cw1.len() as int * rh1.len() as int,
                 c == i % cw1.len() as int, r == i / cw1.len() as int;
    let cl1 = Limits { min: inner1.min, max: Size::new(cw1[c].width, rh1[r].height) };
    let cl2 = Limits { min: inner2.min, max: Size::new(cw2[c].width, rh2[r].height) };
    lemma_layout_widget_full_depth_congruence(cl1, cl2, ch1[i], ch2[i], (fuel - 1) as nat);
    lemma_min_children_depth_le::<T>(ch1, (fuel - 1) as nat, 0, i);
    let cn1 = grid_widget_child_nodes(inner1, cw1, rh1, ch1, cw1.len(), (fuel - 1) as nat);
    let cn2 = grid_widget_child_nodes(inner2, cw2, rh2, ch2, cw2.len(), (fuel - 1) as nat);
    crate::diff::lemma_deeply_eqv_depth_monotone(cn1[i], cn2[i],
        congruence_depth(ch1[i], (fuel - 1) as nat), rd);
}

/// Grid per-index position congruence helper.
proof fn lemma_grid_position_eqv_at<T: OrderedField>(
    p1: Padding<T>, p2: Padding<T>,
    cw1: Seq<Size<T>>, cw2: Seq<Size<T>>,
    rh1: Seq<Size<T>>, rh2: Seq<Size<T>>,
    hs1: T, hs2: T, vs1: T, vs2: T,
    ha: Alignment, va: Alignment,
    cs2d1: Seq<Seq<Size<T>>>, cs2d2: Seq<Seq<Size<T>>>,
    i: int,
)
    requires
        padding_eqv(p1, p2), hs1.eqv(hs2), vs1.eqv(vs2),
        sizes_eqv(cw1, cw2), sizes_eqv(rh1, rh2),
        cw1.len() > 0, rh1.len() > 0,
        0 <= i < cw1.len() as int * rh1.len() as int,
        cs2d1.len() >= rh1.len(), cs2d2.len() >= rh2.len(),
        forall|r: int| 0 <= r < cs2d1.len() ==> (#[trigger] cs2d1[r]).len() >= cw1.len(),
        forall|r: int| 0 <= r < cs2d2.len() ==> (#[trigger] cs2d2[r]).len() >= cw2.len(),
        forall|r: int, c: int| 0 <= r < rh1.len() && 0 <= c < cw1.len() ==>
            size_eqv(cs2d1[r][c], cs2d2[r][c]),
    ensures ({
        let gc1 = crate::layout::grid::grid_all_children(p1, cw1, rh1, hs1, vs1, ha, va, cs2d1, 0);
        let gc2 = crate::layout::grid::grid_all_children(p2, cw2, rh2, hs2, vs2, ha, va, cs2d2, 0);
        gc1[i].x.eqv(gc2[i].x) && gc1[i].y.eqv(gc2[i].y)
    }),
{
    let c = (i % cw1.len() as int) as nat;
    let r = (i / cw1.len() as int) as nat;
    assert(c < cw1.len() && r < rh1.len()) by(nonlinear_arith)
        requires cw1.len() > 0, rh1.len() > 0, 0 <= i, i < cw1.len() as int * rh1.len() as int,
                 c == (i % cw1.len() as int) as nat, r == (i / cw1.len() as int) as nat;
    // i = r * ncols + c (fundamental div/mod property)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, cw1.len() as int);
    crate::layout::grid_proofs::lemma_grid_all_children_element(
        p1, cw1, rh1, hs1, vs1, ha, va, cs2d1, r, c);
    crate::layout::grid_proofs::lemma_grid_all_children_element(
        p2, cw2, rh2, hs2, vs2, ha, va, cs2d2, r, c);
    lemma_grid_child_position_congruence(p1, p2, cw1, cw2, rh1, rh2, hs1, hs2, vs1, vs2,
        ha, va, r, c, cs2d1[r as int][c as int], cs2d2[r as int][c as int]);
}


/// Grid full-depth dispatch.
pub proof fn lemma_grid_full_depth_dispatch<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    p1: Padding<T>, hs1: T, vs1: T, ha: Alignment, va: Alignment,
    cw1: Seq<Size<T>>, rh1: Seq<Size<T>>, ch1: Seq<Widget<T>>,
    w2: Widget<T>, fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(Widget::Container(ContainerWidget::Grid {
            padding: p1, h_spacing: hs1, v_spacing: vs1, h_align: ha, v_align: va,
            col_widths: cw1, row_heights: rh1, children: ch1 }), w2, fuel),
        fuel > 1, ch1.len() > 0, cw1.len() > 0, rh1.len() > 0,
        ch1.len() == cw1.len() * rh1.len(),
    ensures crate::diff::nodes_deeply_eqv(
        layout_widget(lim1, Widget::Container(ContainerWidget::Grid {
            padding: p1, h_spacing: hs1, v_spacing: vs1, h_align: ha, v_align: va,
            col_widths: cw1, row_heights: rh1, children: ch1 }), fuel),
        layout_widget(lim2, w2, fuel),
        min_children_congruence_depth(ch1, (fuel - 1) as nat, 0) + 1),
    decreases fuel, 1nat,
{
    if let Widget::Container(ContainerWidget::Grid {
        padding: p2, h_spacing: hs2, v_spacing: vs2, col_widths: cw2, row_heights: rh2, children: ch2, ..
    }) = w2 {
        lemma_padding_horizontal_congruence(p1, p2);
        lemma_padding_vertical_congruence(p1, p2);
        lemma_shrink_congruence(lim1, lim2, p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
        let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
        let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
        let cn1 = grid_widget_child_nodes(inner1, cw1, rh1, ch1, cw1.len(), (fuel - 1) as nat);
        let cn2 = grid_widget_child_nodes(inner2, cw2, rh2, ch2, cw2.len(), (fuel - 1) as nat);
        let rd = min_children_congruence_depth(ch1, (fuel - 1) as nat, 0);
        // IH per child — use per-index helper
        assert forall|i: int| 0 <= i < ch1.len() as int implies
            crate::diff::nodes_deeply_eqv(#[trigger] cn1[i], cn2[i], rd)
        by {
            lemma_grid_child_ih_at(inner1, inner2, cw1, cw2, rh1, rh2, ch1, ch2, fuel, rd, i);
        };
        lemma_sizes_eqv_from_deeply_eqv(cn1, cn2, rd);
        // Grid layout + position congruence
        reveal(crate::layout::grid::grid_layout);
        let cs2d1 = Seq::new(rh1.len(), |r: int| Seq::new(cw1.len(), |c: int| cn1[(r * cw1.len() as int + c)].size));
        let cs2d2 = Seq::new(rh2.len(), |r: int| Seq::new(cw2.len(), |c: int| cn2[(r * cw2.len() as int + c)].size));
        let gl1 = crate::layout::grid::grid_layout(lim1, p1, hs1, vs1, ha, va, cw1, rh1, cs2d1);
        let gl2 = crate::layout::grid::grid_layout(lim2, p2, hs2, vs2, ha, va, cw2, rh2, cs2d2);
        lemma_grid_structural_bridge(lim1, p1, hs1, vs1, ha, va, cw1, rh1, ch1, fuel);
        lemma_grid_structural_bridge(lim2, p2, hs2, vs2, ha, va, cw2, rh2, ch2, fuel);
        crate::layout::grid_proofs::lemma_grid_all_children_len(p1, cw1, rh1, hs1, vs1, ha, va, cs2d1, 0, cw1.len());
        // Establish cs2d size eqv from cn size eqv
        assert(forall|r: int, c: int| 0 <= r < rh1.len() && 0 <= c < cw1.len() ==>
            size_eqv(cs2d1[r][c], cs2d2[r][c]));
        // Position congruence per child (ch1.len() == cw1.len() * rh1.len())
        assert forall|i: int| 0 <= i < ch1.len() as int implies
            gl1.children[i].x.eqv(gl2.children[i].x) && gl1.children[i].y.eqv(gl2.children[i].y)
        by {
            assert(i < cw1.len() as int * rh1.len() as int) by(nonlinear_arith)
                requires i < ch1.len() as int, ch1.len() == cw1.len() * rh1.len();
            lemma_grid_position_eqv_at(p1, p2, cw1, cw2, rh1, rh2, hs1, hs2, vs1, vs2,
                ha, va, cs2d1, cs2d2, i);
        };
        lemma_layout_widget_node_congruence(lim1, lim2,
            Widget::Container(ContainerWidget::Grid {
                padding: p1, h_spacing: hs1, v_spacing: vs1, h_align: ha, v_align: va,
                col_widths: cw1, row_heights: rh1, children: ch1 }), w2, fuel);
        lemma_merge_layout_deep_congruence_plus_one(gl1, gl2, cn1, cn2, rd);
    }
}

/// Absolute full-depth dispatch.
pub proof fn lemma_absolute_full_depth_dispatch<T: OrderedField>(
    lim1: Limits<T>, lim2: Limits<T>,
    p1: Padding<T>, ch1: Seq<AbsoluteChild<T>>,
    w2: Widget<T>, fuel: nat,
)
    requires
        limits_eqv(lim1, lim2),
        widget_eqv(Widget::Container(ContainerWidget::Absolute { padding: p1, children: ch1 }), w2, fuel),
        fuel > 1, ch1.len() > 0,
    ensures crate::diff::nodes_deeply_eqv(
        layout_widget(lim1, Widget::Container(ContainerWidget::Absolute { padding: p1, children: ch1 }), fuel),
        layout_widget(lim2, w2, fuel),
        min_children_congruence_depth(
            Seq::new(ch1.len(), |i: int| ch1[i].child), (fuel - 1) as nat, 0) + 1),
    decreases fuel, 1nat,
{
    if let Widget::Container(ContainerWidget::Absolute { padding: p2, children: ch2 }) = w2 {
        lemma_padding_horizontal_congruence(p1, p2);
        lemma_padding_vertical_congruence(p1, p2);
        lemma_shrink_congruence(lim1, lim2, p1.horizontal(), p2.horizontal(), p1.vertical(), p2.vertical());
        let inner1 = lim1.shrink(p1.horizontal(), p1.vertical());
        let inner2 = lim2.shrink(p2.horizontal(), p2.vertical());
        let cn1 = absolute_widget_child_nodes(inner1, ch1, (fuel - 1) as nat);
        let cn2 = absolute_widget_child_nodes(inner2, ch2, (fuel - 1) as nat);
        let wc1 = Seq::new(ch1.len(), |i: int| ch1[i].child);
        let rd = min_children_congruence_depth(wc1, (fuel - 1) as nat, 0);
        assert forall|i: int| 0 <= i < cn1.len() implies
            crate::diff::nodes_deeply_eqv(#[trigger] cn1[i], cn2[i], rd)
        by {
            lemma_layout_widget_full_depth_congruence(inner1, inner2, ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            lemma_min_children_depth_le::<T>(wc1, (fuel - 1) as nat, 0, i);
            crate::diff::lemma_deeply_eqv_depth_monotone(cn1[i], cn2[i],
                congruence_depth(ch1[i].child, (fuel - 1) as nat), rd);
        };
        lemma_sizes_eqv_from_deeply_eqv(cn1, cn2, rd);
        // Absolute layout
        let cd1 = Seq::new(cn1.len(), |i: int| (ch1[i].x, ch1[i].y, cn1[i].size));
        let cd2 = Seq::new(cn2.len(), |i: int| (ch2[i].x, ch2[i].y, cn2[i].size));
        reveal(crate::layout::absolute::absolute_layout);
        let al1 = crate::layout::absolute::absolute_layout(lim1, p1, cd1);
        let al2 = crate::layout::absolute::absolute_layout(lim2, p2, cd2);
        assert(abs_data_eqv(cd1, cd2));
        lemma_absolute_children_positions_congruence(p1, p2, cd1, cd2, 0);
        lemma_absolute_layout_children_len(lim1, p1, cd1);
        lemma_absolute_layout_children_len(lim2, p2, cd2);
        // Bridge: layout_widget == merge_layout(al_bridge, cn) where al_bridge uses bridge's cd
        lemma_absolute_structural_bridge(lim1, p1, ch1, fuel);
        lemma_absolute_structural_bridge(lim2, p2, ch2, fuel);
        // node_eqv: bridge gives layout_widget == merge_layout(al, cn)
        // node_congruence gives node_eqv(layout_widget, layout_widget)
        // Therefore node_eqv(merge_layout(al1, cn1), merge_layout(al2, cn2))
        lemma_layout_widget_node_congruence(lim1, lim2,
            Widget::Container(ContainerWidget::Absolute { padding: p1, children: ch1 }), w2, fuel);
        // merge+1: children at rd + positions eqv + node_eqv → depth rd+1
        lemma_merge_layout_deep_congruence_plus_one(al1, al2, cn1, cn2, rd);
        return;
    }
}

} // verus!
