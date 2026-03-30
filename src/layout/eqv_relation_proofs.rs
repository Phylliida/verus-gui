use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::limits::Limits;
use crate::widget::*;
use crate::layout::congruence_proofs::*;
use crate::layer::*;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::vec3::Vec3;

verus! {

//  ── Layer eqv relation helpers ───────────────────────────────────────

proof fn lemma_vec3_eqv_symmetric<T: OrderedRing>(a: Vec3<T>, b: Vec3<T>)
    requires vec3_eqv(a, b),
    ensures vec3_eqv(b, a),
{
    T::axiom_eqv_symmetric(a.x, b.x);
    T::axiom_eqv_symmetric(a.y, b.y);
    T::axiom_eqv_symmetric(a.z, b.z);
}

proof fn lemma_mat3_eqv_symmetric<T: OrderedRing>(a: Mat3x3<T>, b: Mat3x3<T>)
    requires mat3_eqv(a, b),
    ensures mat3_eqv(b, a),
{
    lemma_vec3_eqv_symmetric(a.row0, b.row0);
    lemma_vec3_eqv_symmetric(a.row1, b.row1);
    lemma_vec3_eqv_symmetric(a.row2, b.row2);
}

proof fn lemma_clip_rect_eqv_symmetric<T: OrderedRing>(a: ClipRect<T>, b: ClipRect<T>)
    requires clip_rect_eqv(a, b),
    ensures clip_rect_eqv(b, a),
{
    T::axiom_eqv_symmetric(a.x, b.x);
    T::axiom_eqv_symmetric(a.y, b.y);
    T::axiom_eqv_symmetric(a.width, b.width);
    T::axiom_eqv_symmetric(a.height, b.height);
}

proof fn lemma_layer_info_eqv_symmetric<T: OrderedRing>(a: LayerInfo<T>, b: LayerInfo<T>)
    requires layer_info_eqv(a, b),
    ensures layer_info_eqv(b, a),
{
    lemma_mat3_eqv_symmetric(a.transform, b.transform);
    T::axiom_eqv_symmetric(a.alpha, b.alpha);
    match (a.clip, b.clip) {
        (Some(ca), Some(cb)) => { lemma_clip_rect_eqv_symmetric(ca, cb); },
        _ => {},
    }
}

proof fn lemma_vec3_eqv_transitive<T: OrderedRing>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    requires vec3_eqv(a, b), vec3_eqv(b, c),
    ensures vec3_eqv(a, c),
{
    T::axiom_eqv_transitive(a.x, b.x, c.x);
    T::axiom_eqv_transitive(a.y, b.y, c.y);
    T::axiom_eqv_transitive(a.z, b.z, c.z);
}

proof fn lemma_mat3_eqv_transitive<T: OrderedRing>(a: Mat3x3<T>, b: Mat3x3<T>, c: Mat3x3<T>)
    requires mat3_eqv(a, b), mat3_eqv(b, c),
    ensures mat3_eqv(a, c),
{
    lemma_vec3_eqv_transitive(a.row0, b.row0, c.row0);
    lemma_vec3_eqv_transitive(a.row1, b.row1, c.row1);
    lemma_vec3_eqv_transitive(a.row2, b.row2, c.row2);
}

proof fn lemma_clip_rect_eqv_transitive<T: OrderedRing>(
    a: ClipRect<T>, b: ClipRect<T>, c: ClipRect<T>,
)
    requires clip_rect_eqv(a, b), clip_rect_eqv(b, c),
    ensures clip_rect_eqv(a, c),
{
    T::axiom_eqv_transitive(a.x, b.x, c.x);
    T::axiom_eqv_transitive(a.y, b.y, c.y);
    T::axiom_eqv_transitive(a.width, b.width, c.width);
    T::axiom_eqv_transitive(a.height, b.height, c.height);
}

proof fn lemma_layer_info_eqv_transitive<T: OrderedRing>(
    a: LayerInfo<T>, b: LayerInfo<T>, c: LayerInfo<T>,
)
    requires layer_info_eqv(a, b), layer_info_eqv(b, c),
    ensures layer_info_eqv(a, c),
{
    lemma_mat3_eqv_transitive(a.transform, b.transform, c.transform);
    T::axiom_eqv_transitive(a.alpha, b.alpha, c.alpha);
    match (a.clip, b.clip, c.clip) {
        (Some(ca), Some(cb), Some(cc)) => {
            lemma_clip_rect_eqv_transitive(ca, cb, cc);
        },
        _ => {},
    }
}

//  ══════════════════════════════════════════════════════════════════════
//  widget_eqv IS AN EQUIVALENCE RELATION
//
//  Symmetry:    widget_eqv(w1, w2, f) ==> widget_eqv(w2, w1, f)
//  Transitivity: widget_eqv(w1, w2, f) && widget_eqv(w2, w3, f) ==> widget_eqv(w1, w3, f)
//  Reflexivity: widget_eqv(w1, w2, f) ==> widget_eqv(w1, w1, f)  (derived)
//  ══════════════════════════════════════════════════════════════════════

//  ── Component helpers ────────────────────────────────────────────────

proof fn lemma_size_eqv_symmetric<T: OrderedRing>(a: Size<T>, b: Size<T>)
    requires size_eqv(a, b),
    ensures size_eqv(b, a),
{
    T::axiom_eqv_symmetric(a.width, b.width);
    T::axiom_eqv_symmetric(a.height, b.height);
}

proof fn lemma_size_eqv_transitive<T: OrderedRing>(a: Size<T>, b: Size<T>, c: Size<T>)
    requires size_eqv(a, b), size_eqv(b, c),
    ensures size_eqv(a, c),
{
    T::axiom_eqv_transitive(a.width, b.width, c.width);
    T::axiom_eqv_transitive(a.height, b.height, c.height);
}

proof fn lemma_size_eqv_reflexive<T: OrderedRing>(a: Size<T>)
    ensures size_eqv(a, a),
{
    T::axiom_eqv_reflexive(a.width);
    T::axiom_eqv_reflexive(a.height);
}

proof fn lemma_padding_eqv_symmetric<T: OrderedRing>(a: crate::padding::Padding<T>, b: crate::padding::Padding<T>)
    requires padding_eqv(a, b),
    ensures padding_eqv(b, a),
{
    T::axiom_eqv_symmetric(a.top, b.top);
    T::axiom_eqv_symmetric(a.right, b.right);
    T::axiom_eqv_symmetric(a.bottom, b.bottom);
    T::axiom_eqv_symmetric(a.left, b.left);
}

proof fn lemma_padding_eqv_transitive<T: OrderedRing>(
    a: crate::padding::Padding<T>, b: crate::padding::Padding<T>, c: crate::padding::Padding<T>,
)
    requires padding_eqv(a, b), padding_eqv(b, c),
    ensures padding_eqv(a, c),
{
    T::axiom_eqv_transitive(a.top, b.top, c.top);
    T::axiom_eqv_transitive(a.right, b.right, c.right);
    T::axiom_eqv_transitive(a.bottom, b.bottom, c.bottom);
    T::axiom_eqv_transitive(a.left, b.left, c.left);
}

proof fn lemma_padding_eqv_reflexive<T: OrderedRing>(a: crate::padding::Padding<T>)
    ensures padding_eqv(a, a),
{
    T::axiom_eqv_reflexive(a.top);
    T::axiom_eqv_reflexive(a.right);
    T::axiom_eqv_reflexive(a.bottom);
    T::axiom_eqv_reflexive(a.left);
}

proof fn lemma_limits_eqv_symmetric<T: OrderedRing>(a: Limits<T>, b: Limits<T>)
    requires limits_eqv(a, b),
    ensures limits_eqv(b, a),
{
    lemma_size_eqv_symmetric(a.min, b.min);
    lemma_size_eqv_symmetric(a.max, b.max);
}

proof fn lemma_limits_eqv_transitive<T: OrderedRing>(a: Limits<T>, b: Limits<T>, c: Limits<T>)
    requires limits_eqv(a, b), limits_eqv(b, c),
    ensures limits_eqv(a, c),
{
    lemma_size_eqv_transitive(a.min, b.min, c.min);
    lemma_size_eqv_transitive(a.max, b.max, c.max);
}

proof fn lemma_limits_eqv_reflexive<T: OrderedRing>(a: Limits<T>)
    ensures limits_eqv(a, a),
{
    lemma_size_eqv_reflexive(a.min);
    lemma_size_eqv_reflexive(a.max);
}

proof fn lemma_sizes_eqv_symmetric<T: OrderedRing>(a: Seq<Size<T>>, b: Seq<Size<T>>)
    requires sizes_eqv(a, b),
    ensures sizes_eqv(b, a),
{
    assert forall|i: int| 0 <= i < b.len() implies size_eqv(#[trigger] b[i], a[i])
    by { lemma_size_eqv_symmetric(a[i], b[i]); };
}

proof fn lemma_sizes_eqv_transitive<T: OrderedRing>(a: Seq<Size<T>>, b: Seq<Size<T>>, c: Seq<Size<T>>)
    requires sizes_eqv(a, b), sizes_eqv(b, c),
    ensures sizes_eqv(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies size_eqv(#[trigger] a[i], c[i])
    by { lemma_size_eqv_transitive(a[i], b[i], c[i]); };
}

//  ── Symmetry ─────────────────────────────────────────────────────────

///  widget_eqv is symmetric: w1 ≡ w2 implies w2 ≡ w1.
pub proof fn theorem_widget_eqv_symmetric<T: OrderedField>(
    w1: Widget<T>, w2: Widget<T>, fuel: nat,
)
    requires widget_eqv(w1, w2, fuel),
    ensures widget_eqv(w2, w1, fuel),
    decreases fuel, 2nat,
{
    if fuel == 0 { return; }
    match (w1, w2) {
        (Widget::Leaf(l1), Widget::Leaf(l2)) => {
            lemma_leaf_eqv_symmetric(l1, l2, fuel);
        },
        (Widget::Wrapper(wr1), Widget::Wrapper(wr2)) => {
            lemma_wrapper_eqv_symmetric(wr1, wr2, fuel);
        },
        (Widget::Container(c1), Widget::Container(c2)) => {
            lemma_container_eqv_symmetric(c1, c2, fuel);
        },
        _ => {},
    }
}

proof fn lemma_leaf_eqv_symmetric<T: OrderedField>(
    l1: LeafWidget<T>, l2: LeafWidget<T>, fuel: nat,
)
    requires fuel > 0, widget_eqv(Widget::Leaf(l1), Widget::Leaf(l2), fuel),
    ensures widget_eqv(Widget::Leaf(l2), Widget::Leaf(l1), fuel),
{
    match (l1, l2) {
        (LeafWidget::Leaf { size: s1 }, LeafWidget::Leaf { size: s2 }) => {
            lemma_size_eqv_symmetric(s1, s2);
        },
        (LeafWidget::TextInput { preferred_size: s1, .. },
         LeafWidget::TextInput { preferred_size: s2, .. }) => {
            lemma_size_eqv_symmetric(s1, s2);
        },
        _ => {},
    }
}

proof fn lemma_wrapper_eqv_symmetric<T: OrderedField>(
    wr1: WrapperWidget<T>, wr2: WrapperWidget<T>, fuel: nat,
)
    requires fuel > 0, widget_eqv(Widget::Wrapper(wr1), Widget::Wrapper(wr2), fuel),
    ensures widget_eqv(Widget::Wrapper(wr2), Widget::Wrapper(wr1), fuel),
    decreases fuel, 1nat,
{
    match (wr1, wr2) {
        (WrapperWidget::Margin { margin: m1, child: c1 },
         WrapperWidget::Margin { margin: m2, child: c2 }) => {
            lemma_padding_eqv_symmetric(m1, m2);
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        (WrapperWidget::Conditional { visible: v1, child: c1 },
         WrapperWidget::Conditional { visible: v2, child: c2 }) => {
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        (WrapperWidget::SizedBox { inner_limits: l1, child: c1 },
         WrapperWidget::SizedBox { inner_limits: l2, child: c2 }) => {
            lemma_limits_eqv_symmetric(l1, l2);
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        (WrapperWidget::AspectRatio { ratio: r1, child: c1 },
         WrapperWidget::AspectRatio { ratio: r2, child: c2 }) => {
            T::axiom_eqv_symmetric(r1, r2);
            //  !r1.eqv(zero) and r1.eqv(r2) → !r2.eqv(zero)
            //  Proof: if r2.eqv(zero), then r1.eqv(r2).eqv(zero) → r1.eqv(zero), contradiction
            if r2.eqv(T::zero()) {
                T::axiom_eqv_transitive(r1, r2, T::zero());
            }
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        (WrapperWidget::ScrollView { viewport: v1, scroll_x: sx1, scroll_y: sy1, child: c1 },
         WrapperWidget::ScrollView { viewport: v2, scroll_x: sx2, scroll_y: sy2, child: c2 }) => {
            lemma_size_eqv_symmetric(v1, v2);
            T::axiom_eqv_symmetric(sx1, sx2);
            T::axiom_eqv_symmetric(sy1, sy2);
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        (WrapperWidget::Layer { layer: l1, child: c1 },
         WrapperWidget::Layer { layer: l2, child: c2 }) => {
            lemma_layer_info_eqv_symmetric(l1, l2);
            theorem_widget_eqv_symmetric(*c1, *c2, (fuel - 1) as nat);
        },
        _ => {},
    }
}

proof fn lemma_container_eqv_symmetric<T: OrderedField>(
    c1: ContainerWidget<T>, c2: ContainerWidget<T>, fuel: nat,
)
    requires fuel > 0, widget_eqv(Widget::Container(c1), Widget::Container(c2), fuel),
    ensures widget_eqv(Widget::Container(c2), Widget::Container(c1), fuel),
    decreases fuel, 1nat,
{
    match (c1, c2) {
        (ContainerWidget::Column { padding: p1, spacing: s1, alignment: a1, children: ch1 },
         ContainerWidget::Column { padding: p2, spacing: s2, alignment: a2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            T::axiom_eqv_symmetric(s1, s2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        (ContainerWidget::Row { padding: p1, spacing: s1, alignment: a1, children: ch1 },
         ContainerWidget::Row { padding: p2, spacing: s2, alignment: a2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            T::axiom_eqv_symmetric(s1, s2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        (ContainerWidget::Stack { padding: p1, h_align: ha1, v_align: va1, children: ch1 },
         ContainerWidget::Stack { padding: p2, h_align: ha2, v_align: va2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        (ContainerWidget::Wrap { padding: p1, h_spacing: hs1, v_spacing: vs1, children: ch1 },
         ContainerWidget::Wrap { padding: p2, h_spacing: hs2, v_spacing: vs2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            T::axiom_eqv_symmetric(hs1, hs2);
            T::axiom_eqv_symmetric(vs1, vs2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        (ContainerWidget::Flex { padding: p1, spacing: s1, alignment: a1, direction: d1, children: ch1 },
         ContainerWidget::Flex { padding: p2, spacing: s2, alignment: a2, direction: d2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            T::axiom_eqv_symmetric(s1, s2);
            //  sum_weights congruence: !sw1.eqv(zero), sw1.eqv(sw2) → !sw2.eqv(zero)
            let w1s = Seq::new(ch1.len(), |i: int| ch1[i].weight);
            let w2s = Seq::new(ch2.len(), |i: int| ch2[i].weight);
            let sw1 = crate::layout::flex::sum_weights(w1s, w1s.len() as nat);
            let sw2 = crate::layout::flex::sum_weights(w2s, w2s.len() as nat);
            lemma_sum_weights_congruence(w1s, w2s, w1s.len() as nat);
            if sw2.eqv(T::zero()) {
                T::axiom_eqv_symmetric(sw1, sw2);
                T::axiom_eqv_transitive(sw1, sw2, T::zero());
            }
            assert forall|i: int| 0 <= i < ch2.len() implies {
                &&& ch2[i].weight.eqv(ch1[i].weight)
                &&& widget_eqv(ch2[i].child, ch1[i].child, (fuel - 1) as nat)
            } by {
                T::axiom_eqv_symmetric(ch1[i].weight, ch2[i].weight);
                theorem_widget_eqv_symmetric(ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            };
        },
        (ContainerWidget::Grid { padding: p1, h_spacing: hs1, v_spacing: vs1,
            h_align: ha1, v_align: va1, col_widths: cw1, row_heights: rh1, children: ch1 },
         ContainerWidget::Grid { padding: p2, h_spacing: hs2, v_spacing: vs2,
            h_align: ha2, v_align: va2, col_widths: cw2, row_heights: rh2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            T::axiom_eqv_symmetric(hs1, hs2);
            T::axiom_eqv_symmetric(vs1, vs2);
            lemma_sizes_eqv_symmetric(cw1, cw2);
            lemma_sizes_eqv_symmetric(rh1, rh2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        (ContainerWidget::Absolute { padding: p1, children: ch1 },
         ContainerWidget::Absolute { padding: p2, children: ch2 }) => {
            lemma_padding_eqv_symmetric(p1, p2);
            assert forall|i: int| 0 <= i < ch2.len() implies {
                &&& ch2[i].x.eqv(ch1[i].x)
                &&& ch2[i].y.eqv(ch1[i].y)
                &&& widget_eqv(ch2[i].child, ch1[i].child, (fuel - 1) as nat)
            } by {
                T::axiom_eqv_symmetric(ch1[i].x, ch2[i].x);
                T::axiom_eqv_symmetric(ch1[i].y, ch2[i].y);
                theorem_widget_eqv_symmetric(ch1[i].child, ch2[i].child, (fuel - 1) as nat);
            };
        },
        (ContainerWidget::ListView { spacing: s1, scroll_y: sy1, viewport: v1, children: ch1 },
         ContainerWidget::ListView { spacing: s2, scroll_y: sy2, viewport: v2, children: ch2 }) => {
            T::axiom_eqv_symmetric(s1, s2);
            T::axiom_eqv_symmetric(sy1, sy2);
            lemma_size_eqv_symmetric(v1, v2);
            assert forall|i: int| 0 <= i < ch2.len() implies
                widget_eqv(#[trigger] ch2[i], ch1[i], (fuel - 1) as nat)
            by { theorem_widget_eqv_symmetric(ch1[i], ch2[i], (fuel - 1) as nat); };
        },
        _ => {},
    }
}

//  ── Transitivity ─────────────────────────────────────────────────────

///  widget_eqv is transitive: w1 ≡ w2 and w2 ≡ w3 implies w1 ≡ w3.
pub proof fn theorem_widget_eqv_transitive<T: OrderedField>(
    w1: Widget<T>, w2: Widget<T>, w3: Widget<T>, fuel: nat,
)
    requires widget_eqv(w1, w2, fuel), widget_eqv(w2, w3, fuel),
    ensures widget_eqv(w1, w3, fuel),
    decreases fuel, 2nat,
{
    if fuel == 0 { return; }
    match (w1, w2) {
        (Widget::Leaf(l1), Widget::Leaf(l2)) => {
            if let Widget::Leaf(l3) = w3 {
                lemma_leaf_eqv_transitive(l1, l2, l3, fuel);
            }
        },
        (Widget::Wrapper(wr1), Widget::Wrapper(wr2)) => {
            if let Widget::Wrapper(wr3) = w3 {
                lemma_wrapper_eqv_transitive(wr1, wr2, wr3, fuel);
            }
        },
        (Widget::Container(c1), Widget::Container(c2)) => {
            if let Widget::Container(c3) = w3 {
                lemma_container_eqv_transitive(c1, c2, c3, fuel);
            }
        },
        _ => {},
    }
}

proof fn lemma_leaf_eqv_transitive<T: OrderedField>(
    l1: LeafWidget<T>, l2: LeafWidget<T>, l3: LeafWidget<T>, fuel: nat,
)
    requires fuel > 0,
        widget_eqv(Widget::Leaf(l1), Widget::Leaf(l2), fuel),
        widget_eqv(Widget::Leaf(l2), Widget::Leaf(l3), fuel),
    ensures widget_eqv(Widget::Leaf(l1), Widget::Leaf(l3), fuel),
{
    match (l1, l2, l3) {
        (LeafWidget::Leaf { size: s1 }, LeafWidget::Leaf { size: s2 }, LeafWidget::Leaf { size: s3 }) => {
            lemma_size_eqv_transitive(s1, s2, s3);
        },
        (LeafWidget::TextInput { preferred_size: s1, .. },
         LeafWidget::TextInput { preferred_size: s2, .. },
         LeafWidget::TextInput { preferred_size: s3, .. }) => {
            lemma_size_eqv_transitive(s1, s2, s3);
        },
        _ => {},
    }
}

proof fn lemma_wrapper_eqv_transitive<T: OrderedField>(
    wr1: WrapperWidget<T>, wr2: WrapperWidget<T>, wr3: WrapperWidget<T>, fuel: nat,
)
    requires fuel > 0,
        widget_eqv(Widget::Wrapper(wr1), Widget::Wrapper(wr2), fuel),
        widget_eqv(Widget::Wrapper(wr2), Widget::Wrapper(wr3), fuel),
    ensures widget_eqv(Widget::Wrapper(wr1), Widget::Wrapper(wr3), fuel),
    decreases fuel, 1nat,
{
    match (wr1, wr2) {
        (WrapperWidget::Margin { margin: m1, child: c1 },
         WrapperWidget::Margin { margin: m2, child: c2 }) => {
            if let WrapperWidget::Margin { margin: m3, child: c3 } = wr3 {
                lemma_padding_eqv_transitive(m1, m2, m3);
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        (WrapperWidget::Conditional { visible: v1, child: c1 },
         WrapperWidget::Conditional { visible: v2, child: c2 }) => {
            if let WrapperWidget::Conditional { visible: v3, child: c3 } = wr3 {
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        (WrapperWidget::SizedBox { inner_limits: l1, child: c1 },
         WrapperWidget::SizedBox { inner_limits: l2, child: c2 }) => {
            if let WrapperWidget::SizedBox { inner_limits: l3, child: c3 } = wr3 {
                lemma_limits_eqv_transitive(l1, l2, l3);
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        (WrapperWidget::AspectRatio { ratio: r1, child: c1 },
         WrapperWidget::AspectRatio { ratio: r2, child: c2 }) => {
            if let WrapperWidget::AspectRatio { ratio: r3, child: c3 } = wr3 {
                T::axiom_eqv_transitive(r1, r2, r3);
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        (WrapperWidget::ScrollView { viewport: v1, scroll_x: sx1, scroll_y: sy1, child: c1 },
         WrapperWidget::ScrollView { viewport: v2, scroll_x: sx2, scroll_y: sy2, child: c2 }) => {
            if let WrapperWidget::ScrollView { viewport: v3, scroll_x: sx3, scroll_y: sy3, child: c3 } = wr3 {
                lemma_size_eqv_transitive(v1, v2, v3);
                T::axiom_eqv_transitive(sx1, sx2, sx3);
                T::axiom_eqv_transitive(sy1, sy2, sy3);
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        (WrapperWidget::Layer { layer: l1, child: c1 },
         WrapperWidget::Layer { layer: l2, child: c2 }) => {
            if let WrapperWidget::Layer { layer: l3, child: c3 } = wr3 {
                lemma_layer_info_eqv_transitive(l1, l2, l3);
                theorem_widget_eqv_transitive(*c1, *c2, *c3, (fuel - 1) as nat);
            }
        },
        _ => {},
    }
}

proof fn lemma_container_eqv_transitive<T: OrderedField>(
    c1: ContainerWidget<T>, c2: ContainerWidget<T>, c3: ContainerWidget<T>, fuel: nat,
)
    requires fuel > 0,
        widget_eqv(Widget::Container(c1), Widget::Container(c2), fuel),
        widget_eqv(Widget::Container(c2), Widget::Container(c3), fuel),
    ensures widget_eqv(Widget::Container(c1), Widget::Container(c3), fuel),
    decreases fuel, 1nat,
{
    match (c1, c2) {
        (ContainerWidget::Column { padding: p1, spacing: s1, alignment: a1, children: ch1 },
         ContainerWidget::Column { padding: p2, spacing: s2, alignment: a2, children: ch2 }) => {
            if let ContainerWidget::Column { padding: p3, spacing: s3, alignment: a3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                T::axiom_eqv_transitive(s1, s2, s3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        (ContainerWidget::Row { padding: p1, spacing: s1, alignment: a1, children: ch1 },
         ContainerWidget::Row { padding: p2, spacing: s2, alignment: a2, children: ch2 }) => {
            if let ContainerWidget::Row { padding: p3, spacing: s3, alignment: a3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                T::axiom_eqv_transitive(s1, s2, s3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        (ContainerWidget::Stack { padding: p1, h_align: ha1, v_align: va1, children: ch1 },
         ContainerWidget::Stack { padding: p2, h_align: ha2, v_align: va2, children: ch2 }) => {
            if let ContainerWidget::Stack { padding: p3, h_align: ha3, v_align: va3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        (ContainerWidget::Wrap { padding: p1, h_spacing: hs1, v_spacing: vs1, children: ch1 },
         ContainerWidget::Wrap { padding: p2, h_spacing: hs2, v_spacing: vs2, children: ch2 }) => {
            if let ContainerWidget::Wrap { padding: p3, h_spacing: hs3, v_spacing: vs3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                T::axiom_eqv_transitive(hs1, hs2, hs3);
                T::axiom_eqv_transitive(vs1, vs2, vs3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        (ContainerWidget::Flex { padding: p1, spacing: s1, alignment: a1, direction: d1, children: ch1 },
         ContainerWidget::Flex { padding: p2, spacing: s2, alignment: a2, direction: d2, children: ch2 }) => {
            if let ContainerWidget::Flex { padding: p3, spacing: s3, alignment: a3, direction: d3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                T::axiom_eqv_transitive(s1, s2, s3);
                assert forall|i: int| 0 <= i < ch1.len() implies {
                    &&& ch1[i].weight.eqv(ch3[i].weight)
                    &&& widget_eqv(ch1[i].child, ch3[i].child, (fuel - 1) as nat)
                } by {
                    T::axiom_eqv_transitive(ch1[i].weight, ch2[i].weight, ch3[i].weight);
                    theorem_widget_eqv_transitive(ch1[i].child, ch2[i].child, ch3[i].child, (fuel - 1) as nat);
                };
            }
        },
        (ContainerWidget::Grid { padding: p1, h_spacing: hs1, v_spacing: vs1,
            h_align: ha1, v_align: va1, col_widths: cw1, row_heights: rh1, children: ch1 },
         ContainerWidget::Grid { padding: p2, h_spacing: hs2, v_spacing: vs2,
            h_align: ha2, v_align: va2, col_widths: cw2, row_heights: rh2, children: ch2 }) => {
            if let ContainerWidget::Grid { padding: p3, h_spacing: hs3, v_spacing: vs3,
                h_align: ha3, v_align: va3, col_widths: cw3, row_heights: rh3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                T::axiom_eqv_transitive(hs1, hs2, hs3);
                T::axiom_eqv_transitive(vs1, vs2, vs3);
                lemma_sizes_eqv_transitive(cw1, cw2, cw3);
                lemma_sizes_eqv_transitive(rh1, rh2, rh3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        (ContainerWidget::Absolute { padding: p1, children: ch1 },
         ContainerWidget::Absolute { padding: p2, children: ch2 }) => {
            if let ContainerWidget::Absolute { padding: p3, children: ch3 } = c3 {
                lemma_padding_eqv_transitive(p1, p2, p3);
                assert forall|i: int| 0 <= i < ch1.len() implies {
                    &&& ch1[i].x.eqv(ch3[i].x)
                    &&& ch1[i].y.eqv(ch3[i].y)
                    &&& widget_eqv(ch1[i].child, ch3[i].child, (fuel - 1) as nat)
                } by {
                    T::axiom_eqv_transitive(ch1[i].x, ch2[i].x, ch3[i].x);
                    T::axiom_eqv_transitive(ch1[i].y, ch2[i].y, ch3[i].y);
                    theorem_widget_eqv_transitive(ch1[i].child, ch2[i].child, ch3[i].child, (fuel - 1) as nat);
                };
            }
        },
        (ContainerWidget::ListView { spacing: s1, scroll_y: sy1, viewport: v1, children: ch1 },
         ContainerWidget::ListView { spacing: s2, scroll_y: sy2, viewport: v2, children: ch2 }) => {
            if let ContainerWidget::ListView { spacing: s3, scroll_y: sy3, viewport: v3, children: ch3 } = c3 {
                T::axiom_eqv_transitive(s1, s2, s3);
                T::axiom_eqv_transitive(sy1, sy2, sy3);
                lemma_size_eqv_transitive(v1, v2, v3);
                assert forall|i: int| 0 <= i < ch1.len() implies
                    widget_eqv(#[trigger] ch1[i], ch3[i], (fuel - 1) as nat)
                by { theorem_widget_eqv_transitive(ch1[i], ch2[i], ch3[i], (fuel - 1) as nat); };
            }
        },
        _ => {},
    }
}

//  ── Reflexivity (derived from symmetry + transitivity) ───────────────

///  widget_eqv reflexivity for participating widgets:
///  if w is eqv to anything, it's eqv to itself.
pub proof fn theorem_widget_eqv_reflexive<T: OrderedField>(
    w1: Widget<T>, w2: Widget<T>, fuel: nat,
)
    requires widget_eqv(w1, w2, fuel),
    ensures widget_eqv(w1, w1, fuel),
{
    theorem_widget_eqv_symmetric(w1, w2, fuel);
    theorem_widget_eqv_transitive(w1, w2, w1, fuel);
}

} //  verus!
