use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::inequalities::lemma_nonneg_add;
use verus_algebra::min_max::{max, lemma_max_ge_left, lemma_max_ge_right};
use crate::size::Size;
use crate::node::Node;
use crate::padding::Padding;
use crate::layout::wrap::*;

verus! {

///  Length of wrap_children sequence.
pub proof fn lemma_wrap_children_len<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    index: nat,
)
    requires
        index <= child_sizes.len(),
    ensures
        wrap_children(
            padding, h_spacing, v_spacing, child_sizes, available_width, index,
        ).len() == child_sizes.len() - index,
    decreases child_sizes.len() - index,
{
    if index >= child_sizes.len() {
    } else {
        lemma_wrap_children_len(
            padding, h_spacing, v_spacing, child_sizes, available_width, index + 1,
        );
    }
}

///  Element access: wrap_children[k] is a leaf at the correct position.
pub proof fn lemma_wrap_children_element<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    k: nat,
)
    requires
        k < child_sizes.len(),
    ensures
        ({
            let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k);
            let child = child_sizes[k as int];
            let needs_break = wrap_needs_break(cursor.x, child.width, available_width);
            let cx = if needs_break { T::zero() } else { cursor.x };
            let cy = if needs_break {
                cursor.y.add(cursor.line_height).add(v_spacing)
            } else {
                cursor.y
            };
            wrap_children(
                padding, h_spacing, v_spacing, child_sizes, available_width, 0,
            )[k as int] == Node::leaf(padding.left.add(cx), padding.top.add(cy), child)
        }),
{
    lemma_wrap_children_element_shifted(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0, k,
    );
}

proof fn lemma_wrap_children_element_shifted<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    start: nat,
    k: nat,
)
    requires
        start <= k,
        k < child_sizes.len(),
    ensures
        ({
            let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k);
            let child = child_sizes[k as int];
            let needs_break = wrap_needs_break(cursor.x, child.width, available_width);
            let cx = if needs_break { T::zero() } else { cursor.x };
            let cy = if needs_break {
                cursor.y.add(cursor.line_height).add(v_spacing)
            } else {
                cursor.y
            };
            wrap_children(
                padding, h_spacing, v_spacing, child_sizes, available_width, start,
            )[(k - start) as int] == Node::leaf(padding.left.add(cx), padding.top.add(cy), child)
        }),
    decreases k - start,
{
    if start == k {
    } else {
        lemma_wrap_children_len(
            padding, h_spacing, v_spacing, child_sizes, available_width, start + 1,
        );
        lemma_wrap_children_len(
            padding, h_spacing, v_spacing, child_sizes, available_width, start,
        );
        lemma_wrap_children_element_shifted(
            padding, h_spacing, v_spacing, child_sizes, available_width, start + 1, k,
        );
        let tail = wrap_children(
            padding, h_spacing, v_spacing, child_sizes, available_width, start + 1,
        );
        let sc = wrap_children(
            padding, h_spacing, v_spacing, child_sizes, available_width, start,
        );
        assert(sc[(k - start) as int] == tail[((k - start) as int) - 1]);
    }
}

//  ── Algebraic helper ──────────────────────────────────────────────

///  a <= a + b when b >= 0.
proof fn lemma_le_add_nonneg<T: OrderedRing>(a: T, b: T)
    requires
        T::zero().le(b),
    ensures
        a.le(a.add(b)),
{
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    T::axiom_le_add_monotone(T::zero(), b, a);
    //  T::zero().add(a).le(b.add(a))
    lemma_add_zero_left::<T>(a);
    T::axiom_add_commutative(b, a);
    T::axiom_le_congruence(
        T::zero().add(a), a,
        b.add(a), a.add(b),
    );
}

//  ── Cursor nonneg ─────────────────────────────────────────────────

///  All cursor fields are nonneg when child sizes and spacings are nonneg.
pub proof fn lemma_wrap_cursor_nonneg<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    count: nat,
)
    requires
        count <= child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
    ensures
        ({
            let c = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, count);
            &&& T::zero().le(c.x)
            &&& T::zero().le(c.y)
            &&& T::zero().le(c.line_height)
            &&& T::zero().le(c.content_width)
        }),
    decreases count,
{
    if count == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        lemma_wrap_cursor_nonneg(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        let prev = wrap_cursor(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        let child = child_sizes[(count - 1) as int];
        if wrap_needs_break(prev.x, child.width, available_width) {
            //  x = child.width + h_spacing
            lemma_nonneg_add::<T>(child.width, h_spacing);
            //  y = prev.y + prev.line_height + v_spacing
            lemma_nonneg_add::<T>(prev.y, prev.line_height);
            lemma_nonneg_add::<T>(prev.y.add(prev.line_height), v_spacing);
            //  line_height = child.height (nonneg by assumption)
            //  content_width = max(prev.content_width, child.width) >= prev.content_width >= 0
            lemma_max_ge_left::<T>(prev.content_width, child.width);
            T::axiom_le_transitive(
                T::zero(), prev.content_width, max::<T>(prev.content_width, child.width),
            );
        } else {
            //  x = prev.x + child.width + h_spacing
            lemma_nonneg_add::<T>(prev.x, child.width);
            lemma_nonneg_add::<T>(prev.x.add(child.width), h_spacing);
            //  y = prev.y (nonneg by IH)
            //  line_height = max(prev.line_height, child.height) >= prev.line_height >= 0
            lemma_max_ge_left::<T>(prev.line_height, child.height);
            T::axiom_le_transitive(
                T::zero(), prev.line_height, max::<T>(prev.line_height, child.height),
            );
            //  content_width = max(prev.content_width, prev.x + child.width)
            lemma_nonneg_add::<T>(prev.x, child.width);
            lemma_max_ge_left::<T>(prev.content_width, prev.x.add(child.width));
            T::axiom_le_transitive(
                T::zero(),
                prev.content_width,
                max::<T>(prev.content_width, prev.x.add(child.width)),
            );
        }
    }
}

//  ── Child position bounds ─────────────────────────────────────────

///  Each child in a wrap layout is positioned at x >= padding.left and y >= padding.top.
pub proof fn lemma_wrap_child_position_nonneg<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    k: nat,
)
    requires
        k < child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        T::zero().le(padding.left),
        T::zero().le(padding.top),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
    ensures
        ({
            let children = wrap_children(
                padding, h_spacing, v_spacing, child_sizes, available_width, 0,
            );
            &&& padding.left.le(children[k as int].x)
            &&& padding.top.le(children[k as int].y)
        }),
{
    lemma_wrap_children_element(
        padding, h_spacing, v_spacing, child_sizes, available_width, k,
    );
    lemma_wrap_cursor_nonneg(
        child_sizes, h_spacing, v_spacing, available_width, k,
    );
    let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k);
    let child = child_sizes[k as int];
    let needs_break = wrap_needs_break(cursor.x, child.width, available_width);
    let cx = if needs_break { T::zero() } else { cursor.x };
    let cy = if needs_break {
        cursor.y.add(cursor.line_height).add(v_spacing)
    } else {
        cursor.y
    };
    //  cx >= 0 (either zero or cursor.x which is nonneg)
    if needs_break {
        T::axiom_le_reflexive(T::zero());
    }
    //  cy >= 0 (either cursor.y or cursor.y + cursor.line_height + v_spacing, both nonneg)
    if needs_break {
        lemma_nonneg_add::<T>(cursor.y, cursor.line_height);
        lemma_nonneg_add::<T>(cursor.y.add(cursor.line_height), v_spacing);
    }
    //  padding.left + cx >= padding.left (since cx >= 0)
    assert(T::zero().le(cx));
    T::axiom_le_add_monotone(T::zero(), cx, padding.left);
    //  0 + padding.left <= cx + padding.left
    //  Need: padding.left <= padding.left + cx
    //  axiom_le_add_monotone gives: 0.add(padding.left).le(cx.add(padding.left))
    //  i.e. padding.left.le(cx.add(padding.left)) via zero+padding.left eqv padding.left
    //  But we need padding.left.le(padding.left.add(cx))
    //  Use commutativity: padding.left.add(cx) == cx.add(padding.left) via axiom_add_commutative
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    lemma_add_zero_left::<T>(padding.left);
    //  T::zero().add(padding.left).eqv(padding.left)
    T::axiom_add_commutative(cx, padding.left);
    //  cx.add(padding.left).eqv(padding.left.add(cx))
    T::axiom_le_congruence(
        T::zero().add(padding.left),
        padding.left,
        cx.add(padding.left),
        padding.left.add(cx),
    );

    //  Similarly for y: padding.top + cy >= padding.top
    assert(T::zero().le(cy));
    T::axiom_le_add_monotone(T::zero(), cy, padding.top);
    lemma_add_zero_left::<T>(padding.top);
    T::axiom_add_commutative(cy, padding.top);
    T::axiom_le_congruence(
        T::zero().add(padding.top),
        padding.top,
        cy.add(padding.top),
        padding.top.add(cy),
    );

    //  Connect to actual children via element lemma
    let children = wrap_children(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );
    lemma_wrap_children_len(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );
    assert(children[k as int] == Node::leaf(padding.left.add(cx), padding.top.add(cy), child));
    assert(children[k as int].x == padding.left.add(cx));
    assert(children[k as int].y == padding.top.add(cy));
}

//  ── Same-line horizontal non-overlapping ──────────────────────────

///  Consecutive children on the same line don't overlap horizontally.
///
///  When child k+1 does not trigger a line break, the right edge of child k
///  is at or before the left edge of child k+1.
pub proof fn lemma_wrap_same_line_nonoverlapping<T: OrderedRing>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    available_width: T,
    k: nat,
)
    requires
        (k + 1) < child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        T::zero().le(padding.left),
        T::zero().le(padding.top),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        //  No break at k+1 (child k+1 stays on the same line)
        !wrap_needs_break(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k + 1).x,
            child_sizes[(k + 1) as int].width,
            available_width,
        ),
    ensures
        ({
            let children = wrap_children(
                padding, h_spacing, v_spacing, child_sizes, available_width, 0,
            );
            children[k as int].x.add(child_sizes[k as int].width)
                .le(children[(k + 1) as int].x)
        }),
{
    //  Get element positions
    lemma_wrap_children_element(
        padding, h_spacing, v_spacing, child_sizes, available_width, k,
    );
    lemma_wrap_children_element(
        padding, h_spacing, v_spacing, child_sizes, available_width, k + 1,
    );
    lemma_wrap_children_len(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );

    let cursor_k = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k);
    let cursor_k1 = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k + 1);
    let child_k = child_sizes[k as int];
    let child_k1 = child_sizes[(k + 1) as int];

    let needs_break_k = wrap_needs_break(cursor_k.x, child_k.width, available_width);
    let cx_k = if needs_break_k { T::zero() } else { cursor_k.x };
    //  No break at k+1 (given), so cx_{k+1} = cursor_{k+1}.x
    let cx_k1 = cursor_k1.x;

    //  Key: cursor_{k+1}.x = cx_k + child_k.width + h_spacing (from wrap_cursor definition)
    //  Whether or not there was a break at k:
    //    break at k → cursor_{k+1}.x = child_k.width + h_spacing = zero + child_k.width + h_spacing
    //    no break at k → cursor_{k+1}.x = cursor_k.x + child_k.width + h_spacing = cx_k + child_k.width + h_spacing
    //  In both cases: cursor_{k+1}.x = cx_k.add(child_k.width).add(h_spacing)

    //  Need: padding.left + cx_k + child_k.width <= padding.left + cx_k1
    //  i.e.  cx_k + child_k.width <= cx_k1
    //  i.e.  cx_k + child_k.width <= cx_k + child_k.width + h_spacing (via cursor relation)
    //  i.e.  a <= a + h_spacing where a = cx_k + child_k.width

    //  First establish cursor nonneg for cx_k >= 0
    lemma_wrap_cursor_nonneg(
        child_sizes, h_spacing, v_spacing, available_width, k,
    );

    //  cx_k.add(child_k.width) <= cx_k.add(child_k.width).add(h_spacing)
    if needs_break_k {
        //  cx_k = zero, cursor_{k+1}.x = child_k.width.add(h_spacing)
        //  Need: zero.add(child_k.width).le(child_k.width.add(h_spacing))
        use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
        lemma_add_zero_left::<T>(child_k.width);
        //  zero.add(child_k.width).eqv(child_k.width)
        lemma_le_add_nonneg(child_k.width, h_spacing);
        //  child_k.width.le(child_k.width.add(h_spacing))
        T::axiom_eqv_symmetric(T::zero().add(child_k.width), child_k.width);
        //  child_k.width.eqv(zero.add(child_k.width))
        T::axiom_eqv_reflexive(child_k.width.add(h_spacing));
        T::axiom_le_congruence(
            child_k.width, T::zero().add(child_k.width),
            child_k.width.add(h_spacing), child_k.width.add(h_spacing),
        );
        //  zero.add(child_k.width).le(child_k.width.add(h_spacing))
    } else {
        //  cx_k = cursor_k.x, cursor_{k+1}.x = cursor_k.x.add(child_k.width).add(h_spacing)
        //  Need: cursor_k.x.add(child_k.width).le(cursor_k.x.add(child_k.width).add(h_spacing))
        lemma_le_add_nonneg(cursor_k.x.add(child_k.width), h_spacing);
    }

    //  Now we have: cx_k.add(child_k.width).le(cx_k1)
    //  Need: padding.left.add(cx_k).add(child_k.width).le(padding.left.add(cx_k1))
    //  Use add_monotone: cx_k.add(child_k.width).le(cx_k1) implies
    //    cx_k.add(child_k.width).add(padding.left).le(cx_k1.add(padding.left))
    T::axiom_le_add_monotone(
        cx_k.add(child_k.width), cx_k1, padding.left,
    );
    //  cx_k.add(child_k.width).add(padding.left).le(cx_k1.add(padding.left))

    //  Need to show LHS = padding.left.add(cx_k).add(child_k.width) and RHS = padding.left.add(cx_k1)
    //  via associativity + commutativity
    T::axiom_add_associative(padding.left, cx_k, child_k.width);
    //  padding.left.add(cx_k).add(child_k.width).eqv(padding.left.add(cx_k.add(child_k.width)))
    //  a1 = cx_k.add(child_k.width).add(padding.left), we proved a1.le(cx_k1.add(padding.left))
    //  a2 = padding.left.add(cx_k).add(child_k.width) [desired LHS]
    //  b2 = padding.left.add(cx_k1) [desired RHS]
    //  Need: a1.eqv(a2) via commutativity+associativity, b1.eqv(b2) via commutativity

    //  a1 → a2: cx_k.add(child_k.width).add(padding.left) → padding.left.add(cx_k).add(child_k.width)
    T::axiom_add_commutative(cx_k.add(child_k.width), padding.left);
    //  cx_k.add(child_k.width).add(padding.left).eqv(padding.left.add(cx_k.add(child_k.width)))
    T::axiom_add_associative(padding.left, cx_k, child_k.width);
    //  padding.left.add(cx_k).add(child_k.width).eqv(padding.left.add(cx_k.add(child_k.width)))
    T::axiom_eqv_symmetric(
        padding.left.add(cx_k).add(child_k.width),
        padding.left.add(cx_k.add(child_k.width)),
    );
    //  padding.left.add(cx_k.add(child_k.width)).eqv(padding.left.add(cx_k).add(child_k.width))
    T::axiom_eqv_transitive(
        cx_k.add(child_k.width).add(padding.left),
        padding.left.add(cx_k.add(child_k.width)),
        padding.left.add(cx_k).add(child_k.width),
    );
    //  cx_k.add(child_k.width).add(padding.left).eqv(padding.left.add(cx_k).add(child_k.width))

    //  b1 → b2: cx_k1.add(padding.left) → padding.left.add(cx_k1)
    T::axiom_add_commutative(cx_k1, padding.left);
    //  cx_k1.add(padding.left).eqv(padding.left.add(cx_k1))

    T::axiom_le_congruence(
        cx_k.add(child_k.width).add(padding.left),
        padding.left.add(cx_k).add(child_k.width),
        cx_k1.add(padding.left),
        padding.left.add(cx_k1),
    );
    //  padding.left.add(cx_k).add(child_k.width).le(padding.left.add(cx_k1))

    //  Connect to children array
    let children = wrap_children(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );
    assert(children[k as int].x == padding.left.add(cx_k));
    assert(children[(k + 1) as int].x == padding.left.add(cx_k1));
}

//  ── Cursor monotonicity ──────────────────────────────────────────

///  cursor.content_width is monotonically non-decreasing.
proof fn lemma_wrap_cursor_cw_monotone<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    k: nat,
    n: nat,
)
    requires
        k <= n,
        n <= child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
    ensures
        wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).content_width.le(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, n).content_width),
    decreases n - k,
{
    if k == n {
        T::axiom_le_reflexive(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).content_width);
    } else {
        lemma_wrap_cursor_cw_monotone(child_sizes, h_spacing, v_spacing, available_width, k, (n - 1) as nat);
        let prev = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, (n - 1) as nat);
        let child = child_sizes[(n - 1) as int];
        if wrap_needs_break(prev.x, child.width, available_width) {
            lemma_max_ge_left::<T>(prev.content_width, child.width);
        } else {
            lemma_max_ge_left::<T>(prev.content_width, prev.x.add(child.width));
        }
        T::axiom_le_transitive(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).content_width,
            prev.content_width,
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, n).content_width,
        );
    }
}

///  cursor.y + cursor.line_height is monotonically non-decreasing.
proof fn lemma_wrap_cursor_ylh_monotone<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    k: nat,
    n: nat,
)
    requires
        k <= n,
        n <= child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
    ensures
        wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).y.add(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).line_height
        ).le(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, n).y.add(
                wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, n).line_height)),
    decreases n - k,
{
    if k == n {
        T::axiom_le_reflexive(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).y.add(
                wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).line_height));
    } else {
        lemma_wrap_cursor_ylh_monotone(
            child_sizes, h_spacing, v_spacing, available_width, k, (n - 1) as nat,
        );
        let prev = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, (n - 1) as nat);
        let cur = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, n);
        let child = child_sizes[(n - 1) as int];
        if wrap_needs_break(prev.x, child.width, available_width) {
            //  cur.y = prev.y + prev.line_height + v_spacing, cur.line_height = child.height
            //  cur.y + cur.lh = prev.y + prev.lh + v_spacing + child.height >= prev.y + prev.lh
            lemma_nonneg_add::<T>(v_spacing, child.height);
            lemma_le_add_nonneg(prev.y.add(prev.line_height), v_spacing.add(child.height));
            //  Need assoc: (prev.y + prev.lh) + (v_sp + child.h) = prev.y + prev.lh + v_sp + child.h
            T::axiom_add_associative(prev.y.add(prev.line_height), v_spacing, child.height);
            T::axiom_eqv_symmetric(
                prev.y.add(prev.line_height).add(v_spacing).add(child.height),
                prev.y.add(prev.line_height).add(v_spacing.add(child.height)),
            );
            verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                prev.y.add(prev.line_height),
                prev.y.add(prev.line_height).add(v_spacing.add(child.height)),
                cur.y.add(cur.line_height),
            );
        } else {
            //  cur.y = prev.y, cur.line_height = max(prev.line_height, child.height)
            //  cur.y + cur.lh = prev.y + max(prev.lh, child.h) >= prev.y + prev.lh
            lemma_max_ge_left::<T>(prev.line_height, child.height);
            T::axiom_le_add_monotone(prev.line_height, max::<T>(prev.line_height, child.height), prev.y);
            T::axiom_add_commutative(prev.line_height, prev.y);
            T::axiom_add_commutative(max::<T>(prev.line_height, child.height), prev.y);
            T::axiom_le_congruence(
                prev.line_height.add(prev.y), prev.y.add(prev.line_height),
                max::<T>(prev.line_height, child.height).add(prev.y),
                prev.y.add(max::<T>(prev.line_height, child.height)),
            );
        }
        T::axiom_le_transitive(
            wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).y.add(
                wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, k).line_height),
            prev.y.add(prev.line_height),
            cur.y.add(cur.line_height),
        );
    }
}

//  ── Wrap CWB ─────────────────────────────────────────────────────

///  Helper: per-child X upper bound for wrap layout.
proof fn lemma_wrap_child_x_upper_bound<T: OrderedField>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    avail_w: T,
    content_width: T,
    parent_w: T,
    i: int,
)
    requires
        padding.is_nonneg(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        0 <= i < child_sizes.len(),
        child_sizes.len() > 0,
        forall|k: int| 0 <= k < child_sizes.len() ==>
            T::zero().le(child_sizes[k].width) && T::zero().le(child_sizes[k].height),
        forall|k: int| 0 <= k < child_sizes.len() ==>
            child_sizes[k].width.le(avail_w),
        content_width == wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w,
            child_sizes.len() as nat).content_width,
        padding.horizontal().add(content_width).le(parent_w),
    ensures ({
        let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, i as nat);
        let child = child_sizes[i];
        let needs_break = wrap_needs_break(cursor.x, child.width, avail_w);
        let cx = if needs_break { T::zero() } else { cursor.x };
        padding.left.add(cx).add(child.width).le(parent_w)
    }),
{
    let n = child_sizes.len() as nat;
    let h = padding.horizontal();
    let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, i as nat);
    let child = child_sizes[i];
    let needs_break = wrap_needs_break(cursor.x, child.width, avail_w);
    let cx = if needs_break { T::zero() } else { cursor.x };
    let cursor_i1 = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, (i + 1) as nat);

    //  Step 1: cx + child.width <= cursor_i1.content_width
    if needs_break {
        lemma_max_ge_right::<T>(cursor.content_width, child.width);
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(child.width);
        T::axiom_eqv_symmetric(T::zero().add(child.width), child.width);
        verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            child.width, T::zero().add(child.width), cursor_i1.content_width,
        );
    } else {
        lemma_max_ge_right::<T>(cursor.content_width, cursor.x.add(child.width));
    }

    //  Step 2: cursor_i1.cw <= cursor(n).cw = content_width
    lemma_wrap_cursor_cw_monotone(child_sizes, h_spacing, v_spacing, avail_w, (i + 1) as nat, n);
    T::axiom_le_transitive(cx.add(child.width), cursor_i1.content_width,
        wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, n).content_width);

    //  Step 3: left + cx + child_w <= left + content_width
    T::axiom_le_add_monotone(cx.add(child.width), content_width, padding.left);
    T::axiom_add_commutative(cx.add(child.width), padding.left);
    T::axiom_add_commutative(content_width, padding.left);
    T::axiom_le_congruence(
        cx.add(child.width).add(padding.left), padding.left.add(cx.add(child.width)),
        content_width.add(padding.left), padding.left.add(content_width),
    );
    T::axiom_add_associative(padding.left, cx, child.width);
    T::axiom_eqv_symmetric(
        padding.left.add(cx).add(child.width),
        padding.left.add(cx.add(child.width)),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        padding.left.add(cx.add(child.width)),
        padding.left.add(cx).add(child.width),
        padding.left.add(content_width),
    );

    //  Step 4: left + content_width <= h + content_width
    crate::layout::proofs::lemma_le_add_nonneg(padding.left, padding.right);
    T::axiom_le_add_monotone(padding.left, h, content_width);
    T::axiom_add_commutative(padding.left, content_width);
    T::axiom_add_commutative(h, content_width);
    T::axiom_le_congruence(
        padding.left.add(content_width), content_width.add(padding.left),
        h.add(content_width), content_width.add(h),
    );

    //  Chain: left + cx + child_w <= left + cw <= h + cw <= parent_w
    T::axiom_le_transitive(
        padding.left.add(cx).add(child.width),
        padding.left.add(content_width),
        h.add(content_width),
    );
    T::axiom_le_transitive(
        padding.left.add(cx).add(child.width),
        h.add(content_width),
        parent_w,
    );
}

///  Helper: per-child Y upper bound for wrap layout.
proof fn lemma_wrap_child_y_upper_bound<T: OrderedField>(
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    child_sizes: Seq<Size<T>>,
    avail_w: T,
    content_height: T,
    parent_h: T,
    i: int,
)
    requires
        padding.is_nonneg(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        0 <= i < child_sizes.len(),
        child_sizes.len() > 0,
        forall|k: int| 0 <= k < child_sizes.len() ==>
            T::zero().le(child_sizes[k].width) && T::zero().le(child_sizes[k].height),
        content_height == wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w,
            child_sizes.len() as nat).y.add(
            wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w,
                child_sizes.len() as nat).line_height),
        padding.vertical().add(content_height).le(parent_h),
    ensures ({
        let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, i as nat);
        let child = child_sizes[i];
        let needs_break = wrap_needs_break(cursor.x, child.width, avail_w);
        let cy = if needs_break {
            cursor.y.add(cursor.line_height).add(v_spacing)
        } else { cursor.y };
        padding.top.add(cy).add(child.height).le(parent_h)
    }),
{
    let n = child_sizes.len() as nat;
    let v = padding.vertical();
    let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, i as nat);
    let child = child_sizes[i];
    let needs_break = wrap_needs_break(cursor.x, child.width, avail_w);
    let cy = if needs_break {
        cursor.y.add(cursor.line_height).add(v_spacing)
    } else { cursor.y };
    let cursor_i1 = wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, (i + 1) as nat);

    //  Step 1: cy + child.height <= cursor_i1.y + cursor_i1.line_height
    if needs_break {
        T::axiom_le_reflexive(cursor_i1.y.add(cursor_i1.line_height));
    } else {
        lemma_max_ge_right::<T>(cursor.line_height, child.height);
        T::axiom_le_add_monotone(child.height, cursor_i1.line_height, cursor_i1.y);
        T::axiom_add_commutative(child.height, cursor_i1.y);
        T::axiom_add_commutative(cursor_i1.line_height, cursor_i1.y);
        T::axiom_le_congruence(
            child.height.add(cursor_i1.y), cursor_i1.y.add(child.height),
            cursor_i1.line_height.add(cursor_i1.y), cursor_i1.y.add(cursor_i1.line_height),
        );
    }

    //  Step 2: cursor_i1.y + lh <= cursor(n).y + lh = content_height
    lemma_wrap_cursor_ylh_monotone(child_sizes, h_spacing, v_spacing, avail_w, (i + 1) as nat, n);
    T::axiom_le_transitive(
        cy.add(child.height),
        cursor_i1.y.add(cursor_i1.line_height),
        wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, n).y.add(
            wrap_cursor(child_sizes, h_spacing, v_spacing, avail_w, n).line_height),
    );

    //  Step 3: top + cy + child_h <= top + content_height
    T::axiom_le_add_monotone(cy.add(child.height), content_height, padding.top);
    T::axiom_add_commutative(cy.add(child.height), padding.top);
    T::axiom_add_commutative(content_height, padding.top);
    T::axiom_le_congruence(
        cy.add(child.height).add(padding.top), padding.top.add(cy.add(child.height)),
        content_height.add(padding.top), padding.top.add(content_height),
    );
    T::axiom_add_associative(padding.top, cy, child.height);
    T::axiom_eqv_symmetric(
        padding.top.add(cy).add(child.height),
        padding.top.add(cy.add(child.height)),
    );
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        padding.top.add(cy.add(child.height)),
        padding.top.add(cy).add(child.height),
        padding.top.add(content_height),
    );

    //  Step 4: top + content_height <= v + content_height
    crate::layout::proofs::lemma_le_add_nonneg(padding.top, padding.bottom);
    T::axiom_le_add_monotone(padding.top, v, content_height);
    T::axiom_add_commutative(padding.top, content_height);
    T::axiom_add_commutative(v, content_height);
    T::axiom_le_congruence(
        padding.top.add(content_height), content_height.add(padding.top),
        v.add(content_height), content_height.add(v),
    );

    //  Chain
    T::axiom_le_transitive(
        padding.top.add(cy).add(child.height),
        padding.top.add(content_height),
        v.add(content_height),
    );
    T::axiom_le_transitive(
        padding.top.add(cy).add(child.height),
        v.add(content_height),
        parent_h,
    );
}

///  Wrap layout has children_within_bounds.
///
///  Preconditions: padding fits, nonneg spacings, each child width <= available_width,
///  and content size + padding <= max (so children don't overflow).
pub proof fn lemma_wrap_children_within_bounds<T: OrderedField>(
    limits: crate::limits::Limits<T>,
    padding: Padding<T>,
    h_spacing: T,
    v_spacing: T,
    children: Seq<crate::widget::Widget<T>>,
    fuel: nat,
)
    requires
        limits.wf(),
        fuel > 1,
        padding.is_nonneg(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        padding.horizontal().add(limits.min.width).le(limits.max.width),
        padding.vertical().add(limits.min.height).le(limits.max.height),
        children.len() > 0,
        //  Content fits within limits
        ({
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = crate::widget::widget_child_nodes(inner, children, (fuel - 1) as nat);
            let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
            let avail_w = limits.max.width.sub(padding.horizontal());
            let content = wrap_content_size(child_sizes, h_spacing, v_spacing, avail_w);
            //  Each child fits on a line
            (forall|i: int| 0 <= i < child_sizes.len() ==>
                child_sizes[i].width.le(avail_w))
            //  Content + padding fits
            && padding.horizontal().add(content.width).le(limits.max.width)
            && padding.vertical().add(content.height).le(limits.max.height)
        }),
    ensures
        crate::widget::layout_widget(limits, crate::widget::Widget::Container(crate::widget::ContainerWidget::Wrap {
            padding, h_spacing, v_spacing, children,
        }), fuel).children_within_bounds(),
{
    let h = padding.horizontal();
    let v = padding.vertical();
    let inner = limits.shrink(h, v);
    let cn = crate::widget::widget_child_nodes(inner, children, (fuel - 1) as nat);
    let child_sizes = Seq::new(cn.len(), |i: int| cn[i].size);
    let avail_w = limits.max.width.sub(h);
    let content = wrap_content_size(child_sizes, h_spacing, v_spacing, avail_w);
    let n = child_sizes.len() as nat;
    let total_w = h.add(content.width);
    let total_h = v.add(content.height);

    //  h, v >= 0
    crate::layout::proofs::lemma_nonneg_sum(padding.left, padding.right);
    crate::layout::proofs::lemma_nonneg_sum(padding.top, padding.bottom);

    //  inner.wf
    crate::layout::proofs::lemma_shrink_wf(limits, h, v);
    crate::layout::proofs::lemma_add_comm_le(h, limits.min.width, limits.max.width);
    crate::layout::proofs::lemma_add_comm_le(v, limits.min.height, limits.max.height);

    //  child sizes nonneg (from layout_respects_limits)
    assert forall|k: int| 0 <= k < child_sizes.len() implies
        T::zero().le(child_sizes[k].width)
        && T::zero().le(child_sizes[k].height)
    by {
        crate::layout::proofs::lemma_layout_respects_limits(
            inner, children[k], (fuel - 1) as nat,
        );
        T::axiom_le_transitive(T::zero(), inner.min.width, cn[k].size.width);
        T::axiom_le_transitive(T::zero(), inner.min.height, cn[k].size.height);
    };

    //  resolve(total_w, total_h) >= (total_w, total_h) since total <= max
    crate::layout::proofs::lemma_resolve_ge_input(
        limits, crate::size::Size::new(total_w, total_h),
    );
    let parent_size = limits.resolve(crate::size::Size::new(total_w, total_h));

    //  Layout structure
    lemma_wrap_children_len(
        padding, h_spacing, v_spacing, child_sizes, avail_w, 0,
    );
    reveal(wrap_layout);
    let layout = wrap_layout(limits, padding, h_spacing, v_spacing, child_sizes);

    //  Per-child bounds
    assert forall|i: int| 0 <= i < cn.len() implies
        T::zero().le(layout.children[i].x)
        && T::zero().le(layout.children[i].y)
        && layout.children[i].x.add(cn[i].size.width).le(layout.size.width)
        && layout.children[i].y.add(cn[i].size.height).le(layout.size.height)
    by {
        lemma_wrap_children_element(
            padding, h_spacing, v_spacing, child_sizes, avail_w, i as nat,
        );
        //  Connect child_sizes[i] to cn[i].size
        assert(child_sizes[i] === cn[i].size);
        //  Connect layout.size to parent_size
        assert(layout.size === parent_size);

        lemma_wrap_child_position_nonneg(
            padding, h_spacing, v_spacing, child_sizes, avail_w, i as nat,
        );
        //  0 <= padding.left <= layout.children[i].x
        T::axiom_le_transitive(T::zero(), padding.left, layout.children[i].x);
        //  0 <= padding.top <= layout.children[i].y
        T::axiom_le_transitive(T::zero(), padding.top, layout.children[i].y);

        lemma_wrap_child_x_upper_bound(
            padding, h_spacing, v_spacing, child_sizes, avail_w,
            content.width, parent_size.width, i,
        );
        lemma_wrap_child_y_upper_bound(
            padding, h_spacing, v_spacing, child_sizes, avail_w,
            content.height, parent_size.height, i,
        );
    };

    crate::layout::proofs::lemma_merge_layout_cwb(layout, cn);
}

//  ── Uniform height lemmas ─────────────────────────────────────────

///  With uniform-height children, every line has the same line_height.
pub proof fn lemma_uniform_line_height<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    count: nat,
    h: T,
)
    requires
        count > 0,
        count <= child_sizes.len(),
        wrap_uniform_height(child_sizes),
        h.eqv(child_sizes[0].height),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
    ensures
        wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, count)
            .line_height.eqv(h),
    decreases count,
{
    let cursor = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, count);
    let child = child_sizes[(count - 1) as int];
    if count == 1 {
        //  prev = wrap_cursor(0) = {x:zero, y:zero, lh:zero, cw:zero}
        //  wrap_needs_break(zero, child[0].w, aw) = !zero.le(zero) && ... = false
        T::axiom_le_reflexive(T::zero());
        let prev = wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, 0 as nat);
        assert(!wrap_needs_break(prev.x, child.width, available_width));
        //  Same line: lh = max(zero, child_sizes[0].height)
        //  zero.le(child_sizes[0].height) from requires → max = child_sizes[0].height
        assert(max::<T>(T::zero(), child_sizes[0].height) == child_sizes[0].height);
        //  h ≡ child_sizes[0].height → child_sizes[0].height ≡ h
        T::axiom_eqv_symmetric(h, child_sizes[0].height);
    } else {
        //  IH: cursor(count-1).line_height ≡ h
        lemma_uniform_line_height(
            child_sizes, h_spacing, v_spacing, available_width,
            (count - 1) as nat, h,
        );
        let prev = wrap_cursor(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        if wrap_needs_break(prev.x, child.width, available_width) {
            //  New line: line_height = child.height ≡ h
            T::axiom_eqv_symmetric(h, child_sizes[0].height);
            //  h.eqv(child_sizes[0].height) reversed
            //  child_sizes[0].height.eqv(child.height) from uniform
            T::axiom_eqv_transitive(
                child.height,
                child_sizes[0].height,
                h,
            );
            T::axiom_eqv_symmetric(child.height, h);
        } else {
            //  Same line: line_height = max(prev.lh, child.height)
            //  prev.lh ≡ h, child.height ≡ h
            //  max(h, h) ≡ h
            //  First show child.height ≡ h
            T::axiom_eqv_symmetric(h, child_sizes[0].height);
            T::axiom_eqv_transitive(child.height, child_sizes[0].height, h);
            T::axiom_eqv_symmetric(child.height, h);
            //  child.height ≡ h (reversed: h ≡ child.height)

            //  max(prev.lh, child.height) ≡ max(h, h) via congruence
            //  First: max(prev.lh, child.height) ≡ max(h, child.height)
            crate::layout::proofs::lemma_max_congruence_left(prev.line_height, h, child.height);
            T::axiom_eqv_symmetric(
                max::<T>(prev.line_height, child.height),
                max::<T>(h, child.height),
            );
            //  Then: max(h, child.height) ≡ max(h, h) (child.height ≡ h)
            T::axiom_eqv_symmetric(child.height, h);
            crate::layout::proofs::lemma_max_congruence_left(child.height, h, h);
            //  max(child.height, h) ≡ max(h, h)
            use verus_algebra::min_max::lemma_max_commutative;
            lemma_max_commutative::<T>(h, child.height);
            lemma_max_commutative::<T>(child.height, h);
            //  max(h, child.height) ≡ max(child.height, h)
            T::axiom_eqv_transitive(
                max::<T>(h, child.height),
                max::<T>(child.height, h),
                max::<T>(h, h),
            );

            use verus_algebra::min_max::lemma_max_self;
            lemma_max_self::<T>(h);
            //  max(h, h) ≡ h

            //  Chain: cursor.lh = max(prev.lh, child.h) ≡ max(h, child.h) ≡ max(h,h) ≡ h
            T::axiom_eqv_transitive(
                max::<T>(prev.line_height, child.height),
                max::<T>(h, child.height),
                max::<T>(h, h),
            );
            T::axiom_eqv_transitive(
                max::<T>(prev.line_height, child.height),
                max::<T>(h, h),
                h,
            );
        }
    }
}

///  Wider available width means at least as few line breaks.
///
///  Key insight: when a child triggers a break under aw1, it may NOT trigger
///  under aw2 (wider). But the reverse can't happen when all child widths ≤ aw1.
pub proof fn lemma_wider_fewer_breaks<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    aw1: T,
    aw2: T,
    count: nat,
)
    requires
        count <= child_sizes.len(),
        aw1.le(aw2),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        //  Each child must fit on a line in the narrower width
        forall|i: int| 0 <= i < child_sizes.len() ==>
            child_sizes[i].width.le(aw1),
    ensures
        wrap_break_count(child_sizes, h_spacing, v_spacing, aw2, count)
            <= wrap_break_count(child_sizes, h_spacing, v_spacing, aw1, count),
        //  Auxiliary: when break counts match, wider width has ≤ x
        //  (narrower width broke earlier, accumulated more x since last break)
        (wrap_break_count(child_sizes, h_spacing, v_spacing, aw2, count)
            == wrap_break_count(child_sizes, h_spacing, v_spacing, aw1, count)
        ==>
            wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, count).x.le(
                wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, count).x)
        ),
        //  Both cursors have nonneg x
        T::zero().le(wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, count).x),
        T::zero().le(wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, count).x),
    decreases count,
{
    if count == 0 {
        T::axiom_le_reflexive(T::zero());
    } else {
        //  IH
        lemma_wider_fewer_breaks(
            child_sizes, h_spacing, v_spacing, aw1, aw2, (count - 1) as nat,
        );
        let c1 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, (count - 1) as nat);
        let c2 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, (count - 1) as nat);
        let child = child_sizes[(count - 1) as int];
        let b1 = wrap_needs_break(c1.x, child.width, aw1);
        let b2 = wrap_needs_break(c2.x, child.width, aw2);
        let bc1 = wrap_break_count(child_sizes, h_spacing, v_spacing, aw1, (count - 1) as nat);
        let bc2 = wrap_break_count(child_sizes, h_spacing, v_spacing, aw2, (count - 1) as nat);

        if b1 && b2 {
            //  Both break: x resets to child.w + h_sp for both → equal
            T::axiom_le_reflexive(child.width.add(h_spacing));
            //  x_new nonneg
            lemma_nonneg_add::<T>(child.width, h_spacing);
        } else if !b1 && !b2 {
            //  Neither breaks: break_counts unchanged
            //  x_new = prev.x + child.w + h_sp
            if bc1 == bc2 {
                //  IH gives c2.x ≤ c1.x → new x2 ≤ new x1
                T::axiom_le_add_monotone(c2.x, c1.x, child.width);
                T::axiom_le_add_monotone(
                    c2.x.add(child.width), c1.x.add(child.width), h_spacing,
                );
            }
            //  x_new nonneg for aw1
            lemma_nonneg_add::<T>(c1.x, child.width);
            lemma_nonneg_add::<T>(c1.x.add(child.width), h_spacing);
            //  x_new nonneg for aw2
            lemma_nonneg_add::<T>(c2.x, child.width);
            lemma_nonneg_add::<T>(c2.x.add(child.width), h_spacing);
        } else if b1 && !b2 {
            //  Only aw1 breaks: bc1 → bc1+1, bc2 stays
            //  bc2 ≤ bc1 → bc2 < bc1+1 → bc2 ≤ bc1+1 ✓
            //  bc2 ≤ bc1 also means bc2 < bc1+1, so bc2 != bc1+1 unless bc2==bc1,
            //  but bc2==bc1+1 requires bc2>bc1, contradicting IH. So x aux N/A.
            //  x_new nonneg
            lemma_nonneg_add::<T>(child.width, h_spacing);
            lemma_nonneg_add::<T>(c2.x, child.width);
            lemma_nonneg_add::<T>(c2.x.add(child.width), h_spacing);
        } else {
            //  !b1 && b2: aw1 doesn't break, aw2 does.
            //  Need: bc2+1 ≤ bc1, i.e., bc2 < bc1 (strict).
            //  Prove bc1 == bc2 is impossible:
            if bc1 == bc2 {
                //  IH gives c2.x ≤ c1.x.
                //  b2: ¬c2.x.le(zero) ∧ ¬(c2.x + w).le(aw2)
                //  !b1: c1.x.le(zero) ∨ (c1.x + w).le(aw1)
                if c1.x.le(T::zero()) {
                    //  c2.x ≤ c1.x ≤ 0 contradicts ¬c2.x.le(0)
                    T::axiom_le_transitive(c2.x, c1.x, T::zero());
                    assert(false);
                } else {
                    //  c1.x > 0, so !b1 requires (c1.x + w).le(aw1)
                    assert(c1.x.add(child.width).le(aw1));
                    //  c2.x + w ≤ c1.x + w (from c2.x ≤ c1.x)
                    T::axiom_le_add_monotone(c2.x, c1.x, child.width);
                    //  c2.x + w ≤ c1.x + w ≤ aw1 ≤ aw2
                    T::axiom_le_transitive(
                        c2.x.add(child.width), c1.x.add(child.width), aw1,
                    );
                    T::axiom_le_transitive(c2.x.add(child.width), aw1, aw2);
                    //  contradicts ¬(c2.x + w).le(aw2)
                    assert(false);
                }
            }
            //  bc2 < bc1 (strict), so bc2 + 1 ≤ bc1 = new_bc1. ✓

            //  x auxiliary: if new bc2+1 == new bc1 (i.e., bc2+1 == bc1):
            //  c2 broke → x2_new = child.w + h_sp
            //  c1 didn't → x1_new = c1.x + child.w + h_sp
            //  Need: x2_new ≤ x1_new, i.e., child.w+h_sp ≤ c1.x+child.w+h_sp
            if bc2 + 1 == bc1 {
                //  0 ≤ c1.x from IH
                T::axiom_le_add_monotone(T::zero(), c1.x, child.width);
                T::axiom_le_add_monotone(
                    T::zero().add(child.width), c1.x.add(child.width), h_spacing,
                );
                //  zero.add(cw).add(hs) ≤ c1.x.add(cw).add(hs)
                //  Bridge: zero.add(cw) ≡ cw
                use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
                lemma_add_zero_left::<T>(child.width);
                T::axiom_add_congruence_left(
                    T::zero().add(child.width), child.width, h_spacing,
                );
                //  zero.add(cw).add(hs) ≡ cw.add(hs)
                T::axiom_eqv_symmetric(
                    T::zero().add(child.width).add(h_spacing),
                    child.width.add(h_spacing),
                );
                T::axiom_eqv_reflexive(c1.x.add(child.width).add(h_spacing));
                T::axiom_le_congruence(
                    T::zero().add(child.width).add(h_spacing),
                    child.width.add(h_spacing),
                    c1.x.add(child.width).add(h_spacing),
                    c1.x.add(child.width).add(h_spacing),
                );
            }
            //  x_new nonneg
            lemma_nonneg_add::<T>(c1.x, child.width);
            lemma_nonneg_add::<T>(c1.x.add(child.width), h_spacing);
            lemma_nonneg_add::<T>(child.width, h_spacing);
        }
    }
}

///  When all children fit on one line, content height equals the max child height.
pub proof fn lemma_wrap_single_line_height<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
)
    requires
        child_sizes.len() > 0,
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        //  All children fit on one line: no breaks
        wrap_break_count(child_sizes, h_spacing, v_spacing, available_width,
            child_sizes.len() as nat) == 0,
    ensures
        //  Content height = cursor.y + cursor.line_height.
        //  With no breaks, cursor.y = 0, so content_height = line_height.
        wrap_content_size(child_sizes, h_spacing, v_spacing, available_width)
            .height.eqv(
                wrap_cursor(child_sizes, h_spacing, v_spacing, available_width,
                    child_sizes.len() as nat).line_height
            ),
{
    //  With no breaks, cursor.y stays 0 throughout
    lemma_no_breaks_y_zero(
        child_sizes, h_spacing, v_spacing, available_width, child_sizes.len() as nat,
    );
    //  cursor.y ≡ 0, so content_height = y + line_height ≡ 0 + line_height ≡ line_height
    let cursor = wrap_cursor(
        child_sizes, h_spacing, v_spacing, available_width, child_sizes.len() as nat,
    );
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    lemma_add_zero_left::<T>(cursor.line_height);
    T::axiom_eqv_symmetric(cursor.y, T::zero());
    T::axiom_add_congruence_left(cursor.y, T::zero(), cursor.line_height);
    T::axiom_eqv_transitive(
        cursor.y.add(cursor.line_height),
        T::zero().add(cursor.line_height),
        cursor.line_height,
    );
}

///  Helper: if break_count is 0, cursor.y is zero.
proof fn lemma_no_breaks_y_zero<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    available_width: T,
    count: nat,
)
    requires
        count <= child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        wrap_break_count(child_sizes, h_spacing, v_spacing, available_width, count) == 0,
    ensures
        wrap_cursor(child_sizes, h_spacing, v_spacing, available_width, count)
            .y.eqv(T::zero()),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        //  bc(count) = bc(count-1) + (1 if break else 0) = 0
        //  So bc(count-1) = 0 and no break at count-1
        let prev_bc = wrap_break_count(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        let cursor_prev = wrap_cursor(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        let child = child_sizes[(count - 1) as int];
        let needs_break = wrap_needs_break(cursor_prev.x, child.width, available_width);
        //  If break: bc(count) = prev_bc + 1 > 0 = impossible (bc(count) == 0)
        //  So !needs_break
        assert(!needs_break);
        //  IH: cursor(count-1).y ≡ 0
        lemma_no_breaks_y_zero(
            child_sizes, h_spacing, v_spacing, available_width, (count - 1) as nat,
        );
        //  No break: cursor(count).y = cursor(count-1).y ≡ 0 ✓
    }
}

///  Wrap content height is monotone when all children fit on a single line.
///
///  When all children fit on one line for BOTH widths, content height is the
///  same (max child height), hence trivially monotone.
pub proof fn lemma_wrap_content_height_single_line_monotone<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    aw1: T,
    aw2: T,
)
    requires
        child_sizes.len() > 0,
        aw1.le(aw2),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        //  Both widths fit all children on one line
        wrap_break_count(child_sizes, h_spacing, v_spacing, aw1,
            child_sizes.len() as nat) == 0,
        wrap_break_count(child_sizes, h_spacing, v_spacing, aw2,
            child_sizes.len() as nat) == 0,
    ensures
        wrap_content_size(child_sizes, h_spacing, v_spacing, aw2).height.le(
            wrap_content_size(child_sizes, h_spacing, v_spacing, aw1).height,
        ),
{
    //  Both single-line → content_height = cursor.line_height in both cases
    lemma_wrap_single_line_height(child_sizes, h_spacing, v_spacing, aw1);
    lemma_wrap_single_line_height(child_sizes, h_spacing, v_spacing, aw2);

    //  Both line_heights equal the max child height built incrementally
    //  Since no breaks in either, both cursors process the same sequence of
    //  max(prev.lh, child.height), just with different x values.
    //  The line_height values are IDENTICAL because they don't depend on x.
    lemma_no_breaks_same_line_height(
        child_sizes, h_spacing, v_spacing, aw1, aw2, child_sizes.len() as nat,
    );
    //  cursor(aw1).lh ≡ cursor(aw2).lh

    let ch1 = wrap_content_size(child_sizes, h_spacing, v_spacing, aw1).height;
    let ch2 = wrap_content_size(child_sizes, h_spacing, v_spacing, aw2).height;
    let lh1 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, child_sizes.len() as nat).line_height;
    let lh2 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, child_sizes.len() as nat).line_height;

    //  ch1 ≡ lh1 ≡ lh2 ≡ ch2 → ch1 ≡ ch2 → ch2 ≤ ch1
    T::axiom_eqv_symmetric(ch2, lh2);
    T::axiom_eqv_transitive(ch1, lh1, lh2);
    T::axiom_eqv_transitive(ch1, lh2, ch2);
    //  ch1 ≡ ch2
    T::axiom_eqv_symmetric(ch1, ch2);
    T::axiom_eqv_reflexive(ch1);
    T::axiom_le_reflexive(ch1);
    T::axiom_le_congruence(ch1, ch2, ch1, ch1);
}

///  Helper: when both widths have no breaks, line_height is identical.
proof fn lemma_no_breaks_same_line_height<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    h_spacing: T,
    v_spacing: T,
    aw1: T,
    aw2: T,
    count: nat,
)
    requires
        count <= child_sizes.len(),
        T::zero().le(h_spacing),
        T::zero().le(v_spacing),
        forall|i: int| 0 <= i < child_sizes.len() ==> {
            &&& T::zero().le(child_sizes[i].width)
            &&& T::zero().le(child_sizes[i].height)
        },
        wrap_break_count(child_sizes, h_spacing, v_spacing, aw1, count) == 0,
        wrap_break_count(child_sizes, h_spacing, v_spacing, aw2, count) == 0,
    ensures
        wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, count).line_height.eqv(
            wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, count).line_height,
        ),
    decreases count,
{
    if count == 0 {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        let prev1 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw1, (count - 1) as nat);
        let prev2 = wrap_cursor(child_sizes, h_spacing, v_spacing, aw2, (count - 1) as nat);
        let child = child_sizes[(count - 1) as int];

        //  No breaks at any step
        let bc1_prev = wrap_break_count(child_sizes, h_spacing, v_spacing, aw1, (count - 1) as nat);
        let bc2_prev = wrap_break_count(child_sizes, h_spacing, v_spacing, aw2, (count - 1) as nat);
        assert(!wrap_needs_break(prev1.x, child.width, aw1));
        assert(!wrap_needs_break(prev2.x, child.width, aw2));

        //  IH
        lemma_no_breaks_same_line_height(
            child_sizes, h_spacing, v_spacing, aw1, aw2, (count - 1) as nat,
        );
        //  prev1.line_height ≡ prev2.line_height

        //  No break: new_lh = max(prev.lh, child.height) for both
        //  max(prev1.lh, child.h) ≡ max(prev2.lh, child.h) via congruence on first arg
        crate::layout::proofs::lemma_max_congruence_left(
            prev1.line_height, prev2.line_height, child.height,
        );
    }
}

} //  verus!
