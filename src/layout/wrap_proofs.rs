use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::inequalities::lemma_nonneg_add;
use verus_algebra::min_max::{max, lemma_max_ge_left};
use crate::size::Size;
use crate::node::Node;
use crate::padding::Padding;
use crate::layout::wrap::*;

verus! {

/// Length of wrap_children sequence.
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

/// Element access: wrap_children[k] is a leaf at the correct position.
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

// ── Algebraic helper ──────────────────────────────────────────────

/// a <= a + b when b >= 0.
proof fn lemma_le_add_nonneg<T: OrderedRing>(a: T, b: T)
    requires
        T::zero().le(b),
    ensures
        a.le(a.add(b)),
{
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    T::axiom_le_add_monotone(T::zero(), b, a);
    // T::zero().add(a).le(b.add(a))
    lemma_add_zero_left::<T>(a);
    T::axiom_add_commutative(b, a);
    T::axiom_le_congruence(
        T::zero().add(a), a,
        b.add(a), a.add(b),
    );
}

// ── Cursor nonneg ─────────────────────────────────────────────────

/// All cursor fields are nonneg when child sizes and spacings are nonneg.
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
            // x = child.width + h_spacing
            lemma_nonneg_add::<T>(child.width, h_spacing);
            // y = prev.y + prev.line_height + v_spacing
            lemma_nonneg_add::<T>(prev.y, prev.line_height);
            lemma_nonneg_add::<T>(prev.y.add(prev.line_height), v_spacing);
            // line_height = child.height (nonneg by assumption)
            // content_width = max(prev.content_width, child.width) >= prev.content_width >= 0
            lemma_max_ge_left::<T>(prev.content_width, child.width);
            T::axiom_le_transitive(
                T::zero(), prev.content_width, max::<T>(prev.content_width, child.width),
            );
        } else {
            // x = prev.x + child.width + h_spacing
            lemma_nonneg_add::<T>(prev.x, child.width);
            lemma_nonneg_add::<T>(prev.x.add(child.width), h_spacing);
            // y = prev.y (nonneg by IH)
            // line_height = max(prev.line_height, child.height) >= prev.line_height >= 0
            lemma_max_ge_left::<T>(prev.line_height, child.height);
            T::axiom_le_transitive(
                T::zero(), prev.line_height, max::<T>(prev.line_height, child.height),
            );
            // content_width = max(prev.content_width, prev.x + child.width)
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

// ── Child position bounds ─────────────────────────────────────────

/// Each child in a wrap layout is positioned at x >= padding.left and y >= padding.top.
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
    // cx >= 0 (either zero or cursor.x which is nonneg)
    if needs_break {
        T::axiom_le_reflexive(T::zero());
    }
    // cy >= 0 (either cursor.y or cursor.y + cursor.line_height + v_spacing, both nonneg)
    if needs_break {
        lemma_nonneg_add::<T>(cursor.y, cursor.line_height);
        lemma_nonneg_add::<T>(cursor.y.add(cursor.line_height), v_spacing);
    }
    // padding.left + cx >= padding.left (since cx >= 0)
    assert(T::zero().le(cx));
    T::axiom_le_add_monotone(T::zero(), cx, padding.left);
    // 0 + padding.left <= cx + padding.left
    // Need: padding.left <= padding.left + cx
    // axiom_le_add_monotone gives: 0.add(padding.left).le(cx.add(padding.left))
    // i.e. padding.left.le(cx.add(padding.left)) via zero+padding.left eqv padding.left
    // But we need padding.left.le(padding.left.add(cx))
    // Use commutativity: padding.left.add(cx) == cx.add(padding.left) via axiom_add_commutative
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    lemma_add_zero_left::<T>(padding.left);
    // T::zero().add(padding.left).eqv(padding.left)
    T::axiom_add_commutative(cx, padding.left);
    // cx.add(padding.left).eqv(padding.left.add(cx))
    T::axiom_le_congruence(
        T::zero().add(padding.left),
        padding.left,
        cx.add(padding.left),
        padding.left.add(cx),
    );

    // Similarly for y: padding.top + cy >= padding.top
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

    // Connect to actual children via element lemma
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

// ── Same-line horizontal non-overlapping ──────────────────────────

/// Consecutive children on the same line don't overlap horizontally.
///
/// When child k+1 does not trigger a line break, the right edge of child k
/// is at or before the left edge of child k+1.
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
        // No break at k+1 (child k+1 stays on the same line)
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
    // Get element positions
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
    // No break at k+1 (given), so cx_{k+1} = cursor_{k+1}.x
    let cx_k1 = cursor_k1.x;

    // Key: cursor_{k+1}.x = cx_k + child_k.width + h_spacing (from wrap_cursor definition)
    // Whether or not there was a break at k:
    //   break at k → cursor_{k+1}.x = child_k.width + h_spacing = zero + child_k.width + h_spacing
    //   no break at k → cursor_{k+1}.x = cursor_k.x + child_k.width + h_spacing = cx_k + child_k.width + h_spacing
    // In both cases: cursor_{k+1}.x = cx_k.add(child_k.width).add(h_spacing)

    // Need: padding.left + cx_k + child_k.width <= padding.left + cx_k1
    // i.e.  cx_k + child_k.width <= cx_k1
    // i.e.  cx_k + child_k.width <= cx_k + child_k.width + h_spacing (via cursor relation)
    // i.e.  a <= a + h_spacing where a = cx_k + child_k.width

    // First establish cursor nonneg for cx_k >= 0
    lemma_wrap_cursor_nonneg(
        child_sizes, h_spacing, v_spacing, available_width, k,
    );

    // cx_k.add(child_k.width) <= cx_k.add(child_k.width).add(h_spacing)
    if needs_break_k {
        // cx_k = zero, cursor_{k+1}.x = child_k.width.add(h_spacing)
        // Need: zero.add(child_k.width).le(child_k.width.add(h_spacing))
        use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
        lemma_add_zero_left::<T>(child_k.width);
        // zero.add(child_k.width).eqv(child_k.width)
        lemma_le_add_nonneg(child_k.width, h_spacing);
        // child_k.width.le(child_k.width.add(h_spacing))
        T::axiom_eqv_symmetric(T::zero().add(child_k.width), child_k.width);
        // child_k.width.eqv(zero.add(child_k.width))
        T::axiom_eqv_reflexive(child_k.width.add(h_spacing));
        T::axiom_le_congruence(
            child_k.width, T::zero().add(child_k.width),
            child_k.width.add(h_spacing), child_k.width.add(h_spacing),
        );
        // zero.add(child_k.width).le(child_k.width.add(h_spacing))
    } else {
        // cx_k = cursor_k.x, cursor_{k+1}.x = cursor_k.x.add(child_k.width).add(h_spacing)
        // Need: cursor_k.x.add(child_k.width).le(cursor_k.x.add(child_k.width).add(h_spacing))
        lemma_le_add_nonneg(cursor_k.x.add(child_k.width), h_spacing);
    }

    // Now we have: cx_k.add(child_k.width).le(cx_k1)
    // Need: padding.left.add(cx_k).add(child_k.width).le(padding.left.add(cx_k1))
    // Use add_monotone: cx_k.add(child_k.width).le(cx_k1) implies
    //   cx_k.add(child_k.width).add(padding.left).le(cx_k1.add(padding.left))
    T::axiom_le_add_monotone(
        cx_k.add(child_k.width), cx_k1, padding.left,
    );
    // cx_k.add(child_k.width).add(padding.left).le(cx_k1.add(padding.left))

    // Need to show LHS = padding.left.add(cx_k).add(child_k.width) and RHS = padding.left.add(cx_k1)
    // via associativity + commutativity
    T::axiom_add_associative(padding.left, cx_k, child_k.width);
    // padding.left.add(cx_k).add(child_k.width).eqv(padding.left.add(cx_k.add(child_k.width)))
    // a1 = cx_k.add(child_k.width).add(padding.left), we proved a1.le(cx_k1.add(padding.left))
    // a2 = padding.left.add(cx_k).add(child_k.width) [desired LHS]
    // b2 = padding.left.add(cx_k1) [desired RHS]
    // Need: a1.eqv(a2) via commutativity+associativity, b1.eqv(b2) via commutativity

    // a1 → a2: cx_k.add(child_k.width).add(padding.left) → padding.left.add(cx_k).add(child_k.width)
    T::axiom_add_commutative(cx_k.add(child_k.width), padding.left);
    // cx_k.add(child_k.width).add(padding.left).eqv(padding.left.add(cx_k.add(child_k.width)))
    T::axiom_add_associative(padding.left, cx_k, child_k.width);
    // padding.left.add(cx_k).add(child_k.width).eqv(padding.left.add(cx_k.add(child_k.width)))
    T::axiom_eqv_symmetric(
        padding.left.add(cx_k).add(child_k.width),
        padding.left.add(cx_k.add(child_k.width)),
    );
    // padding.left.add(cx_k.add(child_k.width)).eqv(padding.left.add(cx_k).add(child_k.width))
    T::axiom_eqv_transitive(
        cx_k.add(child_k.width).add(padding.left),
        padding.left.add(cx_k.add(child_k.width)),
        padding.left.add(cx_k).add(child_k.width),
    );
    // cx_k.add(child_k.width).add(padding.left).eqv(padding.left.add(cx_k).add(child_k.width))

    // b1 → b2: cx_k1.add(padding.left) → padding.left.add(cx_k1)
    T::axiom_add_commutative(cx_k1, padding.left);
    // cx_k1.add(padding.left).eqv(padding.left.add(cx_k1))

    T::axiom_le_congruence(
        cx_k.add(child_k.width).add(padding.left),
        padding.left.add(cx_k).add(child_k.width),
        cx_k1.add(padding.left),
        padding.left.add(cx_k1),
    );
    // padding.left.add(cx_k).add(child_k.width).le(padding.left.add(cx_k1))

    // Connect to children array
    let children = wrap_children(
        padding, h_spacing, v_spacing, child_sizes, available_width, 0,
    );
    assert(children[k as int].x == padding.left.add(cx_k));
    assert(children[(k + 1) as int].x == padding.left.add(cx_k1));
}

} // verus!
