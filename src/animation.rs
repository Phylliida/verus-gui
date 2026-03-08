use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::convex::*;
use crate::size::Size;
use crate::node::Node;
use crate::diff::nodes_deeply_eqv;

verus! {

// ── Scalar interpolation ──────────────────────────────────────────

/// Linear interpolation: (1-t)*a + t*b.
///
/// Relates to `convex(x, y, t) = t*x + (1-t)*y` by:
///   `scalar_lerp(a, b, t) = convex(b, a, t)`
/// (swap arguments, since convex puts weight t on the first argument).
pub open spec fn scalar_lerp<T: OrderedField>(a: T, b: T, t: T) -> T {
    convex::<T>(b, a, t)
}

// ── Size interpolation ────────────────────────────────────────────

/// Componentwise linear interpolation of two sizes.
pub open spec fn lerp_size<T: OrderedField>(a: Size<T>, b: Size<T>, t: T) -> Size<T> {
    Size::new(
        scalar_lerp(a.width, b.width, t),
        scalar_lerp(a.height, b.height, t),
    )
}

// ── Node tree interpolation ───────────────────────────────────────

/// Recursive node tree interpolation. Interpolates x, y, width, height
/// componentwise. Requires matching child counts; falls back to `a` when
/// fuel=0 or children don't match.
pub open spec fn lerp_node<T: OrderedField>(
    a: Node<T>,
    b: Node<T>,
    t: T,
    fuel: nat,
) -> Node<T>
    decreases fuel,
{
    if fuel == 0 || a.children.len() != b.children.len() {
        a
    } else {
        Node {
            x: scalar_lerp(a.x, b.x, t),
            y: scalar_lerp(a.y, b.y, t),
            size: lerp_size(a.size, b.size, t),
            children: Seq::new(a.children.len(), |i: int|
                lerp_node(a.children[i], b.children[i], t, (fuel - 1) as nat)
            ),
        }
    }
}

// ── Scalar lerp lemmas ────────────────────────────────────────────

/// scalar_lerp(a, b, 0) ≡ a.
pub proof fn lemma_scalar_lerp_zero<T: OrderedField>(a: T, b: T)
    ensures
        scalar_lerp::<T>(a, b, T::zero()).eqv(a),
{
    // scalar_lerp(a, b, 0) = convex(b, a, 0) ≡ a
    lemma_convex_at_zero::<T>(b, a);
}

/// scalar_lerp(a, b, 1) ≡ b.
pub proof fn lemma_scalar_lerp_one<T: OrderedField>(a: T, b: T)
    ensures
        scalar_lerp::<T>(a, b, T::one()).eqv(b),
{
    // scalar_lerp(a, b, 1) = convex(b, a, 1) ≡ b
    lemma_convex_at_one::<T>(b, a);
}

/// scalar_lerp(a, a, t) ≡ a (interpolating between identical values).
pub proof fn lemma_scalar_lerp_self<T: OrderedField>(a: T, t: T)
    ensures
        scalar_lerp::<T>(a, a, t).eqv(a),
{
    lemma_convex_self::<T>(a, t);
}

/// When a ≤ b and 0 ≤ t ≤ 1, scalar_lerp stays in [a, b].
pub proof fn lemma_scalar_lerp_bounds<T: OrderedField>(a: T, b: T, t: T)
    requires
        a.le(b),
        T::zero().le(t),
        t.le(T::one()),
    ensures
        a.le(scalar_lerp::<T>(a, b, t)),
        scalar_lerp::<T>(a, b, t).le(b),
{
    // scalar_lerp(a, b, t) = convex(b, a, t)
    // convex_bounds requires a ≤ b → a ≤ convex(a, b, t) ≤ b
    // We have convex(b, a, t) — use complement: convex(b, a, t) ≡ convex(a, b, 1-t)
    lemma_convex_complement::<T>(b, a, t);

    // Derive: 0 ≤ 1-t (from t ≤ 1)
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg;
    lemma_le_iff_sub_nonneg::<T>(t, T::one());
    // t.le(1) <==> zero.le(1.sub(t))

    // Derive: 1-t ≤ 1 (from 0 ≤ t)
    // Strategy: 0 ≤ t → -t ≤ 0 → 1-t ≤ 1
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone;
    lemma_le_sub_monotone::<T>(T::zero(), t, t);
    // zero.sub(t).le(t.sub(t))
    use verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self;
    lemma_sub_self::<T>(t);
    // t.sub(t).eqv(zero)

    // Bridge: zero.sub(t).eqv(zero.add(t.neg())) via axiom_sub_is_add_neg
    T::axiom_sub_is_add_neg(T::zero(), t);
    // zero.sub(t).eqv(zero.add(t.neg()))
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    lemma_add_zero_left::<T>(t.neg());
    // zero.add(t.neg()).eqv(t.neg())
    T::axiom_eqv_transitive(T::zero().sub(t), T::zero().add(t.neg()), t.neg());
    // zero.sub(t).eqv(t.neg())

    // So t.neg().le(zero) via congruence
    T::axiom_le_congruence(
        T::zero().sub(t), t.neg(),
        t.sub(t), T::zero(),
    );
    // t.neg().le(zero)

    // 1-t ≤ 1: from t.neg().le(zero), add 1 to both sides
    T::axiom_le_add_monotone(t.neg(), T::zero(), T::one());
    // t.neg().add(one).le(zero.add(one))
    lemma_add_zero_left::<T>(T::one());
    T::axiom_add_commutative(t.neg(), T::one());
    // Bridge: one.sub(t).eqv(one.add(t.neg())) via axiom_sub_is_add_neg
    T::axiom_sub_is_add_neg(T::one(), t);
    T::axiom_eqv_symmetric(T::one().sub(t), T::one().add(t.neg()));
    // one.add(t.neg()).eqv(one.sub(t))
    // Chain: t.neg().add(one) → one.add(t.neg()) → one.sub(t)
    T::axiom_eqv_transitive(
        t.neg().add(T::one()), T::one().add(t.neg()), T::one().sub(t),
    );
    T::axiom_le_congruence(
        t.neg().add(T::one()), T::one().sub(t),
        T::zero().add(T::one()), T::one(),
    );

    lemma_convex_bounds::<T>(a, b, T::one().sub(t));
    // a ≤ convex(a, b, 1-t) ≤ b

    // Transfer via eqv: convex(b, a, t) ≡ convex(a, b, 1-t)
    T::axiom_eqv_reflexive(a);
    T::axiom_eqv_symmetric(
        convex::<T>(b, a, t), convex::<T>(a, b, T::one().sub(t)),
    );
    T::axiom_le_congruence(
        a, a,
        convex::<T>(a, b, T::one().sub(t)), convex::<T>(b, a, t),
    );

    T::axiom_eqv_reflexive(b);
    T::axiom_le_congruence(
        convex::<T>(a, b, T::one().sub(t)), convex::<T>(b, a, t),
        b, b,
    );
}

// ── Children match deep ──────────────────────────────────────────

/// Whether two nodes have matching children counts at every level to given depth.
pub open spec fn children_match_deep<T: OrderedRing>(
    a: Node<T>, b: Node<T>, depth: nat,
) -> bool
    decreases depth,
{
    a.children.len() == b.children.len()
    && (depth > 0 ==> forall|i: int| 0 <= i < a.children.len() ==>
        children_match_deep(a.children[i], b.children[i], (depth - 1) as nat))
}

/// children_match_deep is reflexive: any node matches itself at any depth.
pub proof fn lemma_children_match_deep_self<T: OrderedRing>(a: Node<T>, depth: nat)
    ensures children_match_deep(a, a, depth),
    decreases depth,
{
    if depth > 0 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            children_match_deep(a.children[i], a.children[i], (depth - 1) as nat)
        by {
            lemma_children_match_deep_self::<T>(a.children[i], (depth - 1) as nat);
        };
    }
}

/// nodes_deeply_eqv implies children_match_deep (deep eqv is stronger).
pub proof fn lemma_deeply_eqv_implies_children_match<T: OrderedRing>(
    a: Node<T>, b: Node<T>, depth: nat,
)
    requires nodes_deeply_eqv(a, b, depth),
    ensures children_match_deep(a, b, depth),
    decreases depth,
{
    if depth > 0 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            children_match_deep(a.children[i], b.children[i], (depth - 1) as nat)
        by {
            lemma_deeply_eqv_implies_children_match::<T>(
                a.children[i], b.children[i], (depth - 1) as nat,
            );
        };
    }
}

// ── Node lerp lemmas ──────────────────────────────────────────────

/// lerp_node(a, b, 0, fuel) is eqv to a at the top level.
pub proof fn lemma_lerp_node_zero<T: OrderedField>(
    a: Node<T>,
    b: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
    ensures
        nodes_deeply_eqv(lerp_node(a, b, T::zero(), fuel), a, 0),
{
    if a.children.len() != b.children.len() {
        crate::diff::lemma_deeply_eqv_reflexive(a, 0);
    } else {
        lemma_scalar_lerp_zero::<T>(a.x, b.x);
        lemma_scalar_lerp_zero::<T>(a.y, b.y);
        lemma_scalar_lerp_zero::<T>(a.size.width, b.size.width);
        lemma_scalar_lerp_zero::<T>(a.size.height, b.size.height);
    }
}

/// lerp_node(a, b, 1, fuel) is eqv to b at the top level (when children counts match).
pub proof fn lemma_lerp_node_one<T: OrderedField>(
    a: Node<T>,
    b: Node<T>,
    fuel: nat,
)
    requires
        fuel > 0,
        a.children.len() == b.children.len(),
    ensures
        nodes_deeply_eqv(lerp_node(a, b, T::one(), fuel), b, 0),
{
    lemma_scalar_lerp_one::<T>(a.x, b.x);
    lemma_scalar_lerp_one::<T>(a.y, b.y);
    lemma_scalar_lerp_one::<T>(a.size.width, b.size.width);
    lemma_scalar_lerp_one::<T>(a.size.height, b.size.height);
}

/// lerp_node(a, a, t, fuel) is eqv to a at the top level.
pub proof fn lemma_lerp_node_self<T: OrderedField>(
    a: Node<T>,
    t: T,
    fuel: nat,
)
    requires
        fuel > 0,
    ensures
        nodes_deeply_eqv(lerp_node(a, a, t, fuel), a, 0),
{
    lemma_scalar_lerp_self::<T>(a.x, t);
    lemma_scalar_lerp_self::<T>(a.y, t);
    lemma_scalar_lerp_self::<T>(a.size.width, t);
    lemma_scalar_lerp_self::<T>(a.size.height, t);
}

/// Interpolating two nonneg sizes with 0 ≤ t ≤ 1 yields a nonneg size.
pub proof fn lemma_lerp_size_nonneg<T: OrderedField>(a: Size<T>, b: Size<T>, t: T)
    requires
        a.is_nonneg(),
        b.is_nonneg(),
        T::zero().le(t),
        t.le(T::one()),
    ensures
        lerp_size(a, b, t).is_nonneg(),
{
    // scalar_lerp(a, b, t) = convex(b, a, t) = t*b + (1-t)*a
    // Both a,b ≥ 0, t ≥ 0, (1-t) ≥ 0 → each term ≥ 0, sum ≥ 0.

    // Derive 0 ≤ 1-t (from t ≤ 1)
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg;
    lemma_le_iff_sub_nonneg::<T>(t, T::one());
    // zero.le(one.sub(t))

    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_nonneg_mul_nonneg;
    use verus_algebra::inequalities::lemma_nonneg_add;

    // Width: t*b.width ≥ 0 and (1-t)*a.width ≥ 0 → sum ≥ 0
    lemma_nonneg_mul_nonneg::<T>(t, b.width);
    lemma_nonneg_mul_nonneg::<T>(T::one().sub(t), a.width);
    lemma_nonneg_add::<T>(t.mul(b.width), T::one().sub(t).mul(a.width));

    // Height: same argument
    lemma_nonneg_mul_nonneg::<T>(t, b.height);
    lemma_nonneg_mul_nonneg::<T>(T::one().sub(t), a.height);
    lemma_nonneg_add::<T>(t.mul(b.height), T::one().sub(t).mul(a.height));
}

// ── Deep node lerp lemmas ────────────────────────────────────────

/// lerp_node(a, b, 0, fuel) is deeply eqv to a.
pub proof fn lemma_lerp_node_zero_deep<T: OrderedField>(
    a: Node<T>, b: Node<T>, fuel: nat,
)
    requires fuel > 0,
    ensures nodes_deeply_eqv(lerp_node(a, b, T::zero(), fuel), a, (fuel - 1) as nat),
    decreases fuel,
{
    if a.children.len() != b.children.len() {
        // lerp_node returns a → reflexive
        crate::diff::lemma_deeply_eqv_reflexive(a, (fuel - 1) as nat);
    } else {
        lemma_scalar_lerp_zero::<T>(a.x, b.x);
        lemma_scalar_lerp_zero::<T>(a.y, b.y);
        lemma_scalar_lerp_zero::<T>(a.size.width, b.size.width);
        lemma_scalar_lerp_zero::<T>(a.size.height, b.size.height);
        if fuel > 1 {
            assert forall|i: int| 0 <= i < a.children.len() implies
                nodes_deeply_eqv(
                    lerp_node(a.children[i], b.children[i], T::zero(), (fuel - 1) as nat),
                    a.children[i], (fuel - 2) as nat,
                )
            by {
                lemma_lerp_node_zero_deep::<T>(
                    a.children[i], b.children[i], (fuel - 1) as nat,
                );
            };
        }
    }
}

/// lerp_node(a, a, t, fuel) is deeply eqv to a.
pub proof fn lemma_lerp_node_self_deep<T: OrderedField>(
    a: Node<T>, t: T, fuel: nat,
)
    requires fuel > 0,
    ensures nodes_deeply_eqv(lerp_node(a, a, t, fuel), a, (fuel - 1) as nat),
    decreases fuel,
{
    // a.children.len() == a.children.len() always holds → enters interpolation case
    lemma_scalar_lerp_self::<T>(a.x, t);
    lemma_scalar_lerp_self::<T>(a.y, t);
    lemma_scalar_lerp_self::<T>(a.size.width, t);
    lemma_scalar_lerp_self::<T>(a.size.height, t);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_deeply_eqv(
                lerp_node(a.children[i], a.children[i], t, (fuel - 1) as nat),
                a.children[i], (fuel - 2) as nat,
            )
        by {
            lemma_lerp_node_self_deep::<T>(a.children[i], t, (fuel - 1) as nat);
        };
    }
}

/// lerp_node(a, b, 1, fuel) is deeply eqv to b when children counts match.
pub proof fn lemma_lerp_node_one_deep<T: OrderedField>(
    a: Node<T>, b: Node<T>, fuel: nat,
)
    requires
        fuel > 0,
        children_match_deep(a, b, (fuel - 1) as nat),
    ensures
        nodes_deeply_eqv(lerp_node(a, b, T::one(), fuel), b, (fuel - 1) as nat),
    decreases fuel,
{
    // children_match_deep gives a.children.len() == b.children.len()
    lemma_scalar_lerp_one::<T>(a.x, b.x);
    lemma_scalar_lerp_one::<T>(a.y, b.y);
    lemma_scalar_lerp_one::<T>(a.size.width, b.size.width);
    lemma_scalar_lerp_one::<T>(a.size.height, b.size.height);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_deeply_eqv(
                lerp_node(a.children[i], b.children[i], T::one(), (fuel - 1) as nat),
                b.children[i], (fuel - 2) as nat,
            )
        by {
            // children_match_deep at depth > 0 gives children_match_deep on children
            lemma_lerp_node_one_deep::<T>(
                a.children[i], b.children[i], (fuel - 1) as nat,
            );
        };
    }
}

// ── Scalar lerp congruence ───────────────────────────────────────

/// scalar_lerp(a1, b, t) ≡ scalar_lerp(a2, b, t) when a1 ≡ a2.
pub proof fn lemma_scalar_lerp_congruence_left<T: OrderedField>(
    a1: T, a2: T, b: T, t: T,
)
    requires a1.eqv(a2),
    ensures scalar_lerp(a1, b, t).eqv(scalar_lerp(a2, b, t)),
{
    // scalar_lerp(a, b, t) = convex(b, a, t) = t.mul(b).add(one.sub(t).mul(a))
    // a1 ≡ a2 → (1-t)*a1 ≡ (1-t)*a2
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence_right;
    lemma_mul_congruence_right::<T>(T::one().sub(t), a1, a2);
    // Need: t.mul(b).add((1-t)*a1) ≡ t.mul(b).add((1-t)*a2)
    T::axiom_eqv_reflexive(t.mul(b));
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
    lemma_add_congruence::<T>(
        t.mul(b), t.mul(b),
        T::one().sub(t).mul(a1), T::one().sub(t).mul(a2),
    );
}

/// scalar_lerp(a, b1, t) ≡ scalar_lerp(a, b2, t) when b1 ≡ b2.
pub proof fn lemma_scalar_lerp_congruence_right<T: OrderedField>(
    a: T, b1: T, b2: T, t: T,
)
    requires b1.eqv(b2),
    ensures scalar_lerp(a, b1, t).eqv(scalar_lerp(a, b2, t)),
{
    // scalar_lerp(a, b, t) = t.mul(b).add(one.sub(t).mul(a))
    // b1 ≡ b2 → t*b1 ≡ t*b2
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence_right;
    lemma_mul_congruence_right::<T>(t, b1, b2);
    // t*b1 + (1-t)*a ≡ t*b2 + (1-t)*a
    T::axiom_eqv_reflexive(T::one().sub(t).mul(a));
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
    lemma_add_congruence::<T>(
        t.mul(b1), t.mul(b2),
        T::one().sub(t).mul(a), T::one().sub(t).mul(a),
    );
}

// ── Deep node lerp congruence ────────────────────────────────────

/// lerp_node(a1, b, t, fuel) deeply ≡ lerp_node(a2, b, t, fuel) when a1 deeply ≡ a2.
pub proof fn lemma_lerp_node_congruence_left<T: OrderedField>(
    a1: Node<T>, a2: Node<T>, b: Node<T>, t: T, fuel: nat,
)
    requires
        fuel > 0,
        nodes_deeply_eqv(a1, a2, (fuel - 1) as nat),
    ensures
        nodes_deeply_eqv(
            lerp_node(a1, b, t, fuel),
            lerp_node(a2, b, t, fuel),
            (fuel - 1) as nat,
        ),
    decreases fuel,
{
    // a1.children.len() == a2.children.len() from deep eqv
    if a1.children.len() != b.children.len() {
        // Both return a1, a2 respectively → use precondition directly
    } else {
        // Both enter interpolation case
        lemma_scalar_lerp_congruence_left::<T>(a1.x, a2.x, b.x, t);
        lemma_scalar_lerp_congruence_left::<T>(a1.y, a2.y, b.y, t);
        lemma_scalar_lerp_congruence_left::<T>(a1.size.width, a2.size.width, b.size.width, t);
        lemma_scalar_lerp_congruence_left::<T>(a1.size.height, a2.size.height, b.size.height, t);
        if fuel > 1 {
            assert forall|i: int| 0 <= i < a1.children.len() implies
                nodes_deeply_eqv(
                    lerp_node(a1.children[i], b.children[i], t, (fuel - 1) as nat),
                    lerp_node(a2.children[i], b.children[i], t, (fuel - 1) as nat),
                    (fuel - 2) as nat,
                )
            by {
                lemma_lerp_node_congruence_left::<T>(
                    a1.children[i], a2.children[i], b.children[i], t, (fuel - 1) as nat,
                );
            };
        }
    }
}

/// lerp_node(a, b1, t, fuel) deeply ≡ lerp_node(a, b2, t, fuel) when b1 deeply ≡ b2.
pub proof fn lemma_lerp_node_congruence_right<T: OrderedField>(
    a: Node<T>, b1: Node<T>, b2: Node<T>, t: T, fuel: nat,
)
    requires
        fuel > 0,
        nodes_deeply_eqv(b1, b2, (fuel - 1) as nat),
    ensures
        nodes_deeply_eqv(
            lerp_node(a, b1, t, fuel),
            lerp_node(a, b2, t, fuel),
            (fuel - 1) as nat,
        ),
    decreases fuel,
{
    // b1.children.len() == b2.children.len() from deep eqv
    if a.children.len() != b1.children.len() {
        // Both a.len != b1.len and a.len != b2.len → both return a → reflexive
        crate::diff::lemma_deeply_eqv_reflexive(a, (fuel - 1) as nat);
    } else {
        // Both enter interpolation case
        lemma_scalar_lerp_congruence_right::<T>(a.x, b1.x, b2.x, t);
        lemma_scalar_lerp_congruence_right::<T>(a.y, b1.y, b2.y, t);
        lemma_scalar_lerp_congruence_right::<T>(a.size.width, b1.size.width, b2.size.width, t);
        lemma_scalar_lerp_congruence_right::<T>(a.size.height, b1.size.height, b2.size.height, t);
        if fuel > 1 {
            assert forall|i: int| 0 <= i < a.children.len() implies
                nodes_deeply_eqv(
                    lerp_node(a.children[i], b1.children[i], t, (fuel - 1) as nat),
                    lerp_node(a.children[i], b2.children[i], t, (fuel - 1) as nat),
                    (fuel - 2) as nat,
                )
            by {
                lemma_lerp_node_congruence_right::<T>(
                    a.children[i], b1.children[i], b2.children[i], t, (fuel - 1) as nat,
                );
            };
        }
    }
}

} // verus!
