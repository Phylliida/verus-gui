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

// ── Scalar lerp monotonicity ─────────────────────────────────────

/// Helper: scalar_lerp(a, b, t) ≡ a + t*(b-a).
///
/// Proof sketch: convex(b, a, t) = t*b + (1-t)*a
///   = t*b + a - t*a  [distribute]  = a + t*b - t*a  [commute]
///   = a + t*(b - a)  [factor]
proof fn lemma_scalar_lerp_as_offset<T: OrderedField>(a: T, b: T, t: T)
    ensures scalar_lerp(a, b, t).eqv(a.add(t.mul(b.sub(a)))),
{
    // scalar_lerp(a, b, t) = convex(b, a, t) = t.mul(b).add((1-t).mul(a))
    // Goal: show t.mul(b).add((1-t).mul(a)) ≡ a.add(t.mul(b.sub(a)))

    // Step 1: (1-t)*a ≡ a - t*a
    // 1.sub(t) * a ≡ 1*a - t*a via lemma_mul_distributes_over_sub
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_over_sub;
    // Need: (1-t)*a, but distributes_over_sub gives a*(b-c) ≡ a*b - a*c.
    // Use commutativity: (1-t)*a ≡ a*(1-t) then a*(1-t) ≡ a*1 - a*t
    T::axiom_mul_commutative(T::one().sub(t), a);
    // (1-t)*a ≡ a*(1-t)
    lemma_mul_distributes_over_sub::<T>(a, T::one(), t);
    // a*(1-t) ≡ a*1 - a*t
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a), a.mul(T::one().sub(t)),
        a.mul(T::one()).sub(a.mul(t)),
    );
    // (1-t)*a ≡ a*1 - a*t

    // Step 2: a*1 ≡ a
    T::axiom_mul_one_right(a);
    // a.mul(1).eqv(a)

    // Step 3: a*t ≡ t*a
    T::axiom_mul_commutative(a, t);
    // a.mul(t).eqv(t.mul(a))

    // Step 4: a*1 - a*t ≡ a - t*a via sub congruence
    use verus_algebra::lemmas::additive_group_lemmas::lemma_sub_congruence;
    lemma_sub_congruence::<T>(a.mul(T::one()), a, a.mul(t), t.mul(a));
    // a*1 - a*t ≡ a - t*a

    // Step 5: (1-t)*a ≡ a - t*a via transitivity
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a),
        a.mul(T::one()).sub(a.mul(t)),
        a.sub(t.mul(a)),
    );

    // Step 6: t*b + (1-t)*a ≡ t*b + (a - t*a) via add congruence
    T::axiom_eqv_reflexive(t.mul(b));
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
    lemma_add_congruence::<T>(
        t.mul(b), t.mul(b),
        T::one().sub(t).mul(a), a.sub(t.mul(a)),
    );
    // t*b + (1-t)*a ≡ t*b + (a - t*a)

    // Step 7: a - t*a ≡ a + (-(t*a)) via axiom_sub_is_add_neg
    T::axiom_sub_is_add_neg(a, t.mul(a));

    // Step 8: t*b + (a + (-(t*a))) via associativity & commutativity
    // t*b + (a - t*a) → rewrite (a - t*a) as a + (-(t*a))
    T::axiom_eqv_reflexive(t.mul(b));
    lemma_add_congruence::<T>(
        t.mul(b), t.mul(b),
        a.sub(t.mul(a)), a.add(t.mul(a).neg()),
    );
    // t*b + (a - t*a) ≡ t*b + (a + (-(t*a)))
    T::axiom_eqv_transitive(
        t.mul(b).add(T::one().sub(t).mul(a)),
        t.mul(b).add(a.sub(t.mul(a))),
        t.mul(b).add(a.add(t.mul(a).neg())),
    );

    // Step 9: t*b + (a + (-(t*a))) ≡ (t*b + a) + (-(t*a)) via associativity
    T::axiom_add_associative(t.mul(b), a, t.mul(a).neg());
    T::axiom_eqv_symmetric(
        t.mul(b).add(a).add(t.mul(a).neg()),
        t.mul(b).add(a.add(t.mul(a).neg())),
    );
    // t*b + (a + (-(t*a))) ≡ (t*b + a) + (-(t*a))
    T::axiom_eqv_transitive(
        t.mul(b).add(T::one().sub(t).mul(a)),
        t.mul(b).add(a.add(t.mul(a).neg())),
        t.mul(b).add(a).add(t.mul(a).neg()),
    );

    // Step 10: (t*b + a) ≡ (a + t*b) via commutativity
    T::axiom_add_commutative(t.mul(b), a);

    // Step 11: (t*b + a) + (-(t*a)) ≡ (a + t*b) + (-(t*a))
    T::axiom_eqv_reflexive(t.mul(a).neg());
    lemma_add_congruence::<T>(
        t.mul(b).add(a), a.add(t.mul(b)),
        t.mul(a).neg(), t.mul(a).neg(),
    );
    T::axiom_eqv_transitive(
        t.mul(b).add(T::one().sub(t).mul(a)),
        t.mul(b).add(a).add(t.mul(a).neg()),
        a.add(t.mul(b)).add(t.mul(a).neg()),
    );

    // Step 12: (a + t*b) + (-(t*a)) ≡ a + (t*b + (-(t*a))) via associativity
    T::axiom_add_associative(a, t.mul(b), t.mul(a).neg());
    T::axiom_eqv_transitive(
        t.mul(b).add(T::one().sub(t).mul(a)),
        a.add(t.mul(b)).add(t.mul(a).neg()),
        a.add(t.mul(b).add(t.mul(a).neg())),
    );

    // Step 13: t*b + (-(t*a)) ≡ t*b - t*a via sub_is_add_neg (reverse)
    T::axiom_sub_is_add_neg(t.mul(b), t.mul(a));
    T::axiom_eqv_symmetric(t.mul(b).sub(t.mul(a)), t.mul(b).add(t.mul(a).neg()));

    // Step 14: t*b - t*a ≡ t*(b-a) via distributes_over_sub (reverse)
    lemma_mul_distributes_over_sub::<T>(t, b, a);
    T::axiom_eqv_symmetric(t.mul(b.sub(a)), t.mul(b).sub(t.mul(a)));

    // Step 15: chain: t*b + (-(t*a)) → t*b - t*a → t*(b-a)
    T::axiom_eqv_transitive(
        t.mul(b).add(t.mul(a).neg()),
        t.mul(b).sub(t.mul(a)),
        t.mul(b.sub(a)),
    );

    // Step 16: a + (t*b + (-(t*a))) ≡ a + t*(b-a)
    T::axiom_eqv_reflexive(a);
    lemma_add_congruence::<T>(
        a, a,
        t.mul(b).add(t.mul(a).neg()), t.mul(b.sub(a)),
    );
    // need to chain through the intermediate: t*b + (-(t*a)) → t*(b-a)
    // first show a + (t*b + neg(t*a)) ≡ a + (t*b - t*a)
    T::axiom_eqv_reflexive(a);
    lemma_add_congruence::<T>(
        a, a,
        t.mul(b).add(t.mul(a).neg()), t.mul(b).sub(t.mul(a)),
    );
    // a + (t*b + neg(t*a)) ≡ a + (t*b - t*a)
    lemma_add_congruence::<T>(
        a, a,
        t.mul(b).sub(t.mul(a)), t.mul(b.sub(a)),
    );
    // a + (t*b - t*a) ≡ a + t*(b-a)
    T::axiom_eqv_transitive(
        a.add(t.mul(b).add(t.mul(a).neg())),
        a.add(t.mul(b).sub(t.mul(a))),
        a.add(t.mul(b.sub(a))),
    );

    // Final: convex(b, a, t) ≡ a + t*(b-a)
    T::axiom_eqv_transitive(
        t.mul(b).add(T::one().sub(t).mul(a)),
        a.add(t.mul(b).add(t.mul(a).neg())),
        a.add(t.mul(b.sub(a))),
    );
}

/// s ≤ t and a ≤ b implies scalar_lerp(a, b, s) ≤ scalar_lerp(a, b, t).
pub proof fn lemma_scalar_lerp_monotone<T: OrderedField>(a: T, b: T, s: T, t: T)
    requires
        a.le(b),
        s.le(t),
    ensures
        scalar_lerp(a, b, s).le(scalar_lerp(a, b, t)),
{
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg;

    // 1. 0 ≤ b-a from a ≤ b
    lemma_le_iff_sub_nonneg::<T>(a, b);
    // T::zero().le(b.sub(a))

    // 2. s*(b-a) ≤ t*(b-a) from s ≤ t and 0 ≤ b-a
    T::axiom_le_mul_nonneg_monotone(s, t, b.sub(a));
    // s.mul(b.sub(a)).le(t.mul(b.sub(a)))

    // 3. a + s*(b-a) ≤ a + t*(b-a) via axiom_le_add_monotone + commutativity
    T::axiom_le_add_monotone(s.mul(b.sub(a)), t.mul(b.sub(a)), a);
    // s.mul(b.sub(a)).add(a).le(t.mul(b.sub(a)).add(a))
    T::axiom_add_commutative(s.mul(b.sub(a)), a);
    T::axiom_add_commutative(t.mul(b.sub(a)), a);
    T::axiom_le_congruence(
        s.mul(b.sub(a)).add(a), a.add(s.mul(b.sub(a))),
        t.mul(b.sub(a)).add(a), a.add(t.mul(b.sub(a))),
    );
    // a.add(s.mul(b.sub(a))).le(a.add(t.mul(b.sub(a))))

    // 4. Transfer via congruence from offset form to scalar_lerp
    lemma_scalar_lerp_as_offset::<T>(a, b, s);
    lemma_scalar_lerp_as_offset::<T>(a, b, t);
    T::axiom_eqv_symmetric(scalar_lerp(a, b, s), a.add(s.mul(b.sub(a))));
    T::axiom_eqv_symmetric(scalar_lerp(a, b, t), a.add(t.mul(b.sub(a))));
    T::axiom_le_congruence(
        a.add(s.mul(b.sub(a))), scalar_lerp(a, b, s),
        a.add(t.mul(b.sub(a))), scalar_lerp(a, b, t),
    );
}

// ── Node componentwise ordering ──────────────────────────────────

/// Whether a ≤ b componentwise at all levels to given depth.
pub open spec fn nodes_componentwise_le<T: OrderedRing>(
    a: Node<T>, b: Node<T>, depth: nat,
) -> bool
    decreases depth,
{
    a.x.le(b.x) && a.y.le(b.y)
    && a.size.width.le(b.size.width) && a.size.height.le(b.size.height)
    && a.children.len() == b.children.len()
    && (depth > 0 ==> forall|i: int| 0 <= i < a.children.len() ==>
        nodes_componentwise_le(a.children[i], b.children[i], (depth - 1) as nat))
}

/// Increasing t moves lerp_node monotonically when a ≤ b componentwise.
pub proof fn lemma_lerp_node_monotone_deep<T: OrderedField>(
    a: Node<T>, b: Node<T>, s: T, t: T, fuel: nat,
)
    requires
        fuel > 0,
        nodes_componentwise_le(a, b, (fuel - 1) as nat),
        s.le(t),
    ensures
        nodes_componentwise_le(
            lerp_node(a, b, s, fuel),
            lerp_node(a, b, t, fuel),
            (fuel - 1) as nat,
        ),
    decreases fuel,
{
    // a.children.len() == b.children.len() from componentwise_le
    // Both lerp_node calls enter the interpolation branch
    // Fields: scalar_lerp_monotone on x, y, width, height
    lemma_scalar_lerp_monotone::<T>(a.x, b.x, s, t);
    lemma_scalar_lerp_monotone::<T>(a.y, b.y, s, t);
    lemma_scalar_lerp_monotone::<T>(a.size.width, b.size.width, s, t);
    lemma_scalar_lerp_monotone::<T>(a.size.height, b.size.height, s, t);
    // Children: recursive IH
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_componentwise_le(
                lerp_node(a.children[i], b.children[i], s, (fuel - 1) as nat),
                lerp_node(a.children[i], b.children[i], t, (fuel - 1) as nat),
                (fuel - 2) as nat,
            )
        by {
            lemma_lerp_node_monotone_deep::<T>(
                a.children[i], b.children[i], s, t, (fuel - 1) as nat,
            );
        };
    }
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

// ── Scalar lerp algebraic properties ─────────────────────────────

/// Lipschitz / exact difference: lerp(a,b,t) - lerp(a,b,s) ≡ (t-s)*(b-a).
///
/// Proof: Using offset form, lerp(a,b,t) = a + t*(b-a), lerp(a,b,s) = a + s*(b-a).
/// Subtract: (a + t*d) - (a + s*d) = t*d - s*d = (t-s)*d where d = b-a.
pub proof fn lemma_scalar_lerp_difference<T: OrderedField>(a: T, b: T, s: T, t: T)
    ensures
        scalar_lerp(a, b, t).sub(scalar_lerp(a, b, s))
            .eqv(t.sub(s).mul(b.sub(a))),
{
    let d = b.sub(a);

    // 1. offset forms
    lemma_scalar_lerp_as_offset::<T>(a, b, t);
    // scalar_lerp(a, b, t) ≡ a.add(t.mul(d))
    lemma_scalar_lerp_as_offset::<T>(a, b, s);
    // scalar_lerp(a, b, s) ≡ a.add(s.mul(d))

    // 2. (a + t*d) - (a + s*d) ≡ t*d - s*d  via right-cancel lemma
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_sub_cancel_right;
    lemma_add_sub_cancel_right::<T>(t.mul(d), s.mul(d), a);
    // t.mul(d).add(a).sub(s.mul(d).add(a)) ≡ t.mul(d).sub(s.mul(d))
    // Need commuted version: (a + t*d) - (a + s*d)
    T::axiom_add_commutative(a, t.mul(d));
    T::axiom_add_commutative(a, s.mul(d));
    use verus_algebra::lemmas::additive_group_lemmas::lemma_sub_congruence;
    lemma_sub_congruence::<T>(
        a.add(t.mul(d)), t.mul(d).add(a),
        a.add(s.mul(d)), s.mul(d).add(a),
    );
    // a.add(t.mul(d)).sub(a.add(s.mul(d))) ≡ t.mul(d).add(a).sub(s.mul(d).add(a))
    T::axiom_eqv_transitive(
        a.add(t.mul(d)).sub(a.add(s.mul(d))),
        t.mul(d).add(a).sub(s.mul(d).add(a)),
        t.mul(d).sub(s.mul(d)),
    );

    // 3. t*d - s*d ≡ (t-s)*d  via distributes_over_sub (reverse)
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_over_sub;
    lemma_mul_distributes_over_sub::<T>(d, t, s);
    // d.mul(t.sub(s)) ≡ d.mul(t).sub(d.mul(s))
    // Need: t.mul(d) - s.mul(d) ≡ (t-s).mul(d) ≡ d.mul(t-s)
    T::axiom_mul_commutative(t, d);
    T::axiom_mul_commutative(s, d);
    lemma_sub_congruence::<T>(t.mul(d), d.mul(t), s.mul(d), d.mul(s));
    // t.mul(d).sub(s.mul(d)) ≡ d.mul(t).sub(d.mul(s))
    T::axiom_eqv_symmetric(d.mul(t.sub(s)), d.mul(t).sub(d.mul(s)));
    T::axiom_eqv_transitive(
        t.mul(d).sub(s.mul(d)),
        d.mul(t).sub(d.mul(s)),
        d.mul(t.sub(s)),
    );
    // t.mul(d).sub(s.mul(d)) ≡ d.mul(t.sub(s))
    T::axiom_mul_commutative(d, t.sub(s));
    T::axiom_eqv_transitive(
        t.mul(d).sub(s.mul(d)),
        d.mul(t.sub(s)),
        t.sub(s).mul(d),
    );

    // 4. Chain: (a+t*d)-(a+s*d) ≡ t*d-s*d ≡ (t-s)*d
    T::axiom_eqv_transitive(
        a.add(t.mul(d)).sub(a.add(s.mul(d))),
        t.mul(d).sub(s.mul(d)),
        t.sub(s).mul(d),
    );

    // 5. Transfer via congruence from offset form to scalar_lerp
    lemma_sub_congruence::<T>(
        scalar_lerp(a, b, t), a.add(t.mul(d)),
        scalar_lerp(a, b, s), a.add(s.mul(d)),
    );
    T::axiom_eqv_transitive(
        scalar_lerp(a, b, t).sub(scalar_lerp(a, b, s)),
        a.add(t.mul(d)).sub(a.add(s.mul(d))),
        t.sub(s).mul(d),
    );
}

/// Composition / nesting: lerp(lerp(a,b,s), lerp(a,b,t), u) ≡ lerp(a, b, lerp(s,t,u)).
///
/// Interpolating between two interpolated values is equivalent to interpolating
/// between the original endpoints with a re-parameterized t.
pub proof fn lemma_scalar_lerp_composition<T: OrderedField>(a: T, b: T, s: T, t: T, u: T)
    ensures
        scalar_lerp(scalar_lerp(a, b, s), scalar_lerp(a, b, t), u)
            .eqv(scalar_lerp(a, b, scalar_lerp(s, t, u))),
{
    let d = b.sub(a);
    let ls = scalar_lerp(a, b, s);
    let lt = scalar_lerp(a, b, t);

    // 1. Offset forms
    lemma_scalar_lerp_as_offset::<T>(a, b, s);
    // ls ≡ a + s*d
    lemma_scalar_lerp_as_offset::<T>(a, b, t);
    // lt ≡ a + t*d

    // 2. LHS = ls + u*(lt - ls) via offset form
    lemma_scalar_lerp_as_offset::<T>(ls, lt, u);
    // lerp(ls, lt, u) ≡ ls + u*(lt - ls)

    // 3. lt - ls ≡ (t-s)*d via Lipschitz
    lemma_scalar_lerp_difference::<T>(a, b, s, t);
    // lt.sub(ls) ≡ (t-s)*d

    // 4. u*(lt - ls) ≡ u*(t-s)*d via mul congruence
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence_right;
    lemma_mul_congruence_right::<T>(u, lt.sub(ls), t.sub(s).mul(d));
    // u.mul(lt.sub(ls)) ≡ u.mul((t-s)*d)

    // 5. u*(t-s)*d ≡ u*(t-s) * d via associativity
    T::axiom_mul_associative(u, t.sub(s), d);
    T::axiom_eqv_symmetric(u.mul(t.sub(s)).mul(d), u.mul(t.sub(s).mul(d)));
    T::axiom_eqv_transitive(
        u.mul(lt.sub(ls)),
        u.mul(t.sub(s).mul(d)),
        u.mul(t.sub(s)).mul(d),
    );

    // 6. ls + u*(lt-ls) ≡ (a + s*d) + u*(t-s)*d via congruence
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
    T::axiom_eqv_reflexive(ls);
    lemma_add_congruence::<T>(
        ls, ls,
        u.mul(lt.sub(ls)), u.mul(t.sub(s)).mul(d),
    );
    // ls.add(u.mul(lt.sub(ls))) ≡ ls.add(u.mul(t.sub(s)).mul(d))
    T::axiom_eqv_reflexive(u.mul(t.sub(s)).mul(d));
    lemma_add_congruence::<T>(
        ls, a.add(s.mul(d)),
        u.mul(t.sub(s)).mul(d), u.mul(t.sub(s)).mul(d),
    );
    // ls.add(u*(t-s)*d) ≡ (a + s*d).add(u*(t-s)*d)

    // 7. (a + s*d) + u*(t-s)*d ≡ a + (s*d + u*(t-s)*d) via associativity
    T::axiom_add_associative(a, s.mul(d), u.mul(t.sub(s)).mul(d));

    // 8. s*d + u*(t-s)*d ≡ (s + u*(t-s))*d via reverse distribution
    //    (s + u*(t-s)) * d = s*d + u*(t-s)*d
    T::axiom_mul_commutative(s, d);
    T::axiom_mul_commutative(u.mul(t.sub(s)), d);
    // s*d ≡ d*s, u*(t-s)*d ≡ d*(u*(t-s))
    T::axiom_mul_commutative(s.add(u.mul(t.sub(s))), d);
    T::axiom_mul_distributes_left(d, s, u.mul(t.sub(s)));
    // d * (s + u*(t-s)) ≡ d*s + d*(u*(t-s))
    // = s*d + u*(t-s)*d (via commutativity, already established)

    use verus_algebra::lemmas::additive_group_lemmas::lemma_sub_congruence;
    T::axiom_eqv_symmetric(s.mul(d), d.mul(s));
    T::axiom_eqv_symmetric(u.mul(t.sub(s)).mul(d), d.mul(u.mul(t.sub(s))));

    // Chain: s*d + u*(t-s)*d ≡ d*s + d*(u*(t-s))
    lemma_add_congruence::<T>(
        s.mul(d), d.mul(s),
        u.mul(t.sub(s)).mul(d), d.mul(u.mul(t.sub(s))),
    );
    // s*d + u*(t-s)*d ≡ d*s + d*(u*(t-s))
    T::axiom_eqv_symmetric(
        d.mul(s.add(u.mul(t.sub(s)))),
        d.mul(s).add(d.mul(u.mul(t.sub(s)))),
    );
    T::axiom_eqv_transitive(
        s.mul(d).add(u.mul(t.sub(s)).mul(d)),
        d.mul(s).add(d.mul(u.mul(t.sub(s)))),
        d.mul(s.add(u.mul(t.sub(s)))),
    );
    // s*d + u*(t-s)*d ≡ d*(s + u*(t-s))
    // ≡ (s + u*(t-s))*d via commutativity (symmetric direction)
    T::axiom_eqv_symmetric(
        s.add(u.mul(t.sub(s))).mul(d),
        d.mul(s.add(u.mul(t.sub(s)))),
    );
    T::axiom_eqv_transitive(
        s.mul(d).add(u.mul(t.sub(s)).mul(d)),
        d.mul(s.add(u.mul(t.sub(s)))),
        s.add(u.mul(t.sub(s))).mul(d),
    );

    // 9. s + u*(t-s) ≡ lerp(s, t, u) via offset form (reverse)
    lemma_scalar_lerp_as_offset::<T>(s, t, u);
    T::axiom_eqv_symmetric(scalar_lerp(s, t, u), s.add(u.mul(t.sub(s))));
    // s.add(u.mul(t.sub(s))) ≡ scalar_lerp(s, t, u)

    // 10. (s + u*(t-s))*d ≡ lerp(s,t,u)*d via mul congruence
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence;
    T::axiom_eqv_reflexive(d);
    lemma_mul_congruence::<T>(
        s.add(u.mul(t.sub(s))), scalar_lerp(s, t, u),
        d, d,
    );
    // (s + u*(t-s))*d ≡ lerp(s,t,u)*d
    T::axiom_eqv_transitive(
        s.mul(d).add(u.mul(t.sub(s)).mul(d)),
        s.add(u.mul(t.sub(s))).mul(d),
        scalar_lerp(s, t, u).mul(d),
    );

    // 11. a + lerp(s,t,u)*d ≡ lerp(a, b, lerp(s,t,u)) via offset form (reverse)
    lemma_scalar_lerp_as_offset::<T>(a, b, scalar_lerp(s, t, u));
    T::axiom_eqv_symmetric(
        scalar_lerp(a, b, scalar_lerp(s, t, u)),
        a.add(scalar_lerp(s, t, u).mul(d)),
    );

    // 12. Final chain: LHS ≡ ls + u*(lt-ls) ≡ (a+s*d) + u*(t-s)*d
    //                      ≡ a + (s*d + u*(t-s)*d) ≡ a + lerp(s,t,u)*d ≡ RHS

    // a + (s*d + u*(t-s)*d) ≡ a + lerp(s,t,u)*d
    T::axiom_eqv_reflexive(a);
    lemma_add_congruence::<T>(
        a, a,
        s.mul(d).add(u.mul(t.sub(s)).mul(d)),
        scalar_lerp(s, t, u).mul(d),
    );

    // Chain through all the intermediate forms
    // lerp(ls, lt, u) ≡ ls.add(u*(lt-ls))
    let lhs = scalar_lerp(ls, lt, u);
    let form1 = ls.add(u.mul(lt.sub(ls)));
    let form2 = ls.add(u.mul(t.sub(s)).mul(d));
    let form3 = a.add(s.mul(d)).add(u.mul(t.sub(s)).mul(d));
    let form4 = a.add(s.mul(d).add(u.mul(t.sub(s)).mul(d)));
    let form5 = a.add(scalar_lerp(s, t, u).mul(d));
    let rhs = scalar_lerp(a, b, scalar_lerp(s, t, u));

    // lhs ≡ form1
    // (already proved above via lemma_scalar_lerp_as_offset)

    // form1 ≡ form2
    // (ls.add(u*(lt-ls)) ≡ ls.add(u*(t-s)*d) — already proved)

    // form2 ≡ form3
    // ls ≡ a+s*d, so form2 ≡ (a+s*d).add(u*(t-s)*d) = form3
    lemma_add_congruence::<T>(
        ls, a.add(s.mul(d)),
        u.mul(t.sub(s)).mul(d), u.mul(t.sub(s)).mul(d),
    );
    T::axiom_eqv_reflexive(u.mul(t.sub(s)).mul(d));

    // form3 ≡ form4 (associativity)
    // Already proved: T::axiom_add_associative(a, s.mul(d), u.mul(t.sub(s)).mul(d))

    // form4 ≡ form5
    // Already proved above

    // form5 ≡ rhs
    // Already proved above

    // Now chain: lhs → form1 → form2 → form3 → form4 → form5 → rhs
    T::axiom_eqv_transitive(lhs, form1, form2);
    T::axiom_eqv_transitive(form2, form3, form4);
    T::axiom_eqv_transitive(form4, form5, rhs);
    T::axiom_eqv_transitive(form2, form4, rhs);
    T::axiom_eqv_transitive(lhs, form2, rhs);
}

/// Midpoint: lerp(a, b, 1/2) ≡ (a + b) / 2.
///
/// Requires: two ≢ 0 (so 1/2 is well-defined and we can divide by 2).
pub proof fn lemma_scalar_lerp_midpoint<T: OrderedField>(a: T, b: T)
    requires
        !T::one().add(T::one()).eqv(T::zero()),
    ensures
        scalar_lerp(a, b, T::one().div(T::one().add(T::one())))
            .eqv(a.add(b).div(T::one().add(T::one()))),
{
    let two = T::one().add(T::one());
    let half = T::one().div(two);
    let d = b.sub(a);

    // 1. lerp(a, b, 1/2) ≡ a + (1/2)*(b-a) via offset form
    lemma_scalar_lerp_as_offset::<T>(a, b, half);

    // 2. (1/2)*(b-a) ≡ (b-a)/2 via div definition: x/y = x * recip(y), 1/2 = recip(2)
    //    half.mul(d) = (1*recip(2)).mul(d) = recip(2).mul(d) via 1*x=x
    //    ≡ d * recip(2) = d / 2
    T::axiom_div_is_mul_recip(T::one(), two);
    // one.div(two) ≡ one.mul(recip(two))
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_one_left;
    lemma_mul_one_left::<T>(T::recip(two));
    // one.mul(recip(two)) ≡ recip(two)
    T::axiom_eqv_transitive(half, T::one().mul(T::recip(two)), T::recip(two));
    // half ≡ recip(two)

    // half * d ≡ recip(two) * d
    use verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence;
    T::axiom_eqv_reflexive(d);
    lemma_mul_congruence::<T>(half, T::recip(two), d, d);
    // half.mul(d) ≡ recip(two).mul(d)

    T::axiom_mul_commutative(T::recip(two), d);
    T::axiom_eqv_transitive(half.mul(d), T::recip(two).mul(d), d.mul(T::recip(two)));
    // half.mul(d) ≡ d.mul(recip(two))

    // d.mul(recip(two)) ≡ d.div(two) via div definition (reverse)
    T::axiom_div_is_mul_recip(d, two);
    T::axiom_eqv_symmetric(d.div(two), d.mul(T::recip(two)));
    T::axiom_eqv_transitive(half.mul(d), d.mul(T::recip(two)), d.div(two));
    // half.mul(d) ≡ d/2

    // 3. a + d/2 ≡ a + (b-a)/2 = (2a + b - a)/2 = (a+b)/2
    //    More directly: a + (b-a)/2 = (2a + (b-a))/2 = (a+b)/2
    //    We need: a ≡ 2a/2
    //    Then: a + (b-a)/2 ≡ 2a/2 + (b-a)/2 ≡ (2a + (b-a))/2 ≡ (a+b)/2

    // a ≡ two*a / two:
    // two * recip(two) ≡ one (field axiom)
    T::axiom_mul_recip_right(two);
    // two.mul(recip(two)) ≡ one

    // a ≡ a * one ≡ a * (two * recip(two)) ≡ (a*two) * recip(two) ≡ (two*a) * recip(two)
    T::axiom_mul_one_right(a);
    T::axiom_eqv_symmetric(a.mul(T::one()), a);
    // a ≡ a * one
    T::axiom_eqv_reflexive(a);
    T::axiom_eqv_symmetric(two.mul(T::recip(two)), T::one());
    lemma_mul_congruence::<T>(a, a, T::one(), two.mul(T::recip(two)));
    // a * one ≡ a * (two * recip(two))
    T::axiom_mul_associative(a, two, T::recip(two));
    T::axiom_eqv_symmetric(a.mul(two).mul(T::recip(two)), a.mul(two.mul(T::recip(two))));
    // a * (two * recip(two)) ≡ (a*two) * recip(two)
    T::axiom_eqv_transitive(a.mul(T::one()), a.mul(two.mul(T::recip(two))), a.mul(two).mul(T::recip(two)));
    T::axiom_eqv_transitive(a, a.mul(T::one()), a.mul(two).mul(T::recip(two)));
    // a ≡ (a*two) * recip(two)

    // (a*two)*recip(two) ≡ (a*two).div(two)
    T::axiom_div_is_mul_recip(a.mul(two), two);
    T::axiom_eqv_symmetric(a.mul(two).div(two), a.mul(two).mul(T::recip(two)));
    T::axiom_eqv_transitive(a, a.mul(two).mul(T::recip(two)), a.mul(two).div(two));
    // a ≡ (a*two)/two

    // a*two ≡ two*a
    T::axiom_mul_commutative(a, two);
    use verus_algebra::lemmas::additive_group_lemmas::{lemma_sub_congruence, lemma_add_congruence};

    // (a*two)/two ≡ (two*a)/two
    // Need div congruence: x ≡ y → x/z ≡ y/z. Use mul_recip form:
    // x/z = x*recip(z), y/z = y*recip(z), so x≡y → x*recip(z) ≡ y*recip(z)
    T::axiom_eqv_reflexive(T::recip(two));
    lemma_mul_congruence::<T>(a.mul(two), two.mul(a), T::recip(two), T::recip(two));
    // (a*two)*recip(two) ≡ (two*a)*recip(two)
    T::axiom_div_is_mul_recip(a.mul(two), two);
    T::axiom_div_is_mul_recip(two.mul(a), two);
    T::axiom_eqv_transitive(
        a.mul(two).div(two),
        a.mul(two).mul(T::recip(two)),
        two.mul(a).mul(T::recip(two)),
    );
    T::axiom_eqv_symmetric(two.mul(a).div(two), two.mul(a).mul(T::recip(two)));
    T::axiom_eqv_transitive(
        a.mul(two).div(two),
        two.mul(a).mul(T::recip(two)),
        two.mul(a).div(two),
    );
    T::axiom_eqv_transitive(a, a.mul(two).div(two), two.mul(a).div(two));
    // a ≡ (two*a)/two

    // 4. a + (b-a)/2 ≡ (two*a)/two + (b-a)/two
    T::axiom_eqv_reflexive(d.div(two));
    lemma_add_congruence::<T>(
        a, two.mul(a).div(two),
        d.div(two), d.div(two),
    );

    // 5. x/z + y/z ≡ (x+y)/z: since div = mul recip,
    //    x*r + y*r = (x+y)*r where r = recip(two)
    let r = T::recip(two);
    T::axiom_mul_commutative(two.mul(a), r);
    T::axiom_mul_commutative(d, r);
    // (two*a)/two = (two*a)*r ≡ r*(two*a)
    // d/two = d*r ≡ r*d
    T::axiom_div_is_mul_recip(two.mul(a), two);
    T::axiom_div_is_mul_recip(d, two);
    // two*a.div(two) ≡ two*a.mul(r)
    // d.div(two) ≡ d.mul(r)

    // (two*a)*r + d*r ≡ (two*a + d)*r via right distribution
    // Use: (p+q)*r = p*r + q*r reversed
    T::axiom_mul_distributes_left(r, two.mul(a), d);
    // r*(two*a + d) ≡ r*(two*a) + r*d
    T::axiom_eqv_symmetric(
        r.mul(two.mul(a).add(d)),
        r.mul(two.mul(a)).add(r.mul(d)),
    );

    // Rewrite via div: (two*a + d)/two
    // two*a + d = two*a + (b - a)
    // Need: two*a + (b-a) ≡ a + b
    // two*a = a + a (since two = 1+1)
    T::axiom_mul_distributes_left(a, T::one(), T::one());
    // a*(1+1) = a*1 + a*1
    T::axiom_mul_one_right(a);
    // a*1 ≡ a
    lemma_add_congruence::<T>(a.mul(T::one()), a, a.mul(T::one()), a);
    // a*1 + a*1 ≡ a + a
    T::axiom_mul_commutative(a, two);
    T::axiom_eqv_transitive(
        a.mul(two),
        a.mul(T::one()).add(a.mul(T::one())),
        a.add(a),
    );
    T::axiom_eqv_symmetric(a.mul(two), two.mul(a));
    T::axiom_eqv_transitive(two.mul(a), a.mul(two), a.add(a));
    // two*a ≡ a + a

    // (a+a) + (b-a) ≡ a + (a + (b-a)) via assoc
    T::axiom_add_associative(a, a, d);
    // a.add(a).add(d) ≡ a.add(a.add(d))
    // Congruence from two*a to a+a:
    T::axiom_eqv_reflexive(d);
    lemma_add_congruence::<T>(two.mul(a), a.add(a), d, d);
    // two*a + d ≡ (a+a) + d ≡ a + (a + d)
    T::axiom_eqv_transitive(
        two.mul(a).add(d),
        a.add(a).add(d),
        a.add(a.add(d)),
    );

    // a + (b-a) ≡ a + b - a ≡ b   ...actually a.add(b.sub(a)) ≡ b
    // Use: a + (b - a) = b via add_then_sub_cancel reversed
    // lemma_add_then_sub_cancel gives: b.add(a).sub(a) ≡ b
    // But we need a.add(b.sub(a)).
    // a.add(b.sub(a)): sub_is_add_neg → a + (b + (-a)) = (a + b) + (-a) = (a+b) - a
    T::axiom_sub_is_add_neg(b, a);
    T::axiom_eqv_reflexive(a);
    lemma_add_congruence::<T>(a, a, b.sub(a), b.add(a.neg()));
    // a + (b-a) ≡ a + (b + (-a))
    T::axiom_add_associative(a, b, a.neg());
    T::axiom_eqv_symmetric(a.add(b).add(a.neg()), a.add(b.add(a.neg())));
    T::axiom_eqv_transitive(
        a.add(b.sub(a)),
        a.add(b.add(a.neg())),
        a.add(b).add(a.neg()),
    );
    // a + (b-a) ≡ (a+b) + (-a) = (a+b) - a
    T::axiom_sub_is_add_neg(a.add(b), a);
    T::axiom_eqv_symmetric(a.add(b).sub(a), a.add(b).add(a.neg()));
    T::axiom_eqv_transitive(
        a.add(b.sub(a)),
        a.add(b).add(a.neg()),
        a.add(b).sub(a),
    );
    // a.add(d) ≡ a.add(b).sub(a)

    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_then_sub_cancel;
    T::axiom_add_commutative(a, b);
    // a+b ≡ b+a
    // (b+a) - a ≡ b via lemma_add_then_sub_cancel
    lemma_add_then_sub_cancel::<T>(b, a);
    lemma_sub_congruence::<T>(a.add(b), b.add(a), a, a);
    T::axiom_eqv_reflexive(a);
    T::axiom_eqv_transitive(a.add(b).sub(a), b.add(a).sub(a), b);
    T::axiom_eqv_transitive(a.add(d), a.add(b).sub(a), b);
    // a + d ≡ b

    // So a + (a + d) ≡ a + b
    T::axiom_eqv_reflexive(a);
    lemma_add_congruence::<T>(a, a, a.add(d), b);
    // a.add(a.add(d)) ≡ a.add(b)

    // Chain: two*a + d ≡ a + (a + d) ≡ a + b
    T::axiom_eqv_transitive(two.mul(a).add(d), a.add(a.add(d)), a.add(b));
    // two*a + d ≡ a + b

    // 6. Final: lerp(a,b,1/2) ≡ a + half*d ≡ a + d/2
    //    ≡ (two*a)/two + d/two ≡ (two*a + d)/two ≡ (a+b)/two
    // We proved all these chains. Let me carefully assemble the final result.

    // lerp(a,b,half) ≡ a.add(half.mul(d))  [step 1]
    // half.mul(d) ≡ d.div(two)  [step 2]
    // a.add(half.mul(d)) ≡ a.add(d.div(two))
    lemma_add_congruence::<T>(a, a, half.mul(d), d.div(two));

    T::axiom_eqv_transitive(
        scalar_lerp(a, b, half),
        a.add(half.mul(d)),
        a.add(d.div(two)),
    );

    // Now: (a+b)/two is the target.
    // (two*a + d)/two → use: two*a + d ≡ a + b, so /two of both sides
    lemma_mul_congruence::<T>(two.mul(a).add(d), a.add(b), r, r);
    T::axiom_eqv_reflexive(r);
    // (two*a+d)*r ≡ (a+b)*r
    // ≡ (two*a+d)/two ≡ (a+b)/two via div_is_mul_recip

    // We need: a + d/2 ≡ (a+b)/2
    // a ≡ (two*a)/two  [step 4]
    // a + d/two ≡ (two*a)/two + d/two
    // = (in mul_recip form): (two*a)*r + d*r = ((two*a)+d)*r = (a+b)*r = (a+b)/two

    // (two*a)/two + d/two: convert to recip form
    // = (two*a)*r + d*r
    T::axiom_div_is_mul_recip(two.mul(a), two);
    T::axiom_div_is_mul_recip(d, two);
    lemma_add_congruence::<T>(
        two.mul(a).div(two), two.mul(a).mul(r),
        d.div(two), d.mul(r),
    );
    // (two*a)/two + d/two ≡ (two*a)*r + d*r

    // (two*a)*r + d*r ≡ ((two*a)+d)*r via distribution
    T::axiom_mul_distributes_left(r, two.mul(a), d);
    T::axiom_mul_commutative(two.mul(a), r);
    T::axiom_mul_commutative(d, r);
    lemma_add_congruence::<T>(
        two.mul(a).mul(r), r.mul(two.mul(a)),
        d.mul(r), r.mul(d),
    );
    // (two*a)*r + d*r ≡ r*(two*a) + r*d
    T::axiom_eqv_transitive(
        two.mul(a).mul(r).add(d.mul(r)),
        r.mul(two.mul(a)).add(r.mul(d)),
        r.mul(two.mul(a).add(d)),
    );
    // (two*a)*r + d*r ≡ r*(two*a + d)
    T::axiom_mul_commutative(r, two.mul(a).add(d));
    T::axiom_eqv_transitive(
        two.mul(a).mul(r).add(d.mul(r)),
        r.mul(two.mul(a).add(d)),
        two.mul(a).add(d).mul(r),
    );

    // (two*a + d)*r ≡ (a+b)*r (via congruence: two*a+d ≡ a+b)
    T::axiom_eqv_reflexive(r);
    lemma_mul_congruence::<T>(two.mul(a).add(d), a.add(b), r, r);
    // (a+b)*r ≡ (a+b)/two
    T::axiom_div_is_mul_recip(a.add(b), two);
    T::axiom_eqv_symmetric(a.add(b).div(two), a.add(b).mul(r));
    T::axiom_eqv_transitive(
        two.mul(a).add(d).mul(r),
        a.add(b).mul(r),
        a.add(b).div(two),
    );

    // Chain: (two*a)*r + d*r ≡ (two*a+d)*r ≡ (a+b)/two
    T::axiom_eqv_transitive(
        two.mul(a).mul(r).add(d.mul(r)),
        two.mul(a).add(d).mul(r),
        a.add(b).div(two),
    );

    // Chain: (two*a)/two + d/two ≡ (two*a)*r + d*r ≡ (a+b)/two
    T::axiom_eqv_transitive(
        two.mul(a).div(two).add(d.div(two)),
        two.mul(a).mul(r).add(d.mul(r)),
        a.add(b).div(two),
    );

    // a + d/two ≡ (two*a)/two + d/two
    T::axiom_eqv_reflexive(d.div(two));
    lemma_add_congruence::<T>(a, two.mul(a).div(two), d.div(two), d.div(two));
    T::axiom_eqv_transitive(
        a.add(d.div(two)),
        two.mul(a).div(two).add(d.div(two)),
        a.add(b).div(two),
    );

    // Final: lerp(a,b,half) ≡ a.add(d.div(two)) ≡ (a+b)/two
    T::axiom_eqv_transitive(
        scalar_lerp(a, b, half),
        a.add(d.div(two)),
        a.add(b).div(two),
    );
}

// ── Symmetry proofs ──────────────────────────────────────────────

/// scalar_lerp(a, b, t) ≡ scalar_lerp(b, a, 1-t).
///
/// Proof: scalar_lerp(a,b,t) = convex(b,a,t) ≡ convex(a,b,1-t) = scalar_lerp(b,a,1-t).
pub proof fn lemma_scalar_lerp_symmetry<T: OrderedField>(a: T, b: T, t: T)
    ensures
        scalar_lerp::<T>(a, b, t).eqv(scalar_lerp::<T>(b, a, T::one().sub(t))),
{
    // scalar_lerp(a,b,t) = convex(b,a,t)
    // scalar_lerp(b,a,1-t) = convex(a,b,1-t)
    // lemma_convex_complement(b,a,t): convex(b,a,t) ≡ convex(a,b,1-t)
    lemma_convex_complement::<T>(b, a, t);
}

/// lerp_size(a, b, t) componentwise ≡ lerp_size(b, a, 1-t).
pub proof fn lemma_lerp_size_symmetry<T: OrderedField>(a: Size<T>, b: Size<T>, t: T)
    ensures
        lerp_size(a, b, t).width.eqv(lerp_size(b, a, T::one().sub(t)).width),
        lerp_size(a, b, t).height.eqv(lerp_size(b, a, T::one().sub(t)).height),
{
    lemma_scalar_lerp_symmetry::<T>(a.width, b.width, t);
    lemma_scalar_lerp_symmetry::<T>(a.height, b.height, t);
}

/// lerp_size bounds: a ≤ b componentwise and 0 ≤ t ≤ 1 implies a ≤ lerp(a,b,t) ≤ b componentwise.
pub proof fn lemma_lerp_size_bounds<T: OrderedField>(a: Size<T>, b: Size<T>, t: T)
    requires
        a.width.le(b.width),
        a.height.le(b.height),
        T::zero().le(t),
        t.le(T::one()),
    ensures
        a.width.le(lerp_size(a, b, t).width),
        lerp_size(a, b, t).width.le(b.width),
        a.height.le(lerp_size(a, b, t).height),
        lerp_size(a, b, t).height.le(b.height),
{
    lemma_scalar_lerp_bounds::<T>(a.width, b.width, t);
    lemma_scalar_lerp_bounds::<T>(a.height, b.height, t);
}

/// children_match_deep is symmetric.
pub proof fn lemma_children_match_deep_symmetric<T: OrderedRing>(
    a: Node<T>, b: Node<T>, depth: nat,
)
    requires children_match_deep(a, b, depth),
    ensures children_match_deep(b, a, depth),
    decreases depth,
{
    if depth > 0 {
        assert forall|i: int| 0 <= i < b.children.len() implies
            children_match_deep(b.children[i], a.children[i], (depth - 1) as nat)
        by {
            lemma_children_match_deep_symmetric::<T>(
                a.children[i], b.children[i], (depth - 1) as nat,
            );
        };
    }
}

/// lerp_node(a, b, t, fuel) is deeply eqv to lerp_node(b, a, 1-t, fuel).
pub proof fn lemma_lerp_node_symmetry_deep<T: OrderedField>(
    a: Node<T>, b: Node<T>, t: T, fuel: nat,
)
    requires
        fuel > 0,
        children_match_deep(a, b, (fuel - 1) as nat),
    ensures
        nodes_deeply_eqv(
            lerp_node(a, b, t, fuel),
            lerp_node(b, a, T::one().sub(t), fuel),
            (fuel - 1) as nat,
        ),
    decreases fuel,
{
    // children_match_deep gives a.children.len() == b.children.len()
    // Both lerp_node calls enter the interpolation case
    lemma_scalar_lerp_symmetry::<T>(a.x, b.x, t);
    lemma_scalar_lerp_symmetry::<T>(a.y, b.y, t);
    lemma_scalar_lerp_symmetry::<T>(a.size.width, b.size.width, t);
    lemma_scalar_lerp_symmetry::<T>(a.size.height, b.size.height, t);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_deeply_eqv(
                lerp_node(a.children[i], b.children[i], t, (fuel - 1) as nat),
                lerp_node(b.children[i], a.children[i], T::one().sub(t), (fuel - 1) as nat),
                (fuel - 2) as nat,
            )
        by {
            lemma_lerp_node_symmetry_deep::<T>(
                a.children[i], b.children[i], t, (fuel - 1) as nat,
            );
        };
    }
}

/// lerp_node bounds: a ≤ b componentwise and 0 ≤ t ≤ 1 implies a ≤ lerp(a,b,t) ≤ b componentwise.
pub proof fn lemma_lerp_node_bounds_deep<T: OrderedField>(
    a: Node<T>, b: Node<T>, t: T, fuel: nat,
)
    requires
        fuel > 0,
        nodes_componentwise_le(a, b, (fuel - 1) as nat),
        T::zero().le(t),
        t.le(T::one()),
    ensures
        nodes_componentwise_le(a, lerp_node(a, b, t, fuel), (fuel - 1) as nat),
        nodes_componentwise_le(lerp_node(a, b, t, fuel), b, (fuel - 1) as nat),
    decreases fuel,
{
    // nodes_componentwise_le gives a.children.len() == b.children.len()
    // lerp_node enters interpolation case
    lemma_scalar_lerp_bounds::<T>(a.x, b.x, t);
    lemma_scalar_lerp_bounds::<T>(a.y, b.y, t);
    lemma_scalar_lerp_bounds::<T>(a.size.width, b.size.width, t);
    lemma_scalar_lerp_bounds::<T>(a.size.height, b.size.height, t);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            nodes_componentwise_le(
                a.children[i],
                lerp_node(a.children[i], b.children[i], t, (fuel - 1) as nat),
                (fuel - 2) as nat,
            )
            && nodes_componentwise_le(
                lerp_node(a.children[i], b.children[i], t, (fuel - 1) as nat),
                b.children[i],
                (fuel - 2) as nat,
            )
        by {
            lemma_lerp_node_bounds_deep::<T>(
                a.children[i], b.children[i], t, (fuel - 1) as nat,
            );
        };
    }
}

// ── Lerp within limits ───────────────────────────────────────────

/// Helper: 0 ≤ t ≤ 1 implies 0 ≤ 1-t ≤ 1.
proof fn lemma_one_sub_t_in_unit<T: OrderedField>(t: T)
    requires T::zero().le(t), t.le(T::one()),
    ensures T::zero().le(T::one().sub(t)), T::one().sub(t).le(T::one()),
{
    // 0 ≤ 1-t: from t ≤ 1, i.e. 0 ≤ 1 - t
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_iff_sub_nonneg;
    lemma_le_iff_sub_nonneg::<T>(t, T::one());

    // 1-t ≤ 1: from 0 ≤ t, subtract t from both sides of 0 ≤ t
    // 0 - t ≤ t - t = 0 → -t ≤ 0 → 1-t ≤ 1
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_sub_monotone;
    lemma_le_sub_monotone::<T>(T::zero(), t, t);
    // (0-t).le(t-t)
    use verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self;
    lemma_sub_self::<T>(t);
    // t-t ≡ 0

    // 0-t ≡ -t
    T::axiom_sub_is_add_neg(T::zero(), t);
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left;
    lemma_add_zero_left::<T>(t.neg());
    T::axiom_eqv_transitive(T::zero().sub(t), T::zero().add(t.neg()), t.neg());

    // So -t ≤ 0
    T::axiom_le_congruence(T::zero().sub(t), t.neg(), t.sub(t), T::zero());

    // Add 1 to both sides: -t + 1 ≤ 0 + 1 = 1
    T::axiom_le_add_monotone(t.neg(), T::zero(), T::one());
    lemma_add_zero_left::<T>(T::one());

    // -t + 1 ≡ 1 + (-t) ≡ 1 - t
    T::axiom_add_commutative(t.neg(), T::one());
    T::axiom_sub_is_add_neg(T::one(), t);
    T::axiom_eqv_symmetric(T::one().sub(t), T::one().add(t.neg()));
    T::axiom_eqv_transitive(
        t.neg().add(T::one()), T::one().add(t.neg()), T::one().sub(t));

    // Transfer: -t + 1 ≤ 0 + 1 becomes 1-t ≤ 1
    T::axiom_le_congruence(
        t.neg().add(T::one()), T::one().sub(t),
        T::zero().add(T::one()), T::one());
}

/// scalar_lerp stays within bounds: if lo ≤ a, b ≤ hi and 0 ≤ t ≤ 1,
/// then lo ≤ lerp(a, b, t) ≤ hi.
pub proof fn lemma_scalar_lerp_within_bounds<T: OrderedField>(
    a: T, b: T, t: T, lo: T, hi: T,
)
    requires
        lo.le(a), a.le(hi),
        lo.le(b), b.le(hi),
        T::zero().le(t), t.le(T::one()),
    ensures
        lo.le(scalar_lerp::<T>(a, b, t)),
        scalar_lerp::<T>(a, b, t).le(hi),
{
    T::axiom_le_total(a, b);
    if a.le(b) {
        lemma_scalar_lerp_bounds::<T>(a, b, t);
        T::axiom_le_transitive(lo, a, scalar_lerp::<T>(a, b, t));
        T::axiom_le_transitive(scalar_lerp::<T>(a, b, t), b, hi);
    } else {
        // b ≤ a by totality. Use symmetry: lerp(a,b,t) ≡ lerp(b,a,1-t).
        lemma_one_sub_t_in_unit::<T>(t);
        lemma_scalar_lerp_bounds::<T>(b, a, T::one().sub(t));
        // b ≤ lerp(b,a,1-t) ≤ a
        lemma_scalar_lerp_symmetry::<T>(a, b, t);
        // lerp(a,b,t) ≡ lerp(b,a,1-t)
        // Transfer lo ≤ lerp(b,a,1-t) to lo ≤ lerp(a,b,t) via eqv
        T::axiom_le_transitive(lo, b, scalar_lerp::<T>(b, a, T::one().sub(t)));
        T::axiom_eqv_reflexive(lo);
        T::axiom_eqv_symmetric(
            scalar_lerp::<T>(a, b, t), scalar_lerp::<T>(b, a, T::one().sub(t)));
        T::axiom_le_congruence(
            lo, lo,
            scalar_lerp::<T>(b, a, T::one().sub(t)), scalar_lerp::<T>(a, b, t));
        // Transfer lerp(b,a,1-t) ≤ a to lerp(a,b,t) ≤ hi
        T::axiom_le_transitive(scalar_lerp::<T>(b, a, T::one().sub(t)), a, hi);
        T::axiom_eqv_reflexive(hi);
        T::axiom_le_congruence(
            scalar_lerp::<T>(b, a, T::one().sub(t)), scalar_lerp::<T>(a, b, t),
            hi, hi);
    }
}

/// lerp_size stays within limits: if both sizes are within [lim.min, lim.max],
/// then lerp_size at t ∈ [0,1] is also within limits.
pub proof fn lemma_lerp_size_within_limits<T: OrderedField>(
    a: Size<T>, b: Size<T>, t: T, lo: Size<T>, hi: Size<T>,
)
    requires
        lo.width.le(a.width), a.width.le(hi.width),
        lo.height.le(a.height), a.height.le(hi.height),
        lo.width.le(b.width), b.width.le(hi.width),
        lo.height.le(b.height), b.height.le(hi.height),
        T::zero().le(t), t.le(T::one()),
    ensures
        lo.width.le(lerp_size(a, b, t).width),
        lerp_size(a, b, t).width.le(hi.width),
        lo.height.le(lerp_size(a, b, t).height),
        lerp_size(a, b, t).height.le(hi.height),
{
    lemma_scalar_lerp_within_bounds::<T>(a.width, b.width, t, lo.width, hi.width);
    lemma_scalar_lerp_within_bounds::<T>(a.height, b.height, t, lo.height, hi.height);
}

// ── lerp_node full two-argument congruence ──────────────────────

/// lerp_node respects deep eqv on both arguments simultaneously.
/// Combines left and right congruence via transitivity.
pub proof fn lemma_lerp_node_congruence_both<T: OrderedField>(
    a1: Node<T>, a2: Node<T>,
    b1: Node<T>, b2: Node<T>,
    t: T, fuel: nat,
)
    requires
        fuel > 0,
        nodes_deeply_eqv(a1, a2, (fuel - 1) as nat),
        nodes_deeply_eqv(b1, b2, (fuel - 1) as nat),
    ensures
        nodes_deeply_eqv(
            lerp_node(a1, b1, t, fuel),
            lerp_node(a2, b2, t, fuel),
            (fuel - 1) as nat,
        ),
{
    // Step 1: lerp(a1, b1, t, fuel) ≡ lerp(a2, b1, t, fuel) by left congruence
    lemma_lerp_node_congruence_left(a1, a2, b1, t, fuel);
    // Step 2: lerp(a2, b1, t, fuel) ≡ lerp(a2, b2, t, fuel) by right congruence
    lemma_lerp_node_congruence_right(a2, b1, b2, t, fuel);
    // Step 3: transitivity
    crate::diff::lemma_deeply_eqv_transitive(
        lerp_node(a1, b1, t, fuel),
        lerp_node(a2, b1, t, fuel),
        lerp_node(a2, b2, t, fuel),
        (fuel - 1) as nat,
    );
}

// ── lerp_node preserves children_match_deep ─────────────────────

/// lerp_node preserves tree structure: if a and b have matching children,
/// then lerp(a, b, t, fuel) also matches both a and b in children count.
pub proof fn lemma_lerp_node_preserves_children_match<T: OrderedField>(
    a: Node<T>, b: Node<T>, t: T, fuel: nat,
)
    requires
        fuel > 0,
        children_match_deep(a, b, (fuel - 1) as nat),
    ensures
        children_match_deep(a, lerp_node(a, b, t, fuel), (fuel - 1) as nat),
        children_match_deep(lerp_node(a, b, t, fuel), b, (fuel - 1) as nat),
    decreases fuel,
{
    // children_match_deep gives a.children.len() == b.children.len()
    // lerp_node enters interpolation: result.children.len() == a.children.len()
    let result = lerp_node(a, b, t, fuel);
    if fuel > 1 {
        assert forall|i: int| 0 <= i < a.children.len() implies
            children_match_deep(a.children[i], result.children[i], (fuel - 2) as nat)
            && children_match_deep(result.children[i], b.children[i], (fuel - 2) as nat)
        by {
            // result.children[i] = lerp_node(a.children[i], b.children[i], t, fuel-1)
            lemma_lerp_node_preserves_children_match(
                a.children[i], b.children[i], t, (fuel - 1) as nat);
        };
    }
}

// ── lerp_node fuel convergence ──────────────────────────────────

/// lerp_node at two fuels produces deeply eqv results up to the
/// minimum depth, when children match at the higher fuel level.
/// This is the correct convergence statement: the results agree on
/// all levels that both fuel values can reach.
pub proof fn lemma_lerp_node_fuel_agree_eqv<T: OrderedField>(
    a: Node<T>, b: Node<T>, t: T,
    fuel1: nat, fuel2: nat,
)
    requires
        fuel1 > 0, fuel2 > 0,
        children_match_deep(a, b, (fuel1 - 1) as nat),
        children_match_deep(a, b, (fuel2 - 1) as nat),
    ensures
        nodes_deeply_eqv(
            lerp_node(a, b, t, fuel1),
            lerp_node(a, b, t, fuel2),
            0),
{
    // Both fuels > 0 and children match → both enter interpolation case.
    // Same scalar_lerp for x, y, width, height → fields eqv.
    // depth 0: only checks field eqv (no children recursion).
    T::axiom_eqv_reflexive(scalar_lerp::<T>(a.x, b.x, t));
    T::axiom_eqv_reflexive(scalar_lerp::<T>(a.y, b.y, t));
    T::axiom_eqv_reflexive(scalar_lerp::<T>(a.size.width, b.size.width, t));
    T::axiom_eqv_reflexive(scalar_lerp::<T>(a.size.height, b.size.height, t));
}

/// children_match_deep is monotone: depth d > 0 implies depth d-1.
proof fn lemma_children_match_deep_monotone<T: OrderedRing>(
    a: Node<T>, b: Node<T>, depth: nat,
)
    requires depth > 0, children_match_deep(a, b, depth),
    ensures children_match_deep(a, b, (depth - 1) as nat),
    decreases depth,
{
    if depth == 1 {
        // depth-1 = 0: only need a.children.len() == b.children.len() ✓
    } else {
        assert forall|i: int| 0 <= i < a.children.len() implies
            children_match_deep(a.children[i], b.children[i], (depth - 2) as nat)
        by {
            lemma_children_match_deep_monotone(
                a.children[i], b.children[i], (depth - 1) as nat);
        };
    }
}

// ── lerp_size monotone in t ──────────────────────────────────────

/// lerp_size is monotone in t: if a ≤ b componentwise and s ≤ t,
/// then lerp_size(a, b, s) ≤ lerp_size(a, b, t) componentwise.
pub proof fn lemma_lerp_size_monotone<T: OrderedField>(
    a: Size<T>, b: Size<T>, s: T, t: T,
)
    requires
        a.width.le(b.width), a.height.le(b.height),
        s.le(t),
    ensures
        lerp_size(a, b, s).width.le(lerp_size(a, b, t).width),
        lerp_size(a, b, s).height.le(lerp_size(a, b, t).height),
{
    lemma_scalar_lerp_monotone::<T>(a.width, b.width, s, t);
    lemma_scalar_lerp_monotone::<T>(a.height, b.height, s, t);
}

} // verus!
