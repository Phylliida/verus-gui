use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::size::Size;
use crate::node::Node;
use crate::draw::*;
use crate::diff::nodes_deeply_eqv;

verus! {

// ── Count preservation ────────────────────────────────────────────────

/// Flattening a node produces exactly node_count draw commands.
pub proof fn lemma_flatten_preserves_count<T: OrderedRing>(
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    ensures
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel).len()
            == node_count::<T>(node, fuel),
    decreases fuel, 0nat,
{
    if fuel == 0 {
        // Base case: single draw command, node_count = 1
    } else {
        let abs_x = offset_x.add(node.x);
        let abs_y = offset_y.add(node.y);
        lemma_flatten_children_preserves_count(
            node.children, abs_x, abs_y, depth + 1, (fuel - 1) as nat, 0);
    }
}

/// Flattening children produces children_node_count draw commands.
pub proof fn lemma_flatten_children_preserves_count<T: OrderedRing>(
    children: Seq<Node<T>>,
    parent_abs_x: T,
    parent_abs_y: T,
    start_depth: nat,
    fuel: nat,
    from: nat,
)
    ensures
        flatten_children_to_draws(children, parent_abs_x, parent_abs_y, start_depth, fuel, from).len()
            == children_node_count::<T>(children, fuel, from),
    decreases fuel, children.len() - from,
{
    if from >= children.len() {
        // Empty: both are 0
    } else {
        lemma_flatten_preserves_count(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let first_draws = flatten_node_to_draws(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let next_depth = start_depth + first_draws.len();
        lemma_flatten_children_preserves_count(
            children, parent_abs_x, parent_abs_y, next_depth, fuel, from + 1);
    }
}

// ── Depth ordering ────────────────────────────────────────────────────

/// The first draw command in a flattened node has the given depth.
pub proof fn lemma_flatten_first_depth<T: OrderedRing>(
    node: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    ensures
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel).len() > 0,
        flatten_node_to_draws(node, offset_x, offset_y, depth, fuel)[0].depth == depth,
{
    // Both fuel==0 and fuel>0 cases produce a first element with the given depth
}

// ── Structural identity ──────────────────────────────────────────────

/// If two nodes are structurally identical, their draw command
/// sequences are identical.
pub proof fn lemma_same_node_same_draws<T: OrderedRing>(
    node1: Node<T>,
    node2: Node<T>,
    offset_x: T,
    offset_y: T,
    depth: nat,
    fuel: nat,
)
    requires
        node1 === node2,
    ensures
        flatten_node_to_draws(node1, offset_x, offset_y, depth, fuel)
            === flatten_node_to_draws(node2, offset_x, offset_y, depth, fuel),
{
    // Trivially true: node1 === node2 implies identical function application
}

// ── Draw command eqv ────────────────────────────────────────────────

/// Two draw commands are eqv: coordinates and dimensions are eqv, depth equal.
pub open spec fn draw_cmd_eqv<T: OrderedRing>(
    a: DrawCommand<T>, b: DrawCommand<T>,
) -> bool {
    a.x.eqv(b.x) && a.y.eqv(b.y)
    && a.width.eqv(b.width) && a.height.eqv(b.height)
    && a.depth == b.depth
}

/// Two draw command sequences are element-wise eqv.
pub open spec fn draws_eqv<T: OrderedRing>(
    a: Seq<DrawCommand<T>>, b: Seq<DrawCommand<T>>,
) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==> draw_cmd_eqv(a[i], b[i])
}

// ── Draw congruence ─────────────────────────────────────────────────

/// add_congruence helper: a1+b1 eqv a2+b2 when a1 eqv a2 and b1 eqv b2.
proof fn lemma_add_congruence<T: OrderedField>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2),
    ensures a1.add(b1).eqv(a2.add(b2)),
{
    T::axiom_add_congruence_left(a1, a2, b1);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(a2, b1, b2);
    T::axiom_eqv_transitive(a1.add(b1), a2.add(b1), a2.add(b2));
}

/// Flattening deeply eqv nodes with eqv offsets produces eqv draw commands.
pub proof fn lemma_flatten_congruence<T: OrderedField>(
    n1: Node<T>, n2: Node<T>,
    ox1: T, ox2: T, oy1: T, oy2: T,
    depth: nat, fuel: nat,
)
    requires
        nodes_deeply_eqv(n1, n2, fuel),
        ox1.eqv(ox2), oy1.eqv(oy2),
    ensures
        draws_eqv(
            flatten_node_to_draws(n1, ox1, oy1, depth, fuel),
            flatten_node_to_draws(n2, ox2, oy2, depth, fuel),
        ),
    decreases fuel, 0nat,
{
    // Self draw command eqv: abs_x = offset_x + node.x, etc.
    lemma_add_congruence(ox1, ox2, n1.x, n2.x);
    lemma_add_congruence(oy1, oy2, n1.y, n2.y);
    let ax1 = ox1.add(n1.x);
    let ax2 = ox2.add(n2.x);
    let ay1 = oy1.add(n1.y);
    let ay2 = oy2.add(n2.y);

    if fuel == 0 {
        // Single draw command
        let d1 = flatten_node_to_draws(n1, ox1, oy1, depth, 0);
        let d2 = flatten_node_to_draws(n2, ox2, oy2, depth, 0);
        assert(d1.len() == 1 && d2.len() == 1);
        assert(draw_cmd_eqv(d1[0], d2[0]));
    } else {
        // Self command + children
        lemma_flatten_children_congruence(
            n1.children, n2.children,
            ax1, ax2, ay1, ay2,
            depth + 1, (fuel - 1) as nat, 0);
        let child_draws1 = flatten_children_to_draws(
            n1.children, ax1, ay1, depth + 1, (fuel - 1) as nat, 0);
        let child_draws2 = flatten_children_to_draws(
            n2.children, ax2, ay2, depth + 1, (fuel - 1) as nat, 0);
        // Full sequence: [self_draw] ++ child_draws
        let d1 = flatten_node_to_draws(n1, ox1, oy1, depth, fuel);
        let d2 = flatten_node_to_draws(n2, ox2, oy2, depth, fuel);
        // d1[0] and d2[0] are the self draw commands (eqv)
        assert(draw_cmd_eqv(d1[0], d2[0]));
        // d1[1..] and d2[1..] are child draws (eqv by helper)
        assert forall|i: int| 0 <= i < d1.len() implies draw_cmd_eqv(d1[i], d2[i])
        by {
            if i == 0 {
            } else {
                assert(d1[i] == child_draws1[i - 1]);
                assert(d2[i] == child_draws2[i - 1]);
            }
        };
    }
}

/// Children flattening congruence.
proof fn lemma_flatten_children_congruence<T: OrderedField>(
    ch1: Seq<Node<T>>, ch2: Seq<Node<T>>,
    px1: T, px2: T, py1: T, py2: T,
    start_depth: nat, fuel: nat, from: nat,
)
    requires
        ch1.len() == ch2.len(),
        forall|i: int| 0 <= i < ch1.len() ==>
            nodes_deeply_eqv(ch1[i], ch2[i], fuel),
        px1.eqv(px2), py1.eqv(py2),
    ensures
        draws_eqv(
            flatten_children_to_draws(ch1, px1, py1, start_depth, fuel, from),
            flatten_children_to_draws(ch2, px2, py2, start_depth, fuel, from),
        ),
    decreases fuel, ch1.len() - from,
{
    if from >= ch1.len() {
        // Both empty
    } else {
        // Flatten this child
        lemma_flatten_congruence(ch1[from as int], ch2[from as int],
            px1, px2, py1, py2, start_depth, fuel);
        let first1 = flatten_node_to_draws(ch1[from as int], px1, py1, start_depth, fuel);
        let first2 = flatten_node_to_draws(ch2[from as int], px2, py2, start_depth, fuel);
        // Count preservation to establish length equality
        lemma_flatten_preserves_count(ch1[from as int], px1, py1, start_depth, fuel);
        lemma_flatten_preserves_count(ch2[from as int], px2, py2, start_depth, fuel);
        // first1.len() == first2.len() because node_count depends only on children count
        // which is the same for deeply eqv nodes
        lemma_node_count_congruence::<T>(ch1[from as int], ch2[from as int], fuel);
        let next_depth = start_depth + first1.len();
        // Recurse for remaining children
        lemma_flatten_children_congruence(ch1, ch2, px1, px2, py1, py2,
            next_depth, fuel, from + 1);
        let rest1 = flatten_children_to_draws(ch1, px1, py1, next_depth, fuel, from + 1);
        let rest2 = flatten_children_to_draws(ch2, px2, py2, next_depth, fuel, from + 1);
        // Concatenation preserves eqv
        let full1 = flatten_children_to_draws(ch1, px1, py1, start_depth, fuel, from);
        let full2 = flatten_children_to_draws(ch2, px2, py2, start_depth, fuel, from);
        assert forall|i: int| 0 <= i < full1.len() implies draw_cmd_eqv(full1[i], full2[i])
        by {
            if i < first1.len() as int {
                assert(full1[i] == first1[i]);
                assert(full2[i] == first2[i]);
            } else {
                assert(full1[i] == rest1[i - first1.len() as int]);
                assert(full2[i] == rest2[i - first2.len() as int]);
            }
        };
    }
}

/// node_count is the same for deeply eqv nodes.
proof fn lemma_node_count_congruence<T: OrderedRing>(
    n1: Node<T>, n2: Node<T>, fuel: nat,
)
    requires nodes_deeply_eqv(n1, n2, fuel),
    ensures node_count::<T>(n1, fuel) == node_count::<T>(n2, fuel),
    decreases fuel, 0nat,
{
    if fuel == 0 {
    } else {
        lemma_children_node_count_congruence::<T>(
            n1.children, n2.children, (fuel - 1) as nat, 0);
    }
}

/// children_node_count is the same for eqv children.
proof fn lemma_children_node_count_congruence<T: OrderedRing>(
    ch1: Seq<Node<T>>, ch2: Seq<Node<T>>,
    fuel: nat, from: nat,
)
    requires
        ch1.len() == ch2.len(),
        forall|i: int| 0 <= i < ch1.len() ==>
            nodes_deeply_eqv(ch1[i], ch2[i], fuel),
    ensures
        children_node_count::<T>(ch1, fuel, from)
            == children_node_count::<T>(ch2, fuel, from),
    decreases fuel, ch1.len() - from,
{
    if from >= ch1.len() {
    } else {
        lemma_node_count_congruence::<T>(ch1[from as int], ch2[from as int], fuel);
        lemma_children_node_count_congruence::<T>(ch1, ch2, fuel, from + 1);
    }
}

} // verus!
