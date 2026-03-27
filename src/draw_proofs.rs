use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::min_max::{min, max};
use crate::size::Size;
use crate::limits::Limits;
use crate::node::Node;
use crate::draw::*;
use crate::diff::nodes_deeply_eqv;
use crate::widget::*;
use crate::vulkan_bridge::{draw_command_valid, all_draws_valid};

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

// ── Draw command validity ────────────────────────────────────────────

/// All nodes in a tree have non-negative sizes.
pub open spec fn all_sizes_nonneg<T: OrderedRing>(node: Node<T>, fuel: nat) -> bool
    decreases fuel,
{
    node.size.is_nonneg()
    && (fuel > 0 ==> forall|i: int| 0 <= i < node.children.len() ==>
        all_sizes_nonneg(node.children[i], (fuel - 1) as nat))
}

/// If a node has nonneg size, its self-draw is valid.
proof fn lemma_nonneg_implies_self_draw_valid<T: OrderedRing>(
    node: Node<T>, offset_x: T, offset_y: T, depth: nat,
)
    requires node.size.is_nonneg(),
    ensures
        draw_command_valid(DrawCommand {
            x: offset_x.add(node.x), y: offset_y.add(node.y),
            width: node.size.width, height: node.size.height, depth,
        }),
{
}

/// If all nodes in a tree have nonneg sizes, flatten produces valid draws.
pub proof fn lemma_flatten_all_valid<T: OrderedRing>(
    node: Node<T>, offset_x: T, offset_y: T, depth: nat, fuel: nat,
)
    requires all_sizes_nonneg(node, fuel),
    ensures all_draws_valid(flatten_node_to_draws(node, offset_x, offset_y, depth, fuel)),
    decreases fuel, 0nat,
{
    let draws = flatten_node_to_draws(node, offset_x, offset_y, depth, fuel);
    if fuel == 0 {
        // Single draw: node.size.is_nonneg() → draw_command_valid
        assert forall|i: int| 0 <= i < draws.len()
            implies draw_command_valid(#[trigger] draws[i])
        by {
            assert(i == 0);
        };
    } else {
        let abs_x = offset_x.add(node.x);
        let abs_y = offset_y.add(node.y);
        // Self draw is valid
        // Children draws are valid by IH
        lemma_flatten_children_all_valid(
            node.children, abs_x, abs_y, depth + 1, (fuel - 1) as nat, 0);
        let child_draws = flatten_children_to_draws(
            node.children, abs_x, abs_y, depth + 1, (fuel - 1) as nat, 0);
        assert forall|i: int| 0 <= i < draws.len()
            implies draw_command_valid(#[trigger] draws[i])
        by {
            if i == 0 {
                // Self draw
            } else {
                // Child draw: draws[i] == child_draws[i-1]
                assert(draws[i] == child_draws[i - 1]);
            }
        };
    }
}

/// Children flatten all valid.
proof fn lemma_flatten_children_all_valid<T: OrderedRing>(
    children: Seq<Node<T>>,
    parent_abs_x: T, parent_abs_y: T,
    start_depth: nat, fuel: nat, from: nat,
)
    requires
        forall|i: int| 0 <= i < children.len() ==>
            all_sizes_nonneg(children[i], fuel),
    ensures
        all_draws_valid(
            flatten_children_to_draws(children, parent_abs_x, parent_abs_y,
                start_depth, fuel, from)),
    decreases fuel, children.len() - from,
{
    if from >= children.len() {
    } else {
        lemma_flatten_all_valid(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let first = flatten_node_to_draws(
            children[from as int], parent_abs_x, parent_abs_y, start_depth, fuel);
        let next_depth = start_depth + first.len();
        lemma_flatten_children_all_valid(
            children, parent_abs_x, parent_abs_y, next_depth, fuel, from + 1);
        let rest = flatten_children_to_draws(
            children, parent_abs_x, parent_abs_y, next_depth, fuel, from + 1);
        let full = flatten_children_to_draws(
            children, parent_abs_x, parent_abs_y, start_depth, fuel, from);
        assert forall|i: int| 0 <= i < full.len()
            implies draw_command_valid(#[trigger] full[i])
        by {
            if i < first.len() as int {
                assert(full[i] == first[i]);
            } else {
                assert(full[i] == rest[i - first.len() as int]);
            }
        };
    }
}

/// Resolve with wf limits produces nonneg sizes.
pub proof fn lemma_resolve_nonneg<T: OrderedRing>(
    limits: Limits<T>, size: Size<T>,
)
    requires limits.wf(),
    ensures limits.resolve(size).is_nonneg(),
{
    // resolve.width = clamp(size.width, min.width, max.width) = max(min.width, min(size.width, max.width))
    // limits.wf() → min.width ≥ 0
    // max(min.width, _) ≥ min.width ≥ 0
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        limits.min.width, min::<T>(size.width, limits.max.width));
    T::axiom_le_transitive(
        T::zero(), limits.min.width,
        max::<T>(limits.min.width, min::<T>(size.width, limits.max.width)));
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        limits.min.height, min::<T>(size.height, limits.max.height));
    T::axiom_le_transitive(
        T::zero(), limits.min.height,
        max::<T>(limits.min.height, min::<T>(size.height, limits.max.height)));
}

/// Resolve nonneg from min nonneg (weaker precondition than limits.wf()).
/// Since resolve = max(min, min(val, max)), and min >= 0 implies max(min, _) >= 0.
proof fn lemma_resolve_nonneg_from_min<T: OrderedRing>(
    limits: Limits<T>, size: Size<T>,
)
    requires limits.min.is_nonneg(),
    ensures limits.resolve(size).is_nonneg(),
{
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        limits.min.width, min::<T>(size.width, limits.max.width));
    T::axiom_le_transitive(
        T::zero(), limits.min.width,
        max::<T>(limits.min.width, min::<T>(size.width, limits.max.width)));
    verus_algebra::min_max::lemma_max_ge_left::<T>(
        limits.min.height, min::<T>(size.height, limits.max.height));
    T::axiom_le_transitive(
        T::zero(), limits.min.height,
        max::<T>(limits.min.height, min::<T>(size.height, limits.max.height)));
}

/// all_sizes_nonneg is insensitive to x/y: nodes with the same size and children
/// have the same all_sizes_nonneg value.
proof fn lemma_all_sizes_nonneg_xy_irrelevant<T: OrderedRing>(
    n1: Node<T>, n2: Node<T>, fuel: nat,
)
    requires
        n1.size == n2.size,
        n1.children =~= n2.children,
    ensures
        all_sizes_nonneg(n1, fuel) == all_sizes_nonneg(n2, fuel),
{
}

/// THE KEY THEOREM: every node in a layout tree has non-negative sizes.
///
/// Induction on layout fuel. The check_fuel parameter is independent — we prove
/// the property at any depth of checking.
pub proof fn lemma_layout_widget_all_sizes_nonneg<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
    check_fuel: nat,
)
    requires limits.min.is_nonneg(),
    ensures all_sizes_nonneg(layout_widget(limits, widget, fuel), check_fuel),
    decreases fuel, check_fuel,
{
    let node = layout_widget(limits, widget, fuel);
    if fuel == 0 {
        // layout returns zero node — zero.le(zero) by reflexive
        T::axiom_le_reflexive(T::zero());
        if check_fuel > 0 {
            // No children, forall is vacuous
        }
    } else if check_fuel == 0 {
        // Just need node.size.is_nonneg()
        lemma_layout_root_nonneg(limits, widget, fuel);
    } else {
        // Need root nonneg + all children nonneg at check_fuel-1
        lemma_layout_root_nonneg(limits, widget, fuel);
        lemma_layout_children_all_nonneg(limits, widget, fuel, check_fuel);
    }
}

/// Root size of any layout is nonneg when limits.min is nonneg.
proof fn lemma_layout_root_nonneg<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures layout_widget(limits, widget, fuel).size.is_nonneg(),
{
    // All variants produce root size via limits.resolve(something)
    lemma_resolve_nonneg_from_min(limits, layout_widget(limits, widget, fuel).size);
    // Need to show layout_widget(...).size == limits.resolve(X) for some X
    // Actually, resolve(resolve(x)) == resolve(x) since resolve clamps to [min,max]
    // But simpler: lemma_layout_widget_respects_limits gives min <= size <= max
    // and min >= 0, so size >= 0.
    crate::layout::bounds_proofs::lemma_layout_widget_respects_limits(limits, widget, fuel);
    T::axiom_le_transitive(T::zero(), limits.min.width, layout_widget(limits, widget, fuel).size.width);
    T::axiom_le_transitive(T::zero(), limits.min.height, layout_widget(limits, widget, fuel).size.height);
}

/// Children of a layout all have nonneg sizes (recursively).
proof fn lemma_layout_children_all_nonneg<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
    check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
    ensures ({
        let node = layout_widget(limits, widget, fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel,
{
    match widget {
        Widget::Leaf(_) => {
            // Leaf has no children (empty Seq)
        },
        Widget::Wrapper(wrapper) => {
            lemma_wrapper_children_nonneg(limits, wrapper, fuel, check_fuel);
        },
        Widget::Container(container) => {
            lemma_container_children_nonneg(limits, container, fuel, check_fuel);
        },
    }
}

/// Wrapper children all_sizes_nonneg.
proof fn lemma_wrapper_children_nonneg<T: OrderedField>(
    limits: Limits<T>,
    wrapper: WrapperWidget<T>,
    fuel: nat,
    check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
    ensures ({
        let node = layout_widget(limits, Widget::Wrapper(wrapper), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel,
{
    match wrapper {
        WrapperWidget::Conditional { visible, child } => {
            if visible {
                // Output children = child_node.children where child_node = layout_widget(limits, *child, fuel-1)
                // Need all_sizes_nonneg for each at check_fuel-1
                // By IH at (fuel-1, check_fuel): all_sizes_nonneg(child_node, check_fuel)
                // which gives forall|i| all_sizes_nonneg(child_node.children[i], check_fuel-1)
                lemma_layout_widget_all_sizes_nonneg(limits, *child, (fuel - 1) as nat, check_fuel);
                let child_node = layout_widget(limits, *child, (fuel - 1) as nat);
                let node = layout_widget(limits, Widget::Wrapper(wrapper), fuel);
                assert(node.children =~= child_node.children);
            } else {
                // No children
            }
        },
        WrapperWidget::Margin { margin, child } => {
            let inner = limits.shrink(margin.horizontal(), margin.vertical());
            // inner.min == limits.min, so inner.min.is_nonneg()
            lemma_layout_widget_all_sizes_nonneg(inner, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
        WrapperWidget::SizedBox { inner_limits, child } => {
            let effective = limits.intersect(inner_limits);
            // intersect.min = max(limits.min, inner_limits.min) >= limits.min >= 0
            verus_algebra::min_max::lemma_max_ge_left::<T>(limits.min.width, inner_limits.min.width);
            T::axiom_le_transitive(T::zero(), limits.min.width,
                max::<T>(limits.min.width, inner_limits.min.width));
            verus_algebra::min_max::lemma_max_ge_left::<T>(limits.min.height, inner_limits.min.height);
            T::axiom_le_transitive(T::zero(), limits.min.height,
                max::<T>(limits.min.height, inner_limits.min.height));
            lemma_layout_widget_all_sizes_nonneg(effective, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
        WrapperWidget::AspectRatio { ratio, child } => {
            // Inner limits have min = limits.min which is nonneg
            let w1 = limits.max.width;
            let h1 = w1.div(ratio);
            if h1.le(limits.max.height) {
                let eff = Limits { min: limits.min, max: Size::new(w1, h1) };
                lemma_layout_widget_all_sizes_nonneg(eff, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
            } else {
                let h2 = limits.max.height;
                let w2 = h2.mul(ratio);
                let eff = Limits { min: limits.min, max: Size::new(w2, h2) };
                lemma_layout_widget_all_sizes_nonneg(eff, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
            }
        },
        WrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child } => {
            // child_limits = Limits { min: zero, max: viewport }
            // min = zero which is nonneg
            let child_limits = Limits {
                min: Size::zero_size(),
                max: viewport,
            };
            T::axiom_le_reflexive(T::zero());
            lemma_layout_widget_all_sizes_nonneg(child_limits, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
    }
}

/// Container children all_sizes_nonneg.
proof fn lemma_container_children_nonneg<T: OrderedField>(
    limits: Limits<T>,
    container: ContainerWidget<T>,
    fuel: nat,
    check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
    ensures ({
        let node = layout_widget(limits, Widget::Container(container), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel,
{
    // For ALL container variants, children in the output (after merge_layout or direct construction)
    // have size = child_nodes[i].size and children = child_nodes[i].children, where
    // child_nodes[i] = layout_widget(inner_limits, widget_i, fuel-1).
    // By IH: all_sizes_nonneg(layout_widget(inner, widget_i, fuel-1), check_fuel-1)
    // Since merged child has same size and children: all_sizes_nonneg(merged_child, check_fuel-1)
    match container {
        ContainerWidget::Column { padding, spacing, alignment, children }
        | ContainerWidget::Row { padding, spacing, alignment, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            assert forall|i: int| 0 <= i < children.len() implies
                all_sizes_nonneg(layout_widget(inner, children[i], (fuel - 1) as nat), (check_fuel - 1) as nat)
            by {
                lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
        },
        ContainerWidget::Stack { padding, h_align, v_align, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            assert forall|i: int| 0 <= i < children.len() implies
                all_sizes_nonneg(layout_widget(inner, children[i], (fuel - 1) as nat), (check_fuel - 1) as nat)
            by {
                lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
        },
        ContainerWidget::Wrap { padding, h_spacing, v_spacing, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            assert forall|i: int| 0 <= i < children.len() implies
                all_sizes_nonneg(layout_widget(inner, children[i], (fuel - 1) as nat), (check_fuel - 1) as nat)
            by {
                lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
        },
        ContainerWidget::Flex { padding, spacing, alignment, direction, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            // Flex children are laid out with per-child limits derived from inner
            // All have min nonneg since inner.min = limits.min
            assert forall|i: int| 0 <= i < children.len() implies
                all_sizes_nonneg(
                    layout_widget(
                        flex_child_limits(inner, children, direction.axis(), i),
                        children[i].child,
                        (fuel - 1) as nat),
                    (check_fuel - 1) as nat)
            by {
                // flex_child_limits produces limits with min from inner (nonneg)
                lemma_flex_child_limits_min_nonneg(inner, children, direction.axis(), i);
                lemma_layout_widget_all_sizes_nonneg(
                    flex_child_limits(inner, children, direction.axis(), i),
                    children[i].child,
                    (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
        },
        ...
    }
}
```

Hmm, this is getting complex. Let me think about Flex. The flex child layout uses `flex_linear_widget_child_nodes` which is different from `widget_child_nodes`. Let me check how flex children are laid out.
</thinking>

Let me check how flex and grid children are laid out:

<function_calls>
<invoke name="mcp__verus__lookup_source">
<parameter name="name">flex_linear_widget_child_nodes
/// This proves the root node's dimensions are non-negative.
pub proof fn lemma_layout_root_draw_valid<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
    draw_fuel: nat,
)
    requires limits.wf(), fuel > 0,
    ensures ({
        let draws = flatten_node_to_draws(
            layout_widget(limits, widget, fuel),
            T::zero(), T::zero(), 0, draw_fuel);
        draws.len() > 0 && draw_command_valid(draws[0])
    }),
{
    crate::layout::bounds_proofs::lemma_layout_widget_respects_limits(limits, widget, fuel);
    let node = layout_widget(limits, widget, fuel);
    T::axiom_le_transitive(T::zero(), limits.min.width, node.size.width);
    T::axiom_le_transitive(T::zero(), limits.min.height, node.size.height);
    lemma_flatten_first_depth(node, T::zero(), T::zero(), 0, draw_fuel);
}

/// Full draw validity: if all nodes in a layout tree have nonneg sizes,
/// then all draw commands from flattening are valid.
/// Combined with lemma_flatten_all_valid, this gives the end-to-end guarantee.
///
/// Usage: prove all_sizes_nonneg for a specific widget tree
/// (e.g., by strengthening lemma_layout_widget_respects_limits to be recursive),
/// then call this lemma.
pub proof fn lemma_layout_all_draws_valid_from_nonneg<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
    draw_fuel: nat,
)
    requires
        limits.wf(), fuel > 0,
        all_sizes_nonneg(layout_widget(limits, widget, fuel), draw_fuel),
    ensures
        all_draws_valid(
            flatten_node_to_draws(
                layout_widget(limits, widget, fuel),
                T::zero(), T::zero(), 0, draw_fuel)),
{
    lemma_flatten_all_valid(
        layout_widget(limits, widget, fuel),
        T::zero(), T::zero(), 0, draw_fuel);
}

} // verus!
