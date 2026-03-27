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
/// Proves all_sizes_nonneg(layout_widget(limits, widget, fuel), check_fuel) for ANY
/// check_fuel, given only limits.min.is_nonneg(). This weak precondition is preserved
/// by all inner limit constructions (shrink, intersect, zero min, same min).
///
/// Induction on (fuel, check_fuel) with 3-tuple decreases for mutual recursion:
/// - Main function: decreases (fuel, check_fuel, 3)
/// - Wrapper helper: decreases (fuel, check_fuel, 2)
/// - Container helper: decreases (fuel, check_fuel, 2)
/// - Flex child helper: decreases (fuel, check_fuel, 1)
pub proof fn lemma_layout_widget_all_sizes_nonneg<T: OrderedField>(
    limits: Limits<T>,
    widget: Widget<T>,
    fuel: nat,
    check_fuel: nat,
)
    requires limits.min.is_nonneg(),
    ensures all_sizes_nonneg(layout_widget(limits, widget, fuel), check_fuel),
    decreases fuel, check_fuel, 3nat,
{
    if fuel == 0 {
        T::axiom_le_reflexive(T::zero());
    } else if check_fuel == 0 {
        // all_sizes_nonneg(node, 0) = node.size.is_nonneg()
        // Root nonneg for leaf/wrapper: direct resolve call
        // Root nonneg for container: per-variant helper with reveal()
        lemma_root_size_nonneg(limits, widget, fuel);
    } else {
        // Root nonneg + children nonneg at check_fuel-1
        lemma_root_size_nonneg(limits, widget, fuel);
        match widget {
            Widget::Leaf(_) => { /* no children */ },
            Widget::Wrapper(wrapper) => {
                lemma_wrapper_children_nonneg(limits, wrapper, fuel, check_fuel);
            },
            Widget::Container(container) => {
                lemma_container_children_nonneg(limits, container, fuel, check_fuel);
            },
        }
    }
}

// ── Root size nonneg helpers ──────────────────────────────────────────
// Each variant's root is limits.resolve(X). resolve(X) >= min >= 0.
// Container layout functions are #[verifier::opaque] so need reveal().
// Split into per-variant helpers for rlimit.

/// Root size nonneg: leaf and wrapper variants (direct resolve).
proof fn lemma_root_size_nonneg<T: OrderedField>(
    limits: Limits<T>, widget: Widget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures layout_widget(limits, widget, fuel).size.is_nonneg(),
{
    match widget {
        Widget::Leaf(LeafWidget::Leaf { size }) =>
            { lemma_resolve_nonneg_from_min(limits, size); },
        Widget::Leaf(LeafWidget::TextInput { preferred_size, .. }) =>
            { lemma_resolve_nonneg_from_min(limits, preferred_size); },
        Widget::Wrapper(WrapperWidget::Conditional { visible, child }) => {
            if visible {
                lemma_resolve_nonneg_from_min(limits, layout_widget(limits, *child, (fuel - 1) as nat).size);
            } else {
                lemma_resolve_nonneg_from_min(limits, Size::zero_size());
            }
        },
        Widget::Wrapper(WrapperWidget::Margin { margin, child }) => {
            let cn = layout_widget(limits.shrink(margin.horizontal(), margin.vertical()), *child, (fuel - 1) as nat);
            lemma_resolve_nonneg_from_min(limits, Size::new(margin.horizontal().add(cn.size.width), margin.vertical().add(cn.size.height)));
        },
        Widget::Wrapper(WrapperWidget::SizedBox { inner_limits, child }) =>
            { lemma_resolve_nonneg_from_min(limits, layout_widget(limits.intersect(inner_limits), *child, (fuel - 1) as nat).size); },
        Widget::Wrapper(WrapperWidget::AspectRatio { ratio, child }) => {
            if limits.max.width.div(ratio).le(limits.max.height) {
                lemma_resolve_nonneg_from_min(limits, layout_widget(Limits { min: limits.min, max: Size::new(limits.max.width, limits.max.width.div(ratio)) }, *child, (fuel - 1) as nat).size);
            } else {
                lemma_resolve_nonneg_from_min(limits, layout_widget(Limits { min: limits.min, max: Size::new(limits.max.height.mul(ratio), limits.max.height) }, *child, (fuel - 1) as nat).size);
            }
        },
        Widget::Wrapper(WrapperWidget::ScrollView { viewport, .. }) =>
            { lemma_resolve_nonneg_from_min(limits, viewport); },
        Widget::Container(container) => {
            // Per-variant with reveals. Each gets own function for rlimit.
            lemma_container_root_nonneg_column(limits, container, fuel);
            lemma_container_root_nonneg_row(limits, container, fuel);
            lemma_container_root_nonneg_stack(limits, container, fuel);
            lemma_container_root_nonneg_wrap(limits, container, fuel);
            lemma_container_root_nonneg_flex(limits, container, fuel);
            lemma_container_root_nonneg_grid(limits, container, fuel);
            lemma_container_root_nonneg_abs(limits, container, fuel);
            lemma_container_root_nonneg_listview(limits, container, fuel);
        },
    }
}

proof fn lemma_container_root_nonneg_column<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Column ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Column { padding, spacing, alignment, children } = container {
        reveal(crate::layout::linear_layout);
        let cn = widget_child_nodes(limits.shrink(padding.horizontal(), padding.vertical()), children, (fuel - 1) as nat);
        let cs = Seq::new(cn.len(), |i: int| cn[i].size);
        let x = Size::from_axes(crate::layout::Axis::Vertical,
            padding.main_padding(crate::layout::Axis::Vertical).add(crate::layout::linear_content_main(cs, crate::layout::Axis::Vertical, spacing)),
            limits.max.cross_dim(crate::layout::Axis::Vertical));
        lemma_resolve_nonneg_from_min(limits, x);
    }
}

proof fn lemma_container_root_nonneg_row<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Row ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Row { padding, spacing, alignment, children } = container {
        reveal(crate::layout::linear_layout);
        let cn = widget_child_nodes(limits.shrink(padding.horizontal(), padding.vertical()), children, (fuel - 1) as nat);
        let cs = Seq::new(cn.len(), |i: int| cn[i].size);
        let x = Size::from_axes(crate::layout::Axis::Horizontal,
            padding.main_padding(crate::layout::Axis::Horizontal).add(crate::layout::linear_content_main(cs, crate::layout::Axis::Horizontal, spacing)),
            limits.max.cross_dim(crate::layout::Axis::Horizontal));
        lemma_resolve_nonneg_from_min(limits, x);
    }
}

proof fn lemma_container_root_nonneg_stack<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Stack ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Stack { padding, h_align, v_align, children } = container {
        reveal(crate::layout::stack::stack_layout);
        let cn = widget_child_nodes(limits.shrink(padding.horizontal(), padding.vertical()), children, (fuel - 1) as nat);
        let cs = Seq::new(cn.len(), |i: int| cn[i].size);
        let c = crate::layout::stack::stack_content_size(cs);
        lemma_resolve_nonneg_from_min(limits, Size::new(padding.horizontal().add(c.width), padding.vertical().add(c.height)));
    }
}

proof fn lemma_container_root_nonneg_wrap<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Wrap ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Wrap { padding, h_spacing, v_spacing, children } = container {
        reveal(crate::layout::wrap::wrap_layout);
        let cn = widget_child_nodes(limits.shrink(padding.horizontal(), padding.vertical()), children, (fuel - 1) as nat);
        let cs = Seq::new(cn.len(), |i: int| cn[i].size);
        let aw = limits.max.width.sub(padding.horizontal());
        let c = crate::layout::wrap::wrap_content_size(cs, h_spacing, v_spacing, aw);
        lemma_resolve_nonneg_from_min(limits, Size::new(padding.horizontal().add(c.width), padding.vertical().add(c.height)));
    }
}

proof fn lemma_container_root_nonneg_flex<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Flex ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Flex { direction, .. } = container {
        match direction.axis() {
            crate::layout::Axis::Vertical => { reveal(crate::layout::flex::flex_column_layout); },
            crate::layout::Axis::Horizontal => { reveal(crate::layout::flex::flex_row_layout); },
        }
        lemma_resolve_nonneg_from_min(limits, limits.max);
    }
}

proof fn lemma_container_root_nonneg_grid<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Grid ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Grid { padding, h_spacing, v_spacing, col_widths, row_heights, .. } = container {
        reveal(crate::layout::grid::grid_layout);
        lemma_resolve_nonneg_from_min(limits, Size::new(
            padding.horizontal().add(crate::layout::grid::grid_content_width(col_widths, h_spacing)),
            padding.vertical().add(crate::layout::grid::grid_content_height(row_heights, v_spacing))));
    }
}

proof fn lemma_container_root_nonneg_abs<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is Absolute ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::Absolute { padding, children } = container {
        reveal(crate::layout::absolute::absolute_layout);
        let inner = limits.shrink(padding.horizontal(), padding.vertical());
        let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
        let offsets = Seq::new(children.len(), |i: int| (children[i].x, children[i].y));
        // layout_absolute_body constructs child_data internally from cn + offsets
        let child_data = Seq::new(cn.len(), |i: int| (offsets[i].0, offsets[i].1, cn[i].size));
        let c = crate::layout::absolute::absolute_content_size(child_data);
        let x = Size::new(padding.horizontal().add(c.width), padding.vertical().add(c.height));
        // absolute_layout(limits, padding, child_data).size == limits.resolve(x)
        // (from absolute_layout definition, now revealed)
        lemma_resolve_nonneg_from_min(limits, x);
        // Help Z3 see the chain: layout_container → layout_absolute_body → merge_layout
        let layout_node = crate::layout::absolute::absolute_layout(limits, padding, child_data);
        assert(layout_absolute_body(limits, padding, cn, offsets).size == layout_node.size);
    }
}

proof fn lemma_container_root_nonneg_listview<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0,
    ensures container is ListView ==> layout_container(limits, container, fuel).size.is_nonneg(),
{
    if let ContainerWidget::ListView { viewport, .. } = container {
        reveal(crate::layout::listview::layout_listview_body);
        lemma_resolve_nonneg_from_min(limits, viewport);
    }
}

// ── Children nonneg helpers ──────────────────────────────────────────

/// Wrapper children all_sizes_nonneg.
proof fn lemma_wrapper_children_nonneg<T: OrderedField>(
    limits: Limits<T>, wrapper: WrapperWidget<T>, fuel: nat, check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
    ensures ({
        let node = layout_widget(limits, Widget::Wrapper(wrapper), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel, 2nat,
{
    match wrapper {
        WrapperWidget::Conditional { visible, child } => {
            if visible {
                lemma_layout_widget_all_sizes_nonneg(limits, *child, (fuel - 1) as nat, check_fuel);
                let child_node = layout_widget(limits, *child, (fuel - 1) as nat);
                let node = layout_widget(limits, Widget::Wrapper(wrapper), fuel);
                assert(node.children =~= child_node.children);
            }
        },
        WrapperWidget::Margin { margin, child } => {
            let inner = limits.shrink(margin.horizontal(), margin.vertical());
            lemma_layout_widget_all_sizes_nonneg(inner, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
        WrapperWidget::SizedBox { inner_limits, child } => {
            let effective = limits.intersect(inner_limits);
            verus_algebra::min_max::lemma_max_ge_left::<T>(limits.min.width, inner_limits.min.width);
            T::axiom_le_transitive(T::zero(), limits.min.width, max::<T>(limits.min.width, inner_limits.min.width));
            verus_algebra::min_max::lemma_max_ge_left::<T>(limits.min.height, inner_limits.min.height);
            T::axiom_le_transitive(T::zero(), limits.min.height, max::<T>(limits.min.height, inner_limits.min.height));
            lemma_layout_widget_all_sizes_nonneg(effective, *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
        WrapperWidget::AspectRatio { ratio, child } => {
            if limits.max.width.div(ratio).le(limits.max.height) {
                lemma_layout_widget_all_sizes_nonneg(
                    Limits { min: limits.min, max: Size::new(limits.max.width, limits.max.width.div(ratio)) },
                    *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
            } else {
                lemma_layout_widget_all_sizes_nonneg(
                    Limits { min: limits.min, max: Size::new(limits.max.height.mul(ratio), limits.max.height) },
                    *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
            }
        },
        WrapperWidget::ScrollView { viewport, scroll_x, scroll_y, child } => {
            T::axiom_le_reflexive(T::zero());
            lemma_layout_widget_all_sizes_nonneg(
                Limits { min: Size::zero_size(), max: viewport },
                *child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
    }
}

/// Container children all_sizes_nonneg — dispatches to split helpers.
proof fn lemma_container_children_nonneg<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat, check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
    ensures ({
        let node = layout_widget(limits, Widget::Container(container), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel, 2nat,
{
    match container {
        ContainerWidget::Column { .. } =>
            lemma_container_children_nonneg_shrink(limits, container, fuel, check_fuel),
        ContainerWidget::Row { .. } =>
            lemma_container_children_nonneg_shrink(limits, container, fuel, check_fuel),
        ContainerWidget::Stack { .. } =>
            lemma_container_children_nonneg_shrink(limits, container, fuel, check_fuel),
        ContainerWidget::Wrap { .. } =>
            lemma_container_children_nonneg_shrink(limits, container, fuel, check_fuel),
        ContainerWidget::Absolute { .. } =>
            lemma_container_children_nonneg_shrink(limits, container, fuel, check_fuel),
        _ =>
            lemma_container_children_nonneg_complex(limits, container, fuel, check_fuel),
    }
}

/// Container children nonneg — shrink-pattern (Column/Row/Stack/Wrap/Absolute).
proof fn lemma_container_children_nonneg_shrink<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat, check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
        container is Column || container is Row || container is Stack
        || container is Wrap || container is Absolute,
    ensures ({
        let node = layout_widget(limits, Widget::Container(container), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel, 1nat,
{
    match container {
        ContainerWidget::Column { padding, children, .. } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by { lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat); };
        },
        ContainerWidget::Row { padding, children, .. } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by { lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat); };
        },
        ContainerWidget::Stack { padding, children, .. } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by { lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat); };
        },
        ContainerWidget::Wrap { padding, children, .. } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by { lemma_layout_widget_all_sizes_nonneg(inner, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat); };
        },
        ContainerWidget::Absolute { padding, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = absolute_widget_child_nodes(inner, children, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by { lemma_layout_widget_all_sizes_nonneg(inner, children[i].child, (fuel - 1) as nat, (check_fuel - 1) as nat); };
        },
        _ => {},
    }
}

/// Container children nonneg — complex variants (Flex/Grid/ListView).
proof fn lemma_container_children_nonneg_complex<T: OrderedField>(
    limits: Limits<T>, container: ContainerWidget<T>, fuel: nat, check_fuel: nat,
)
    requires limits.min.is_nonneg(), fuel > 0, check_fuel > 0,
        !(container is Column) && !(container is Row) && !(container is Stack)
        && !(container is Wrap) && !(container is Absolute),
    ensures ({
        let node = layout_widget(limits, Widget::Container(container), fuel);
        forall|i: int| 0 <= i < node.children.len() ==>
            all_sizes_nonneg(#[trigger] node.children[i], (check_fuel - 1) as nat)
    }),
    decreases fuel, check_fuel, 1nat,
{
    match container {
        ContainerWidget::Flex { padding, spacing, alignment, direction, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let weights = Seq::new(children.len(), |i: int| children[i].weight);
            let total_weight = crate::layout::flex::sum_weights(weights, weights.len() as nat);
            let total_spacing = if children.len() > 0 {
                crate::layout::repeated_add(spacing, (children.len() - 1) as nat)
            } else { T::zero() };
            let axis = direction.axis();
            let available_main = inner.max.main_dim(axis).sub(total_spacing);
            let cn = flex_linear_widget_child_nodes(
                inner, children, weights, total_weight, available_main, axis, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by {
                lemma_flex_child_nonneg(inner, children, weights, total_weight, available_main, axis, fuel, check_fuel, i);
            };
            // Help Z3 see node.children[i] has same size/children as cn[i]
            // through layout_flex_linear_body → merge_layout(flex_layout, cn)
            let node = layout_widget(limits, Widget::Container(container), fuel);
            assert(node.children.len() == cn.len());
        },
        ContainerWidget::Grid { padding, h_spacing, v_spacing, h_align, v_align, col_widths, row_heights, children } => {
            let inner = limits.shrink(padding.horizontal(), padding.vertical());
            let cn = grid_widget_child_nodes(inner, col_widths, row_heights, children, col_widths.len(), (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by {
                let child_lim = Limits { min: inner.min,
                    max: Size::new(col_widths[(i % col_widths.len() as int)].width,
                                   row_heights[(i / col_widths.len() as int)].height) };
                lemma_layout_widget_all_sizes_nonneg(child_lim, children[i], (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
            let node = layout_widget(limits, Widget::Container(container), fuel);
            assert(node.children.len() == cn.len());
        },
        ContainerWidget::ListView { spacing, scroll_y, viewport, children } => {
            let child_limits = Limits { min: Size::zero_size(), max: Size::new(viewport.width, viewport.height) };
            T::axiom_le_reflexive(T::zero());
            let child_sizes = crate::measure::measure_children(child_limits, children, (fuel - 1) as nat);
            let first = crate::layout::listview::listview_first_visible(child_sizes, spacing, scroll_y);
            let end = crate::layout::listview::listview_end_visible(child_sizes, spacing, scroll_y, viewport.height);
            let cn = crate::layout::listview::listview_widget_child_nodes(child_limits, children, first, end, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < cn.len() implies
                all_sizes_nonneg(#[trigger] cn[i], (check_fuel - 1) as nat)
            by {
                lemma_layout_widget_all_sizes_nonneg(child_limits, children[(first + i) as int], (fuel - 1) as nat, (check_fuel - 1) as nat);
            };
            // ListView constructs children directly (not merge_layout)
            // but with same size/children as cn[i]
            reveal(crate::layout::listview::layout_listview_body);
        },
        _ => {},  // Column/Row/Stack/Wrap/Absolute handled by caller
    }
}

/// Flex child nonneg — per-index helper for rlimit.
proof fn lemma_flex_child_nonneg<T: OrderedField>(
    inner: Limits<T>, children: Seq<FlexItem<T>>, weights: Seq<T>,
    total_weight: T, available_main: T, axis: crate::layout::Axis,
    fuel: nat, check_fuel: nat, i: int,
)
    requires
        inner.min.is_nonneg(), fuel > 0, check_fuel > 0,
        0 <= i < children.len(), weights.len() == children.len(),
    ensures
        all_sizes_nonneg(
            flex_linear_widget_child_nodes(
                inner, children, weights, total_weight, available_main, axis, (fuel - 1) as nat)[i],
            (check_fuel - 1) as nat),
    decreases fuel, check_fuel, 0nat,
{
    let main_alloc = crate::layout::flex::flex_child_main_size(weights[i], total_weight, available_main);
    match axis {
        crate::layout::Axis::Vertical => {
            lemma_layout_widget_all_sizes_nonneg(
                Limits { min: inner.min, max: Size::new(inner.max.width, main_alloc) },
                children[i].child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
        crate::layout::Axis::Horizontal => {
            lemma_layout_widget_all_sizes_nonneg(
                Limits { min: inner.min, max: Size::new(main_alloc, inner.max.height) },
                children[i].child, (fuel - 1) as nat, (check_fuel - 1) as nat);
        },
    }
}

/// Root draw validity: the root-level draw command from layout is always valid.
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
