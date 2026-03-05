use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::padding::RuntimePadding;
use crate::runtime::node::RuntimeNode;
use crate::runtime::column::*;
use crate::runtime::row::*;
use crate::runtime::stack::*;
use crate::runtime::wrap::*;
use crate::size::Size;
use crate::node::Node;
use crate::alignment::Alignment;
use crate::widget::*;
use crate::layout::*;
use crate::layout::proofs::*;
use crate::layout::stack::*;
use crate::layout::wrap::*;
use crate::layout::wrap_proofs::*;

verus! {

/// Runtime Widget tree mirroring the spec Widget enum.
pub enum RuntimeWidget {
    Leaf {
        size: RuntimeSize,
        model: Ghost<Widget<RationalModel>>,
    },
    Column {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Row {
        padding: RuntimePadding,
        spacing: RuntimeRational,
        alignment: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Stack {
        padding: RuntimePadding,
        h_align: Alignment,
        v_align: Alignment,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
    Wrap {
        padding: RuntimePadding,
        h_spacing: RuntimeRational,
        v_spacing: RuntimeRational,
        children: Vec<RuntimeWidget>,
        model: Ghost<Widget<RationalModel>>,
    },
}

impl RuntimeWidget {
    /// Extract the ghost model.
    pub open spec fn model(&self) -> Widget<RationalModel> {
        match self {
            RuntimeWidget::Leaf { model, .. } => model@,
            RuntimeWidget::Column { model, .. } => model@,
            RuntimeWidget::Row { model, .. } => model@,
            RuntimeWidget::Stack { model, .. } => model@,
            RuntimeWidget::Wrap { model, .. } => model@,
        }
    }

    /// Shallow well-formedness: direct fields match model, no recursive child check.
    pub open spec fn wf_shallow(&self) -> bool {
        match self {
            RuntimeWidget::Leaf { size, model } => {
                &&& size.wf_spec()
                &&& model@ == Widget::Leaf { size: size@ }
            },
            RuntimeWidget::Column { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == Widget::Column {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Row { padding, spacing, alignment, children, model } => {
                &&& padding.wf_spec()
                &&& spacing.wf_spec()
                &&& model@ == Widget::Row {
                    padding: padding@,
                    spacing: spacing@,
                    alignment: *alignment,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Stack { padding, h_align, v_align, children, model } => {
                &&& padding.wf_spec()
                &&& model@ == Widget::Stack {
                    padding: padding@,
                    h_align: *h_align,
                    v_align: *v_align,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
            RuntimeWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                &&& padding.wf_spec()
                &&& h_spacing.wf_spec()
                &&& v_spacing.wf_spec()
                &&& model@ == Widget::Wrap {
                    padding: padding@,
                    h_spacing: h_spacing@,
                    v_spacing: v_spacing@,
                    children: Seq::new(children@.len() as nat, |i: int| children@[i].model()),
                }
            },
        }
    }

    /// Full well-formedness at a given fuel depth.
    pub open spec fn wf_spec(&self, fuel: nat) -> bool
        decreases fuel,
    {
        if fuel == 0 {
            false
        } else {
            &&& self.wf_shallow()
            &&& match self {
                RuntimeWidget::Leaf { .. } => true,
                RuntimeWidget::Column { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Row { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Stack { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
                RuntimeWidget::Wrap { children, .. } => {
                    forall|i: int| 0 <= i < children@.len() ==>
                        (#[trigger] children@[i]).wf_spec((fuel - 1) as nat)
                },
            }
        }
    }
}

// ── Layout widget exec ───────────────────────────────────────────

/// Recursively lay out a RuntimeWidget tree.
pub fn layout_widget_exec(
    limits: &RuntimeLimits,
    widget: &RuntimeWidget,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        widget.wf_spec(fuel as nat),
    ensures
        out.wf_spec(),
        out@ == layout_widget::<RationalModel>(limits@, widget.model(), fuel as nat),
    decreases fuel, 1nat,
{
    if fuel == 0 {
        // Unreachable: wf_spec(0) is false
        let z1 = RuntimeRational::from_int(0);
        let z2 = RuntimeRational::from_int(0);
        RuntimeNode::leaf_exec(z1, z2, RuntimeSize::zero_exec())
    } else {
        match widget {
            RuntimeWidget::Leaf { size, model } => {
                let resolved = limits.resolve_exec(size.copy_size());
                let x = RuntimeRational::from_int(0);
                let y = RuntimeRational::from_int(0);
                RuntimeNode::leaf_exec(x, y, resolved)
            },
            RuntimeWidget::Column { padding, spacing, alignment, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                    }
                }
                let dummy_sp = RuntimeRational::from_int(0);
                layout_container_exec(limits, padding, spacing, &Alignment::Start,
                    alignment, &dummy_sp, children, fuel, ContainerKind::Column)
            },
            RuntimeWidget::Row { padding, spacing, alignment, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                let dummy_sp = RuntimeRational::from_int(0);
                layout_container_exec(limits, padding, spacing, alignment,
                    &Alignment::Start, &dummy_sp, children, fuel, ContainerKind::Row)
            },
            RuntimeWidget::Stack { padding, h_align, v_align, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                let zero_sp = RuntimeRational::from_int(0);
                let dummy_sp = RuntimeRational::from_int(0);
                layout_container_exec(limits, padding, &zero_sp, h_align,
                    v_align, &dummy_sp, children, fuel, ContainerKind::Stack)
            },
            RuntimeWidget::Wrap { padding, h_spacing, v_spacing, children, model } => {
                proof {
                    assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    assert forall|j: int| 0 <= j < children@.len() implies
                        (#[trigger] children@[j]).wf_spec((fuel - 1) as nat)
                    by {
                        assert(children@[j].wf_spec((fuel as nat - 1) as nat));
                        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);
                    }
                }
                layout_container_exec(limits, padding, h_spacing, &Alignment::Start,
                    &Alignment::Start, v_spacing, children, fuel, ContainerKind::Wrap)
            },
        }
    }
}

/// Which layout strategy to use.
pub enum ContainerKind {
    Column,
    Row,
    Stack,
    Wrap,
}

/// Shared container layout: recursively compute children, call layout exec, merge.
fn layout_container_exec(
    limits: &RuntimeLimits,
    padding: &RuntimePadding,
    spacing1: &RuntimeRational,  // spacing (col/row), h_spacing (wrap), unused (stack)
    align1: &Alignment,          // alignment (row), h_align (stack), unused (col/wrap)
    align2: &Alignment,          // alignment (col), v_align (stack), unused (row/wrap)
    spacing2: &RuntimeRational,  // v_spacing (wrap), unused (col/row/stack)
    children: &Vec<RuntimeWidget>,
    fuel: usize,
    kind: ContainerKind,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        padding.wf_spec(),
        spacing1.wf_spec(),
        spacing2.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let inner = limits@.shrink(padding@.horizontal(), padding@.vertical());
            let spec_wc = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let cn = widget_child_nodes(inner, spec_wc, (fuel - 1) as nat);
            match kind {
                ContainerKind::Column =>
                    layout_column_body(limits@, padding@, spacing1@, *align2, cn),
                ContainerKind::Row =>
                    layout_row_body(limits@, padding@, spacing1@, *align1, cn),
                ContainerKind::Stack =>
                    layout_stack_body(limits@, padding@, *align1, *align2, cn),
                ContainerKind::Wrap =>
                    layout_wrap_body(limits@, padding@, spacing1@, spacing2@, cn),
            }
        }),
    decreases fuel, 0nat,
{
    let pad_h = padding.horizontal_exec();
    let pad_v = padding.vertical_exec();
    let inner = limits.shrink_exec(&pad_h, &pad_v);

    let n = children.len();

    // Ghost: spec-level children sequence
    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |j: int| children@[j].model());

    // 1. Recursively compute child nodes
    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == children@.len(),
            spec_wc.len() == n as nat,
            // Pointwise Seq::new unfolding (ghost let not available in loop)
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] children@[j]).model(),
            inner.wf_spec(),
            inner@ == limits@.shrink(pad_h@, pad_v@),
            fuel > 0,
            child_nodes@.len() == i as int,
            child_sizes@.len() == i as int,
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == layout_widget::<RationalModel>(
                        inner@, spec_wc[j], (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == child_nodes@[j]@.size
            },
        decreases n - i,
    {
        let cn = layout_widget_exec(&inner, &children[i], fuel - 1);
        child_sizes.push(cn.size.copy_size());
        child_nodes.push(cn);
        i = i + 1;
    }

    // Assert child_sizes wf for layout exec preconditions
    proof {
        assert forall|j: int| 0 <= j < child_sizes@.len() implies
            (#[trigger] child_sizes@[j]).wf_spec()
        by {
            // From loop invariant: child_sizes@[j].wf_spec() for j < i == n
        }
    }

    // 2. Call the appropriate layout exec
    let layout_result = match kind {
        ContainerKind::Column => {
            column_layout_exec(limits, padding, spacing1, align2, &child_sizes)
        },
        ContainerKind::Row => {
            row_layout_exec(limits, padding, spacing1, align1, &child_sizes)
        },
        ContainerKind::Stack => {
            stack_layout_exec(limits, padding, align1, align2, &child_sizes)
        },
        ContainerKind::Wrap => {
            wrap_layout_exec(limits, padding, spacing1, spacing2, &child_sizes)
        },
    };

    // Prove layout_result has n children (needed for merge precondition)
    proof {
        let child_sizes_seq: Seq<Size<RationalModel>> =
            Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        match kind {
            ContainerKind::Column => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                lemma_column_children_len::<RationalModel>(
                    padding@, spacing1@, *align2, child_sizes_seq, avail_w, 0nat);
            },
            ContainerKind::Row => {
                let avail_h = limits@.max.height.sub(padding@.vertical());
                lemma_row_children_len::<RationalModel>(
                    padding@, spacing1@, *align1, child_sizes_seq, avail_h, 0nat);
            },
            ContainerKind::Stack => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                let avail_h = limits@.max.height.sub(padding@.vertical());
                lemma_stack_children_len::<RationalModel>(
                    padding@, *align1, *align2, child_sizes_seq, avail_w, avail_h, 0nat);
            },
            ContainerKind::Wrap => {
                let avail_w = limits@.max.width.sub(padding@.horizontal());
                lemma_wrap_children_len::<RationalModel>(
                    padding@, spacing1@, spacing2@, child_sizes_seq, avail_w, 0nat);
            },
        }
        assert(layout_result.children@.len() == child_nodes@.len());
    }

    // 3. Merge positions from layout_result with child_nodes
    let ghost cn_models: Seq<Node<RationalModel>> =
        Seq::new(n as nat, |j: int| child_nodes@[j]@);

    let merged = merge_layout_exec(layout_result, child_nodes, Ghost(cn_models));

    // 4. Connect to spec
    proof {
        let inner_spec = limits@.shrink(padding@.horizontal(), padding@.vertical());
        let spec_cn = widget_child_nodes(inner_spec, spec_wc, (fuel - 1) as nat);

        // Show cn_models == spec_cn via extensional equality
        assert(cn_models.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < cn_models.len() as int implies
            cn_models[j] == spec_cn[j]
        by {
            // cn_models[j] = child_nodes@[j]@ = layout_widget(inner@, spec_wc[j], fuel-1)
            // spec_cn[j] = layout_widget(inner_spec, spec_wc[j], fuel-1)
            // inner@ == inner_spec, so they're equal
        }
        assert(cn_models =~= spec_cn);

        let child_sizes_seq = Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        assert(child_sizes_seq.len() == spec_cn.len());
        assert forall|j: int| 0 <= j < child_sizes_seq.len() as int implies
            child_sizes_seq[j] == spec_cn[j].size
        by {}
        assert(child_sizes_seq =~= Seq::new(spec_cn.len(), |j: int| spec_cn[j].size));
    }

    merged
}

// ── Merge layout exec ────────────────────────────────────────────

/// Merge positions from a layout result with recursively computed child nodes.
fn merge_layout_exec(
    layout_result: RuntimeNode,
    mut child_nodes: Vec<RuntimeNode>,
    ghost_child_models: Ghost<Seq<Node<RationalModel>>>,
) -> (out: RuntimeNode)
    requires
        layout_result.wf_spec(),
        layout_result.children@.len() == child_nodes@.len(),
        ghost_child_models@.len() == child_nodes@.len() as nat,
        forall|i: int| 0 <= i < child_nodes@.len() ==> {
            &&& (#[trigger] child_nodes@[i]).wf_spec()
            &&& child_nodes@[i]@ == ghost_child_models@[i]
        },
    ensures
        out.wf_spec(),
        out@ == merge_layout::<RationalModel>(layout_result@, ghost_child_models@),
{
    let ghost spec_cn = ghost_child_models@;
    let ghost merged_model = merge_layout::<RationalModel>(layout_result@, spec_cn);

    let n = child_nodes.len();
    let mut merged_children: Vec<RuntimeNode> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == layout_result.children@.len(),
            child_nodes@.len() == n,
            layout_result.wf_spec(),
            merged_children@.len() == i as int,
            spec_cn.len() == n as nat,
            merged_model.children.len() == n as nat,
            layout_result@.children.len() == n as nat,
            // Pointwise merge_layout unfolding (ghost let not available in loop)
            forall|j: int| 0 <= j < n ==>
                (#[trigger] merged_model.children[j]) == (Node::<RationalModel> {
                    x: layout_result@.children[j].x,
                    y: layout_result@.children[j].y,
                    size: spec_cn[j].size,
                    children: spec_cn[j].children,
                }),
            // Elements [i..n) still original
            forall|j: int| i as int <= j < n as int ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ == spec_cn[j]
            },
            // Merged elements match model
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] merged_children@[j]).wf_shallow()
                &&& merged_children@[j]@ == merged_model.children[j]
            },
        decreases n - i,
    {
        let x = copy_rational(&layout_result.children[i].x);
        let y = copy_rational(&layout_result.children[i].y);

        // Capture facts about child_nodes[i] before the swap
        proof {
            assert(child_nodes@[i as int].wf_spec());
            assert(child_nodes@[i as int]@ == spec_cn[i as int]);
        }

        // Swap child_nodes[i] with a dummy to take ownership
        let mut swap_val = RuntimeNode::leaf_exec(
            RuntimeRational::from_int(0),
            RuntimeRational::from_int(0),
            RuntimeSize::zero_exec(),
        );
        child_nodes.set_and_swap(i, &mut swap_val);
        let cn = swap_val;

        // Construct ghost model directly from components
        let ghost child_model = Node::<RationalModel> {
            x: layout_result@.children[i as int].x,
            y: layout_result@.children[i as int].y,
            size: spec_cn[i as int].size,
            children: spec_cn[i as int].children,
        };

        let merged_child = RuntimeNode {
            x,
            y,
            size: cn.size,
            children: cn.children,
            model: Ghost(child_model),
        };

        proof {
            // child_model == merged_model.children[i] from pointwise invariant
            assert(child_model == merged_model.children[i as int]);
            // wf_shallow: fields match model
            assert(layout_result.children@[i as int].wf_shallow());
            assert(layout_result.children@[i as int]@ == layout_result@.children[i as int]);
            assert(merged_child.wf_shallow());
            assert(merged_child@ == merged_model.children[i as int]);
        }

        merged_children.push(merged_child);
        i = i + 1;
    }

    RuntimeNode {
        x: layout_result.x,
        y: layout_result.y,
        size: layout_result.size,
        children: merged_children,
        model: Ghost(merged_model),
    }
}

} // verus!
