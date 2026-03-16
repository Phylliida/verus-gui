use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::ring::Ring;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::node::RuntimeNode;
use crate::node::Node;
use crate::draw::*;
use crate::draw_proofs::*;

verus! {

// ── Runtime draw command ──────────────────────────────────────────────

/// Runtime draw command with rational coordinates.
pub struct RuntimeDrawCommand {
    /// Absolute screen x coordinate.
    pub x: RuntimeRational,
    /// Absolute screen y coordinate.
    pub y: RuntimeRational,
    /// Width of the rectangle.
    pub width: RuntimeRational,
    /// Height of the rectangle.
    pub height: RuntimeRational,
    /// Depth in the tree (DFS order).
    pub depth: usize,
    /// Ghost model.
    pub model: Ghost<DrawCommand<RationalModel>>,
}

impl View for RuntimeDrawCommand {
    type V = DrawCommand<RationalModel>;

    open spec fn view(&self) -> DrawCommand<RationalModel> {
        self.model@
    }
}

impl RuntimeDrawCommand {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.width.wf_spec()
        &&& self.height.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.width@ == self@.width
        &&& self.height@ == self@.height
        &&& self.depth as nat == self@.depth
    }
}

// ── Helper: append draw commands ─────────────────────────────────────

/// Append all elements of `src` to `dst`, preserving ghost models.
fn append_draw_commands(dst: &mut Vec<RuntimeDrawCommand>, src: &Vec<RuntimeDrawCommand>)
    requires
        forall|i: int| 0 <= i < old(dst)@.len() ==>
            (#[trigger] old(dst)@[i]).wf_spec(),
        forall|i: int| 0 <= i < src@.len() ==>
            (#[trigger] src@[i]).wf_spec(),
    ensures
        dst@.len() == old(dst)@.len() + src@.len(),
        forall|i: int| 0 <= i < old(dst)@.len() ==>
            (#[trigger] dst@[i])@ === old(dst)@[i]@,
        forall|i: int| 0 <= i < src@.len() ==>
            (#[trigger] dst@[old(dst)@.len() + i])@ === src@[i]@,
        forall|i: int| 0 <= i < dst@.len() ==>
            (#[trigger] dst@[i]).wf_spec(),
{
    let ghost old_len = old(dst)@.len();
    let n = src.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == src@.len(),
            dst@.len() == old_len + k,
            forall|j: int| 0 <= j < old_len ==>
                (#[trigger] dst@[j])@ === old(dst)@[j]@,
            forall|j: int| 0 <= j < k as int ==>
                (#[trigger] dst@[old_len + j])@ === src@[j]@,
            forall|j: int| 0 <= j < dst@.len() ==>
                (#[trigger] dst@[j]).wf_spec(),
            forall|j: int| 0 <= j < src@.len() ==>
                (#[trigger] src@[j]).wf_spec(),
        decreases n - k,
    {
        let cd = &src[k];
        let cmd = RuntimeDrawCommand {
            x: copy_rational(&cd.x),
            y: copy_rational(&cd.y),
            width: copy_rational(&cd.width),
            height: copy_rational(&cd.height),
            depth: cd.depth,
            model: Ghost(cd@),
        };
        dst.push(cmd);
        k = k + 1;
    }
}

// ── Flatten node exec ─────────────────────────────────────────────────

/// Flatten a RuntimeNode tree into a flat Vec of RuntimeDrawCommands.
///
/// Performs DFS traversal: emit current node, then recursively emit
/// all children. Offsets accumulate absolute screen positions.
///
/// Strong ensures: output matches `flatten_node_to_draws` exactly.
pub fn flatten_node_exec(
    node: &RuntimeNode,
    offset_x: &RuntimeRational,
    offset_y: &RuntimeRational,
    depth: usize,
    fuel: usize,
) -> (out: Vec<RuntimeDrawCommand>)
    requires
        node.wf_deep(fuel as nat),
        offset_x.wf_spec(),
        offset_y.wf_spec(),
        depth as nat + node_count::<RationalModel>(node@, fuel as nat) <= usize::MAX as nat,
    ensures
        out@.len() as nat == flatten_node_to_draws::<RationalModel>(
            node@, offset_x@, offset_y@, depth as nat, fuel as nat).len(),
        forall|i: int| 0 <= i < out@.len() ==> {
            &&& (#[trigger] out@[i]).wf_spec()
            &&& out@[i]@ === flatten_node_to_draws::<RationalModel>(
                node@, offset_x@, offset_y@, depth as nat, fuel as nat)[i]
        },
    decreases fuel, 0nat,
{
    let ghost spec_result = flatten_node_to_draws::<RationalModel>(
        node@, offset_x@, offset_y@, depth as nat, fuel as nat);

    // Compute absolute position of this node
    let abs_x = offset_x.add(&node.x);
    let abs_y = offset_y.add(&node.y);

    // Ghost: the spec self_draw matches what flatten_node_to_draws produces
    let ghost self_draw_model = DrawCommand::<RationalModel> {
        x: abs_x@,
        y: abs_y@,
        width: node@.size.width,
        height: node@.size.height,
        depth: depth as nat,
    };

    let self_draw = RuntimeDrawCommand {
        x: copy_rational(&abs_x),
        y: copy_rational(&abs_y),
        width: copy_rational(&node.size.width),
        height: copy_rational(&node.size.height),
        depth,
        model: Ghost(self_draw_model),
    };

    if fuel == 0 {
        // Base case: just the one draw command
        let mut result: Vec<RuntimeDrawCommand> = Vec::new();
        result.push(self_draw);
        // spec_result = Seq::empty().push(self_draw_model)
        result
    } else {
        let ghost spec_children: Seq<Node<RationalModel>> = node@.children;

        // Bridge nat/usize fuel arithmetic
        assert((fuel as nat - 1) as nat == (fuel - 1) as nat);

        // Depth bound for children: node_count = 1 + children_count
        // so depth + 1 + children_count = depth + node_count <= usize::MAX

        let children_draws = flatten_children_exec(
            &node.children, &abs_x, &abs_y,
            depth + 1, fuel - 1, 0,
            Ghost(spec_children));

        // Build result: self_draw + children_draws
        let mut result: Vec<RuntimeDrawCommand> = Vec::new();
        result.push(self_draw);
        append_draw_commands(&mut result, &children_draws);

        // Prove result matches spec
        proof {
            let children_spec = flatten_children_to_draws::<RationalModel>(
                spec_children, abs_x@, abs_y@,
                (depth as nat) + 1, (fuel - 1) as nat, 0 as nat);

            // Unfold the spec definition for fuel > 0
            assert(spec_result =~= Seq::empty().push(self_draw_model).add(children_spec));

            assert forall|i: int| 0 <= i < result@.len() implies
                (#[trigger] result@[i]).wf_spec() &&
                result@[i]@ === spec_result[i]
            by {
                if i == 0 {
                    // result@[0] is self_draw, which has model self_draw_model
                    // spec_result[0] = self_draw_model (from Seq::empty().push(self_draw_model))
                } else {
                    // result@[i] = children_draws@[i - 1] (from append_draw_commands)
                    // children_draws@[i-1]@ === children_spec[i-1] (from flatten_children_exec ensures)
                    // spec_result[i] = children_spec[i-1] (from .add indexing)
                }
            };
        }

        result
    }
}

// ── Flatten children exec ────────────────────────────────────────────

/// Flatten children of a RuntimeNode starting from index `from`.
/// Mirrors `flatten_children_to_draws` in spec.
fn flatten_children_exec(
    children: &Vec<RuntimeNode>,
    parent_abs_x: &RuntimeRational,
    parent_abs_y: &RuntimeRational,
    start_depth: usize,
    fuel: usize,
    from: usize,
    spec_children: Ghost<Seq<Node<RationalModel>>>,
) -> (out: Vec<RuntimeDrawCommand>)
    requires
        parent_abs_x.wf_spec(),
        parent_abs_y.wf_spec(),
        from <= children@.len(),
        children@.len() == spec_children@.len(),
        forall|i: int| from as int <= i < children@.len() ==> {
            &&& (#[trigger] children@[i]).wf_deep(fuel as nat)
            &&& children@[i]@ == spec_children@[i]
        },
        start_depth as nat + children_node_count::<RationalModel>(
            spec_children@, fuel as nat, from as nat) <= usize::MAX as nat,
    ensures
        out@.len() as nat == flatten_children_to_draws::<RationalModel>(
            spec_children@, parent_abs_x@, parent_abs_y@,
            start_depth as nat, fuel as nat, from as nat).len(),
        forall|i: int| 0 <= i < out@.len() ==> {
            &&& (#[trigger] out@[i]).wf_spec()
            &&& out@[i]@ === flatten_children_to_draws::<RationalModel>(
                spec_children@, parent_abs_x@, parent_abs_y@,
                start_depth as nat, fuel as nat, from as nat)[i]
        },
    decreases fuel, children@.len() - from,
{
    let ghost spec_seq = flatten_children_to_draws::<RationalModel>(
        spec_children@, parent_abs_x@, parent_abs_y@,
        start_depth as nat, fuel as nat, from as nat);

    if from >= children.len() {
        // Empty case: spec returns Seq::empty()
        Vec::new()
    } else {
        // Prove child wf and model agreement
        assert(children@[from as int].wf_deep(fuel as nat));
        assert(children@[from as int]@ == spec_children@[from as int]);

        // Prove depth bound: node_count(child) <= children_count(from) so no overflow
        // children_node_count(spec, fuel, from) = node_count(spec[from], fuel) + children_node_count(spec, fuel, from+1)
        // So start_depth + node_count(spec[from], fuel) <= start_depth + children_count(spec, fuel, from) <= usize::MAX

        let first_draws = flatten_node_exec(
            &children[from], parent_abs_x, parent_abs_y,
            start_depth, fuel);

        // Invoke count preservation lemma to connect first_draws.len() to node_count
        proof {
            lemma_flatten_preserves_count::<RationalModel>(
                spec_children@[from as int], parent_abs_x@, parent_abs_y@,
                start_depth as nat, fuel as nat);
        }

        // Compute next_depth — safe because first_draws.len() = node_count(child, fuel) <= children_count(from)
        let next_depth: usize = start_depth + first_draws.len();

        // Recursive call for remaining children
        let rest_draws = flatten_children_exec(
            children, parent_abs_x, parent_abs_y,
            next_depth, fuel, from + 1,
            spec_children);

        // Concatenate first_draws + rest_draws
        let mut result = first_draws;
        let ghost first_len = result@.len();
        append_draw_commands(&mut result, &rest_draws);

        // Prove result matches spec
        proof {
            let first_spec = flatten_node_to_draws::<RationalModel>(
                spec_children@[from as int], parent_abs_x@, parent_abs_y@,
                start_depth as nat, fuel as nat);
            let next_depth_spec: nat = (start_depth as nat) + first_spec.len();
            let rest_spec = flatten_children_to_draws::<RationalModel>(
                spec_children@, parent_abs_x@, parent_abs_y@,
                next_depth_spec, fuel as nat, (from + 1) as nat);

            // spec_seq = first_spec.add(rest_spec) by definition
            assert(spec_seq =~= first_spec.add(rest_spec));

            assert forall|i: int| 0 <= i < result@.len() implies
                (#[trigger] result@[i]).wf_spec() &&
                result@[i]@ === spec_seq[i]
            by {
                if i < first_len {
                    // result@[i]@ === first_draws@[i]@ (append preserves prefix)
                    // first_draws@[i]@ === first_spec[i] (from flatten_node_exec ensures)
                    // spec_seq[i] = first_spec.add(rest_spec)[i] = first_spec[i] since i < first_spec.len()
                } else {
                    // result@[i]@ === rest_draws@[i - first_len]@ (from append ensures)
                    // rest_draws@[j]@ === rest_spec[j] where j = i - first_len (from recursive ensures)
                    // spec_seq[i] = first_spec.add(rest_spec)[i] = rest_spec[i - first_spec.len()] = rest_spec[i - first_len]
                }
            };
        }

        result
    }
}

} // verus!
