use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::ring::Ring;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::node::RuntimeNode;
use crate::node::Node;
use crate::draw::*;

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

// ── Flatten node exec ─────────────────────────────────────────────────

/// Flatten a RuntimeNode tree into a flat Vec of RuntimeDrawCommands.
///
/// Performs DFS traversal: emit current node, then recursively emit
/// all children. Offsets accumulate absolute screen positions.
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
    ensures
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).wf_spec(),
    decreases fuel,
{
    // Compute absolute position of this node
    let abs_x = offset_x.add(&node.x);
    let abs_y = offset_y.add(&node.y);

    // Ghost: capture the spec-level absolute positions before the loop
    let ghost abs_x_spec: RationalModel = abs_x@;
    let ghost abs_y_spec: RationalModel = abs_y@;

    // Emit this node's draw command
    let ghost self_draw_model = DrawCommand {
        x: abs_x_spec,
        y: abs_y_spec,
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

    let mut result: Vec<RuntimeDrawCommand> = Vec::new();
    result.push(self_draw);

    if fuel == 0 {
        // Base: just the one draw command
        result
    } else {
        // Recursively flatten children
        let n = node.children.len();
        let mut child_idx: usize = 0;

        while child_idx < n
            invariant
                0 <= child_idx <= n,
                n == node.children@.len(),
                node.wf_deep(fuel as nat),
                fuel > 0,
                abs_x.wf_spec(),
                abs_y.wf_spec(),
                abs_x@ == abs_x_spec,
                abs_y@ == abs_y_spec,
                result@.len() >= 1,
                forall|j: int| 0 <= j < result@.len() ==>
                    (#[trigger] result@[j]).wf_spec(),
            decreases n - child_idx,
        {
            assert(node.children@[child_idx as int].wf_deep((fuel - 1) as nat));
            let child_draws = flatten_node_exec(
                &node.children[child_idx],
                &abs_x, &abs_y,
                0, fuel - 1);  // depth tracking simplified for now

            // Append child draws to result
            let mut k: usize = 0;
            let cd_len = child_draws.len();
            while k < cd_len
                invariant
                    0 <= k <= cd_len,
                    cd_len == child_draws@.len(),
                    result@.len() >= 1,
                    forall|j: int| 0 <= j < child_draws@.len() ==>
                        (#[trigger] child_draws@[j]).wf_spec(),
                    forall|j: int| 0 <= j < result@.len() ==>
                        (#[trigger] result@[j]).wf_spec(),
                decreases cd_len - k,
            {
                let cd = &child_draws[k];
                let cmd = RuntimeDrawCommand {
                    x: copy_rational(&cd.x),
                    y: copy_rational(&cd.y),
                    width: copy_rational(&cd.width),
                    height: copy_rational(&cd.height),
                    depth: cd.depth,
                    model: Ghost(cd@),
                };
                result.push(cmd);
                k = k + 1;
            }

            child_idx = child_idx + 1;
        }

        result
    }
}

} // verus!
