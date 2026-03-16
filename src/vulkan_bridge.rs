use vstd::prelude::*;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use crate::draw::DrawCommand;
use crate::node::Node;

verus! {

// ── GUI render pass specification ─────────────────────────────────────

/// Spec-level description of the GUI render pass.
///
/// The GUI uses a single render pass with one color attachment (the UI
/// framebuffer). No depth attachment — z-ordering is handled by draw
/// command order (painter's algorithm via DFS depth).
pub open spec fn gui_render_pass_attachment_count() -> nat {
    1
}

/// The GUI render pass has a single subpass that writes to the color attachment.
pub open spec fn gui_render_pass_subpass_count() -> nat {
    1
}

// ── GUI pipeline specification ────────────────────────────────────────

/// The GUI graphics pipeline renders axis-aligned quads.
///
/// Each quad is drawn as 2 triangles (6 vertices) using push constants
/// for position and size: (x, y, width, height, color_r, color_g, color_b, color_a).
///
/// The vertex shader generates quad corners from push constants.
/// The fragment shader outputs a solid color from push constants.
pub open spec fn gui_vertices_per_quad() -> nat {
    6  // 2 triangles × 3 vertices
}

/// Push constant size for a single quad draw (in bytes).
/// Layout: x(4) + y(4) + w(4) + h(4) + rgba(16) = 32 bytes.
pub open spec fn gui_push_constant_size() -> nat {
    32
}

// ── Draw command → recorded command mapping ───────────────────────────

/// A GUI draw sequence is a sequence of (push_constants, draw) pairs.
/// Each DrawCommand maps to:
///   1. A push constant update with (x, y, w, h, color)
///   2. A Draw(6) command (2 triangles forming a quad)
///
/// This spec describes the LOGICAL mapping. The actual RecordedCommand
/// types from verus-vulkan would be used in the exec layer.
pub open spec fn gui_commands_per_draw() -> nat {
    2  // push_constants + draw
}

/// Total recorded commands for a sequence of draw commands.
pub open spec fn gui_total_recorded_commands<T: OrderedRing>(
    draws: Seq<DrawCommand<T>>,
) -> nat {
    draws.len() * gui_commands_per_draw()
}

// ── Draw command validity ─────────────────────────────────────────────

/// A draw command is valid for GPU submission when its dimensions
/// are non-negative (width >= 0, height >= 0).
pub open spec fn draw_command_valid<T: OrderedRing>(
    cmd: DrawCommand<T>,
) -> bool {
    &&& T::zero().le(cmd.width)
    &&& T::zero().le(cmd.height)
}

/// All draw commands in a sequence are valid.
pub open spec fn all_draws_valid<T: OrderedRing>(
    draws: Seq<DrawCommand<T>>,
) -> bool {
    forall|i: int| 0 <= i < draws.len() ==>
        draw_command_valid(#[trigger] draws[i])
}

/// A draw command is within the viewport bounds.
pub open spec fn draw_within_viewport<T: OrderedRing>(
    cmd: DrawCommand<T>,
    viewport_width: T,
    viewport_height: T,
) -> bool {
    &&& T::zero().le(cmd.x)
    &&& T::zero().le(cmd.y)
    &&& cmd.x.add(cmd.width).le(viewport_width)
    &&& cmd.y.add(cmd.height).le(viewport_height)
}

// ── Pipeline compatibility ────────────────────────────────────────────

/// The GUI pipeline is compatible with the GUI render pass when:
/// - The pipeline's render_pass_id matches the render pass
/// - The pipeline targets subpass 0
/// - The pipeline has exactly 1 color attachment (matching the render pass)
/// - No depth attachment
pub open spec fn gui_pipeline_compatible(
    pipeline_render_pass_id: nat,
    pipeline_subpass: nat,
    pipeline_color_count: nat,
    pipeline_has_depth: bool,
    render_pass_id: nat,
) -> bool {
    &&& pipeline_render_pass_id == render_pass_id
    &&& pipeline_subpass == 0
    &&& pipeline_color_count == gui_render_pass_attachment_count()
    &&& !pipeline_has_depth
}

// ── Master validity theorem (spec) ────────────────────────────────────

/// All draw commands produced by flattening a node tree are valid
/// (non-negative dimensions) when the source node has non-negative dimensions.
///
/// This connects the layout layer (which produces Nodes) to the rendering
/// layer (which consumes DrawCommands), ensuring GPU-ready output.
pub open spec fn gui_draw_commands_valid_spec<T: OrderedRing>(
    draws: Seq<DrawCommand<T>>,
    render_pass_id: nat,
    pipeline_render_pass_id: nat,
    pipeline_subpass: nat,
    pipeline_color_count: nat,
    pipeline_has_depth: bool,
) -> bool {
    &&& all_draws_valid(draws)
    &&& gui_pipeline_compatible(
            pipeline_render_pass_id, pipeline_subpass,
            pipeline_color_count, pipeline_has_depth, render_pass_id)
}

} // verus!
