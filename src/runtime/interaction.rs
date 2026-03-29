use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::runtime::size::RuntimeSize;
use crate::interaction::*;
use crate::size::Size;

verus! {

//  ── Runtime drag constraints ────────────────────────────────────────

///  Runtime-backed drag constraints with rational coordinates.
pub struct RuntimeDragConstraints {
    pub min_x: RuntimeRational,
    pub max_x: RuntimeRational,
    pub min_y: RuntimeRational,
    pub max_y: RuntimeRational,
    pub model: Ghost<DragConstraints<RationalModel>>,
}

impl View for RuntimeDragConstraints {
    type V = DragConstraints<RationalModel>;

    open spec fn view(&self) -> DragConstraints<RationalModel> {
        self.model@
    }
}

impl RuntimeDragConstraints {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min_x.wf_spec()
        &&& self.max_x.wf_spec()
        &&& self.min_y.wf_spec()
        &&& self.max_y.wf_spec()
        &&& self.min_x@ == self@.min_x
        &&& self.max_x@ == self@.max_x
        &&& self.min_y@ == self@.min_y
        &&& self.max_y@ == self@.max_y
    }
}

//  ── Runtime resize constraints ──────────────────────────────────────

///  Runtime-backed resize constraints.
pub struct RuntimeResizeConstraints {
    pub min_size: RuntimeSize,
    pub max_size: RuntimeSize,
    pub model: Ghost<ResizeConstraints<RationalModel>>,
}

impl View for RuntimeResizeConstraints {
    type V = ResizeConstraints<RationalModel>;

    open spec fn view(&self) -> ResizeConstraints<RationalModel> {
        self.model@
    }
}

impl RuntimeResizeConstraints {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min_size.wf_spec()
        &&& self.max_size.wf_spec()
        &&& self.min_size@ == self@.min_size
        &&& self.max_size@ == self@.max_size
    }
}

//  ── Exec: apply_drag ────────────────────────────────────────────────

///  Apply drag delta to position, clamping to constraints.
///  Returns (new_x, new_y).
pub fn apply_drag_exec(
    constraints: &RuntimeDragConstraints,
    x: &RuntimeRational,
    y: &RuntimeRational,
    dx: &RuntimeRational,
    dy: &RuntimeRational,
) -> (out: (RuntimeRational, RuntimeRational))
    requires
        constraints.wf_spec(),
        constraints@.wf(),
        x.wf_spec(),
        y.wf_spec(),
        dx.wf_spec(),
        dy.wf_spec(),
    ensures ({
        let (rx, ry) = out;
        let (sx, sy) = apply_drag(constraints@, x@, y@, dx@, dy@);
        &&& rx.wf_spec()
        &&& ry.wf_spec()
        &&& rx@ == sx
        &&& ry@ == sy
    }),
{
    //  new_x = clamp(x + dx, min_x, max_x) = max(min_x, min(x + dx, max_x))
    let sum_x = x.add(dx);
    let clamped_x = constraints.min_x.max(&sum_x.min(&constraints.max_x));

    //  new_y = clamp(y + dy, min_y, max_y) = max(min_y, min(y + dy, max_y))
    let sum_y = y.add(dy);
    let clamped_y = constraints.min_y.max(&sum_y.min(&constraints.max_y));

    (clamped_x, clamped_y)
}

//  ── Exec: apply_resize ──────────────────────────────────────────────

///  Apply resize delta to size, clamping to constraints.
pub fn apply_resize_exec(
    constraints: &RuntimeResizeConstraints,
    size: &RuntimeSize,
    dw: &RuntimeRational,
    dh: &RuntimeRational,
) -> (out: RuntimeSize)
    requires
        constraints.wf_spec(),
        constraints@.wf(),
        size.wf_spec(),
        dw.wf_spec(),
        dh.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == apply_resize(constraints@, size@, dw@, dh@),
{
    //  width = clamp(w + dw, min_w, max_w) = max(min_w, min(w + dw, max_w))
    let sum_w = size.width.add(dw);
    let clamped_w = constraints.min_size.width.max(
        &sum_w.min(&constraints.max_size.width));

    //  height = clamp(h + dh, min_h, max_h) = max(min_h, min(h + dh, max_h))
    let sum_h = size.height.add(dh);
    let clamped_h = constraints.min_size.height.max(
        &sum_h.min(&constraints.max_size.height));

    RuntimeSize::new(clamped_w, clamped_h)
}

} //  verus!
