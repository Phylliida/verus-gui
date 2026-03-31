use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::interaction::*;
use crate::size::Size;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

pub struct RuntimeDragConstraints<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub min_x: R,
    pub max_x: R,
    pub min_y: R,
    pub max_y: R,
    pub model: Ghost<DragConstraints<V>>,
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimeDragConstraints<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min_x.wf_spec() &&& self.max_x.wf_spec()
        &&& self.min_y.wf_spec() &&& self.max_y.wf_spec()
        &&& self.min_x.model() == self.model@.min_x
        &&& self.max_x.model() == self.model@.max_x
        &&& self.min_y.model() == self.model@.min_y
        &&& self.max_y.model() == self.model@.max_y
    }
}

pub struct RuntimeResizeConstraints<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub min_size: RuntimeSize<R, V>,
    pub max_size: RuntimeSize<R, V>,
    pub model: Ghost<ResizeConstraints<V>>,
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimeResizeConstraints<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min_size.wf_spec()
        &&& self.max_size.wf_spec()
        &&& self.min_size.model@ == self.model@.min_size
        &&& self.max_size.model@ == self.model@.max_size
    }
}

pub fn apply_drag_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    constraints: &RuntimeDragConstraints<R, V>,
    x: &R, y: &R, dx: &R, dy: &R,
) -> (out: (R, R))
    requires
        constraints.wf_spec(), constraints.model@.wf(),
        x.wf_spec(), y.wf_spec(), dx.wf_spec(), dy.wf_spec(),
    ensures ({
        let (rx, ry) = out;
        let (sx, sy) = apply_drag(constraints.model@, x.model(), y.model(), dx.model(), dy.model());
        &&& rx.wf_spec() &&& ry.wf_spec()
        &&& rx.model() == sx &&& ry.model() == sy
    }),
{
    let sum_x = x.add(dx);
    let clamped_x = constraints.min_x.max(&sum_x.min(&constraints.max_x));
    let sum_y = y.add(dy);
    let clamped_y = constraints.min_y.max(&sum_y.min(&constraints.max_y));
    (clamped_x, clamped_y)
}

pub fn apply_resize_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    constraints: &RuntimeResizeConstraints<R, V>,
    size: &RuntimeSize<R, V>,
    dw: &R, dh: &R,
) -> (out: RuntimeSize<R, V>)
    requires
        constraints.wf_spec(), constraints.model@.wf(),
        size.wf_spec(), dw.wf_spec(), dh.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == apply_resize(constraints.model@, size.model@, dw.model(), dh.model()),
{
    let sum_w = size.width.add(dw);
    let clamped_w = constraints.min_size.width.max(&sum_w.min(&constraints.max_size.width));
    let sum_h = size.height.add(dh);
    let clamped_h = constraints.min_size.height.max(&sum_h.min(&constraints.max_size.height));
    RuntimeSize::new(clamped_w, clamped_h)
}

} //  verus!
