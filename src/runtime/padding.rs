use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::padding::Padding;
use crate::layout::Axis;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

verus! {

pub struct RuntimePadding<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub top: R,
    pub right: R,
    pub bottom: R,
    pub left: R,
    pub model: Ghost<Padding<V>>,
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> View for RuntimePadding<R, V> {
    type V = Padding<V>;
    open spec fn view(&self) -> Padding<V> { self.model@ }
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimePadding<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.top.wf_spec() &&& self.right.wf_spec()
        &&& self.bottom.wf_spec() &&& self.left.wf_spec()
        &&& self.top@ == self@.top
        &&& self.right@ == self@.right
        &&& self.bottom@ == self@.bottom
        &&& self.left@ == self@.left
    }

    pub fn new(top: R, right: R, bottom: R, left: R) -> (out: Self)
        requires top.wf_spec(), right.wf_spec(), bottom.wf_spec(), left.wf_spec(),
        ensures out.wf_spec(),
            out@.top == top@, out@.right == right@,
            out@.bottom == bottom@, out@.left == left@,
    {
        let ghost model = Padding { top: top@, right: right@, bottom: bottom@, left: left@ };
        RuntimePadding { top, right, bottom, left, model: Ghost(model) }
    }

    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out ==> (
            self@.top.eqv(rhs@.top) && self@.right.eqv(rhs@.right) &&
            self@.bottom.eqv(rhs@.bottom) && self@.left.eqv(rhs@.left)
        ),
    {
        self.top.eq(&rhs.top) && self.right.eq(&rhs.right) &&
        self.bottom.eq(&rhs.bottom) && self.left.eq(&rhs.left)
    }

    pub fn horizontal_exec(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.horizontal(),
    { self.left.add(&self.right) }

    pub fn vertical_exec(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.vertical(),
    { self.top.add(&self.bottom) }

    pub fn main_padding_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.main_padding(*axis),
    { match axis { Axis::Vertical => self.vertical_exec(), Axis::Horizontal => self.horizontal_exec() } }

    pub fn cross_padding_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.cross_padding(*axis),
    { match axis { Axis::Vertical => self.horizontal_exec(), Axis::Horizontal => self.vertical_exec() } }

    pub fn main_start_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.main_start(*axis),
    { match axis { Axis::Vertical => self.top.copy(), Axis::Horizontal => self.left.copy() } }

    pub fn cross_start_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == self@.cross_start(*axis),
    { match axis { Axis::Vertical => self.left.copy(), Axis::Horizontal => self.top.copy() } }
}

impl RuntimePadding<RuntimeRational, Rational> {
    pub fn normalize_exec(self) -> (out: Self)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out@.top.eqv_spec(self@.top),
            out@.right.eqv_spec(self@.right),
            out@.bottom.eqv_spec(self@.bottom),
            out@.left.eqv_spec(self@.left),
            out@.top.normalized_spec(),
            out@.right.normalized_spec(),
            out@.bottom.normalized_spec(),
            out@.left.normalized_spec(),
    {
        RuntimePadding::new(
            self.top.normalize(), self.right.normalize(),
            self.bottom.normalize(), self.left.normalize(),
        )
    }
}

} //  verus!
