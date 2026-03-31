use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::size::Size;
use crate::layout::Axis;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

verus! {

pub struct RuntimeSize<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub width: R,
    pub height: R,
    pub model: Ghost<Size<V>>,
}

//  View impl for the concrete Rational instantiation — keeps @ working for existing callers.
impl View for RuntimeSize<RuntimeRational, Rational> {
    type V = Size<Rational>;
    open spec fn view(&self) -> Size<Rational> { self.model@ }
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimeSize<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.width.wf_spec()
        &&& self.height.wf_spec()
        &&& self.width.model() == self.model@.width
        &&& self.height.model() == self.model@.height
    }

    pub fn new(width: R, height: R) -> (out: Self)
        requires width.wf_spec(), height.wf_spec(),
        ensures out.wf_spec(), out.model@.width == width.model(), out.model@.height == height.model(),
    {
        let ghost model = Size { width: width.model(), height: height.model() };
        RuntimeSize { width, height, model: Ghost(model) }
    }

    pub fn copy_size(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@,
    {
        RuntimeSize::new(self.width.copy(), self.height.copy())
    }

    pub fn main_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model@.main_dim(*axis),
    {
        match axis {
            Axis::Vertical => self.height.copy(),
            Axis::Horizontal => self.width.copy(),
        }
    }

    pub fn cross_exec(&self, axis: &Axis) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model@.cross_dim(*axis),
    {
        match axis {
            Axis::Vertical => self.width.copy(),
            Axis::Horizontal => self.height.copy(),
        }
    }

    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out ==> (self.model@.width.eqv(rhs.model@.width) && self.model@.height.eqv(rhs.model@.height)),
    {
        self.width.eq(&rhs.width) && self.height.eq(&rhs.height)
    }

    pub fn from_axes_exec(axis: &Axis, main: R, cross: R) -> (out: Self)
        requires main.wf_spec(), cross.wf_spec(),
        ensures out.wf_spec(), out.model@ == Size::<V>::from_axes(*axis, main.model(), cross.model()),
    {
        match axis {
            Axis::Vertical => RuntimeSize::new(cross, main),
            Axis::Horizontal => RuntimeSize::new(main, cross),
        }
    }
}

//  Concrete Rational-specific methods (normalize, zero_exec static).
impl RuntimeSize<RuntimeRational, Rational> {
    pub fn zero_exec() -> (out: Self)
        ensures out.wf_spec(), out@ == Size::<Rational>::zero_size(),
    {
        let ghost model = Size::<Rational>::zero_size();
        RuntimeSize { width: RuntimeRational::from_int(0), height: RuntimeRational::from_int(0), model: Ghost(model) }
    }

    pub fn normalize_exec(self) -> (out: Self)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out@.width.eqv_spec(self@.width),
            out@.height.eqv_spec(self@.height),
            out@.width.normalized_spec(),
            out@.height.normalized_spec(),
    {
        let w = self.width.normalize();
        let h = self.height.normalize();
        RuntimeSize::new(w, h)
    }
}

} //  verus!
