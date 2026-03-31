use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::size::RuntimeSize;
use crate::limits::Limits;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

verus! {

pub struct RuntimeLimits<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub min: RuntimeSize<R, V>,
    pub max: RuntimeSize<R, V>,
    pub model: Ghost<Limits<V>>,
}

impl View for RuntimeLimits<RuntimeRational, Rational> {
    type V = Limits<Rational>;
    open spec fn view(&self) -> Limits<Rational> { self.model@ }
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimeLimits<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min.wf_spec()
        &&& self.max.wf_spec()
        &&& self.min.model@ == self.model@.min
        &&& self.max.model@ == self.model@.max
    }

    pub fn new(min: RuntimeSize<R, V>, max: RuntimeSize<R, V>) -> (out: Self)
        requires min.wf_spec(), max.wf_spec(),
        ensures out.wf_spec(), out.model@.min == min.model@, out.model@.max == max.model@,
    {
        let ghost model = Limits { min: min.model@, max: max.model@ };
        RuntimeLimits { min, max, model: Ghost(model) }
    }

    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out ==> (
            self.model@.min.width.eqv(rhs.model@.min.width) &&
            self.model@.min.height.eqv(rhs.model@.min.height) &&
            self.model@.max.width.eqv(rhs.model@.max.width) &&
            self.model@.max.height.eqv(rhs.model@.max.height)
        ),
    {
        self.min.eq_exec(&rhs.min) && self.max.eq_exec(&rhs.max)
    }

    pub fn resolve_exec(&self, size: RuntimeSize<R, V>) -> (out: RuntimeSize<R, V>)
        requires self.wf_spec(), size.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.resolve(size.model@),
    {
        let w = self.min.width.max(&size.width.min(&self.max.width));
        let h = self.min.height.max(&size.height.min(&self.max.height));
        RuntimeSize::new(w, h)
    }

    pub fn intersect_exec(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.intersect(other.model@),
    {
        let new_min_w = self.min.width.max(&other.min.width);
        let new_min_h = self.min.height.max(&other.min.height);
        let new_max_w = new_min_w.max(&self.max.width.min(&other.max.width));
        let new_max_h = new_min_h.max(&self.max.height.min(&other.max.height));
        RuntimeLimits::new(
            RuntimeSize::new(new_min_w, new_min_h),
            RuntimeSize::new(new_max_w, new_max_h),
        )
    }

    pub fn shrink_exec(&self, pad_w: &R, pad_h: &R) -> (out: Self)
        requires self.wf_spec(), pad_w.wf_spec(), pad_h.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.shrink(pad_w.model(), pad_h.model()),
    {
        let new_max_w = self.min.width.max(&self.max.width.sub(pad_w));
        let new_max_h = self.min.height.max(&self.max.height.sub(pad_h));
        RuntimeLimits::new(self.min.copy_size(), RuntimeSize::new(new_max_w, new_max_h))
    }
}

impl RuntimeLimits<RuntimeRational, Rational> {
    pub fn normalize_exec(self) -> (out: Self)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out@.min.width.eqv_spec(self@.min.width),
            out@.min.height.eqv_spec(self@.min.height),
            out@.max.width.eqv_spec(self@.max.width),
            out@.max.height.eqv_spec(self@.max.height),
            out@.min.width.normalized_spec(),
            out@.min.height.normalized_spec(),
            out@.max.width.normalized_spec(),
            out@.max.height.normalized_spec(),
    {
        RuntimeLimits::new(self.min.normalize_exec(), self.max.normalize_exec())
    }
}

} //  verus!
