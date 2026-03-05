use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::limits::Limits;

verus! {

/// Runtime-backed Limits with rational coordinates.
pub struct RuntimeLimits {
    pub min: RuntimeSize,
    pub max: RuntimeSize,
    pub model: Ghost<Limits<RationalModel>>,
}

impl View for RuntimeLimits {
    type V = Limits<RationalModel>;

    open spec fn view(&self) -> Limits<RationalModel> {
        self.model@
    }
}

impl RuntimeLimits {
    /// Well-formedness.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min.wf_spec()
        &&& self.max.wf_spec()
        &&& self.min@ == self@.min
        &&& self.max@ == self@.max
    }

    /// Construct RuntimeLimits from min and max sizes.
    pub fn new(min: RuntimeSize, max: RuntimeSize) -> (out: Self)
        requires
            min.wf_spec(),
            max.wf_spec(),
        ensures
            out.wf_spec(),
            out@.min == min@,
            out@.max == max@,
    {
        let ghost model = Limits { min: min@, max: max@ };
        RuntimeLimits { min, max, model: Ghost(model) }
    }

    /// Resolve a desired size within these limits (clamp each dimension).
    pub fn resolve_exec(&self, size: RuntimeSize) -> (out: RuntimeSize)
        requires
            self.wf_spec(),
            size.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.resolve(size@),
    {
        let w = self.min.width.max(&size.width.min(&self.max.width));
        let h = self.min.height.max(&size.height.min(&self.max.height));
        RuntimeSize::new(w, h)
    }

    /// Shrink limits by subtracting padding from the max (min unchanged).
    pub fn shrink_exec(&self, pad_w: &RuntimeRational, pad_h: &RuntimeRational) -> (out: Self)
        requires
            self.wf_spec(),
            pad_w.wf_spec(),
            pad_h.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.shrink(pad_w@, pad_h@),
    {
        let new_max_w = self.min.width.max(&self.max.width.sub(pad_w));
        let new_max_h = self.min.height.max(&self.max.height.sub(pad_h));
        let new_min = self.min.copy_size();
        let new_max = RuntimeSize::new(new_max_w, new_max_h);
        RuntimeLimits::new(new_min, new_max)
    }
}

} // verus!
