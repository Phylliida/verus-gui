use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::size::Size;
use crate::layout::Axis;

verus! {

/// Runtime-backed Size with rational coordinates.
pub struct RuntimeSize {
    pub width: RuntimeRational,
    pub height: RuntimeRational,
    pub model: Ghost<Size<RationalModel>>,
}

impl View for RuntimeSize {
    type V = Size<RationalModel>;

    open spec fn view(&self) -> Size<RationalModel> {
        self.model@
    }
}

impl RuntimeSize {
    /// Well-formedness: runtime fields are valid and consistent with the model.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.width.wf_spec()
        &&& self.height.wf_spec()
        &&& self.width@ == self@.width
        &&& self.height@ == self@.height
    }

    /// Construct a RuntimeSize from width and height.
    pub fn new(width: RuntimeRational, height: RuntimeRational) -> (out: Self)
        requires
            width.wf_spec(),
            height.wf_spec(),
        ensures
            out.wf_spec(),
            out@.width == width@,
            out@.height == height@,
    {
        let ghost model = Size { width: width@, height: height@ };
        RuntimeSize { width, height, model: Ghost(model) }
    }

    /// The zero size.
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == Size::<RationalModel>::zero_size(),
    {
        let w = RuntimeRational::from_int(0);
        let h = RuntimeRational::from_int(0);
        let ghost model = Size::<RationalModel>::zero_size();
        RuntimeSize { width: w, height: h, model: Ghost(model) }
    }

    /// Copy this RuntimeSize (deep copy of rational fields).
    pub fn copy_size(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@,
    {
        RuntimeSize {
            width: copy_rational(&self.width),
            height: copy_rational(&self.height),
            model: Ghost(self@),
        }
    }

    /// Main-axis dimension at runtime.
    pub fn main_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.main_dim(*axis),
    {
        match axis {
            Axis::Vertical => copy_rational(&self.height),
            Axis::Horizontal => copy_rational(&self.width),
        }
    }

    /// Cross-axis dimension at runtime.
    pub fn cross_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.cross_dim(*axis),
    {
        match axis {
            Axis::Vertical => copy_rational(&self.width),
            Axis::Horizontal => copy_rational(&self.height),
        }
    }

    /// Construct a RuntimeSize from main-axis and cross-axis values.
    pub fn from_axes_exec(axis: &Axis, main: RuntimeRational, cross: RuntimeRational) -> (out: Self)
        requires
            main.wf_spec(),
            cross.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == Size::<RationalModel>::from_axes(*axis, main@, cross@),
    {
        match axis {
            Axis::Vertical => RuntimeSize::new(cross, main),
            Axis::Horizontal => RuntimeSize::new(main, cross),
        }
    }
}

} // verus!
