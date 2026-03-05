use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::padding::Padding;

verus! {

/// Runtime-backed Padding with rational coordinates.
pub struct RuntimePadding {
    pub top: RuntimeRational,
    pub right: RuntimeRational,
    pub bottom: RuntimeRational,
    pub left: RuntimeRational,
    pub model: Ghost<Padding<RationalModel>>,
}

impl View for RuntimePadding {
    type V = Padding<RationalModel>;

    open spec fn view(&self) -> Padding<RationalModel> {
        self.model@
    }
}

impl RuntimePadding {
    /// Well-formedness.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.top.wf_spec()
        &&& self.right.wf_spec()
        &&& self.bottom.wf_spec()
        &&& self.left.wf_spec()
        &&& self.top@ == self@.top
        &&& self.right@ == self@.right
        &&& self.bottom@ == self@.bottom
        &&& self.left@ == self@.left
    }

    /// Construct from four sides.
    pub fn new(
        top: RuntimeRational,
        right: RuntimeRational,
        bottom: RuntimeRational,
        left: RuntimeRational,
    ) -> (out: Self)
        requires
            top.wf_spec(),
            right.wf_spec(),
            bottom.wf_spec(),
            left.wf_spec(),
        ensures
            out.wf_spec(),
            out@.top == top@,
            out@.right == right@,
            out@.bottom == bottom@,
            out@.left == left@,
    {
        let ghost model = Padding { top: top@, right: right@, bottom: bottom@, left: left@ };
        RuntimePadding { top, right, bottom, left, model: Ghost(model) }
    }

    /// Compute horizontal padding (left + right).
    pub fn horizontal_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.horizontal(),
    {
        self.left.add(&self.right)
    }

    /// Compute vertical padding (top + bottom).
    pub fn vertical_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.vertical(),
    {
        self.top.add(&self.bottom)
    }
}

} // verus!
