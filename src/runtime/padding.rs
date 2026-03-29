use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::padding::Padding;
use crate::layout::Axis;

verus! {

///  Runtime-backed Padding with rational coordinates.
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
    ///  Well-formedness.
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

    ///  Construct from four sides.
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

    ///  Check semantic equality of two paddings.
    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out ==> (
                self@.top.eqv_spec(rhs@.top) &&
                self@.right.eqv_spec(rhs@.right) &&
                self@.bottom.eqv_spec(rhs@.bottom) &&
                self@.left.eqv_spec(rhs@.left)
            ),
    {
        self.top.eq(&rhs.top) && self.right.eq(&rhs.right) &&
        self.bottom.eq(&rhs.bottom) && self.left.eq(&rhs.left)
    }

    ///  Compute horizontal padding (left + right).
    pub fn horizontal_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.horizontal(),
    {
        self.left.add(&self.right)
    }

    ///  Compute vertical padding (top + bottom).
    pub fn vertical_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.vertical(),
    {
        self.top.add(&self.bottom)
    }

    ///  Main-axis padding at runtime.
    pub fn main_padding_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.main_padding(*axis),
    {
        match axis {
            Axis::Vertical => self.vertical_exec(),
            Axis::Horizontal => self.horizontal_exec(),
        }
    }

    ///  Cross-axis padding at runtime.
    pub fn cross_padding_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.cross_padding(*axis),
    {
        match axis {
            Axis::Vertical => self.horizontal_exec(),
            Axis::Horizontal => self.vertical_exec(),
        }
    }

    ///  Main-axis start padding at runtime.
    pub fn main_start_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.main_start(*axis),
    {
        match axis {
            Axis::Vertical => copy_rational(&self.top),
            Axis::Horizontal => copy_rational(&self.left),
        }
    }

    ///  Cross-axis start padding at runtime.
    pub fn cross_start_exec(&self, axis: &Axis) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.cross_start(*axis),
    {
        match axis {
            Axis::Vertical => copy_rational(&self.left),
            Axis::Horizontal => copy_rational(&self.top),
        }
    }

    ///  Normalize all rational fields.
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
        let t = self.top.normalize();
        let r = self.right.normalize();
        let b = self.bottom.normalize();
        let l = self.left.normalize();
        RuntimePadding {
            top: t, right: r, bottom: b, left: l,
            model: Ghost(Padding { top: t@, right: r@, bottom: b@, left: l@ }),
        }
    }
}

} //  verus!
