use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
pub type RationalModel = Rational;

pub mod size;
pub mod limits;
pub mod padding;
pub mod node;
pub mod column;
pub mod row;
pub mod stack;
pub mod flex;
pub mod grid;
pub mod wrap;
pub mod absolute;
pub mod widget;
pub mod widget_sized_box;
pub mod widget_margin;
pub mod widget_aspect_ratio;
pub mod widget_scroll;
pub mod widget_grid;
pub mod widget_absolute;
pub mod measure;
pub mod hit_test;
pub mod diff;
pub mod animation;
pub mod scroll;
pub mod listview;
pub mod event;
pub mod interaction;
pub mod text_model;
pub mod session;
pub mod text_input;
pub mod event_routing;

verus! {

/// Copy a RuntimeRational (needed because BigInt witnesses don't implement Copy).
pub fn copy_rational(r: &RuntimeRational) -> (out: RuntimeRational)
    requires
        r.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == r@,
{
    let num_copy = r.numerator.copy_small_total();
    let den_copy = r.denominator.copy_small_total();
    RuntimeRational {
        numerator: num_copy,
        denominator: den_copy,
        model: Ghost(r@),
    }
}

} // verus!
