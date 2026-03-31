use vstd::prelude::*;
use crate::runtime::size::RuntimeSize;
use crate::size::Size;
use crate::layout::child_y_position;
use crate::scroll::child_visible;

use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;

verus! {

///  Whether child i is visible, using add_spec/lt_spec directly (avoids trait method resolution).
pub open spec fn runtime_child_visible_at<V: OrderedField>(
    padding_top: V,
    spec_sizes: Seq<Size<V>>,
    spacing: V,
    i: nat,
    scroll_y: V,
    viewport_h: V,
) -> bool {
    let y_pos = child_y_position(padding_top, spec_sizes, spacing, i);
    let bottom = y_pos.add(spec_sizes[i as int].height);
    let scroll_bottom = scroll_y.add(viewport_h);
    scroll_y.lt(bottom) && y_pos.lt(scroll_bottom)
}

///  Compute the visible range [first, end) for a column's children
///  given scroll position and viewport height.
///
///  Two-phase scan: first pass finds the first visible child,
///  second pass extends until non-visible (contiguous range).
pub fn visible_range_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    padding_top: &R,
    child_sizes: &Vec<RuntimeSize<R, V>>,
    spacing: &R,
    scroll_y: &R,
    viewport_h: &R,
) -> (out: (usize, usize))
    requires
        padding_top.wf_spec(),
        spacing.wf_spec(),
        scroll_y.wf_spec(),
        viewport_h.wf_spec(),
        forall|i: int| 0 <= i < child_sizes@.len() ==>
            (#[trigger] child_sizes@[i]).wf_spec(),
    ensures ({
        let spec_sizes = Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        let (first, end) = out;
        &&& first <= end
        &&& end <= child_sizes@.len()
        &&& forall|i: nat| first as nat <= i && i < end as nat ==>
            #[trigger] runtime_child_visible_at(
                padding_top@, spec_sizes, spacing@, i, scroll_y@, viewport_h@,
            )
    }),
{
    let n = child_sizes.len();
    if n == 0 {
        return (0, 0);
    }

    let ghost spec_sizes: Seq<Size<V>> =
        Seq::new(n as nat, |j: int| child_sizes@[j]@);

    let scroll_bottom = scroll_y.add(viewport_h);

    //  Phase 1: find the first visible child
    let mut y_pos = padding_top.copy();
    let mut first: usize = 0;

    while first < n
        invariant
            0 <= first <= n,
            n == child_sizes@.len(),
            padding_top.wf_spec(),
            spacing.wf_spec(),
            scroll_y.wf_spec(),
            viewport_h.wf_spec(),
            scroll_bottom.wf_spec(),
            scroll_bottom@ == scroll_y@.add(viewport_h@),
            y_pos.wf_spec(),
            y_pos@ == child_y_position(padding_top@, spec_sizes, spacing@, first as nat),
            forall|i: int| 0 <= i < child_sizes@.len() ==>
                (#[trigger] child_sizes@[i]).wf_spec(),
            forall|j: int| 0 <= j < n ==>
                (#[trigger] spec_sizes[j]) == child_sizes@[j]@,
            spec_sizes.len() == n,
        decreases n - first,
    {
        assert(child_sizes@[first as int].wf_spec());
        let child_h = child_sizes[first].height.copy();
        let bottom = y_pos.add(&child_h);

        if scroll_y.lt(&bottom) && y_pos.lt(&scroll_bottom) {
            //  Found first visible child.
            //  Phase 2: extend from first, tracking visibility
            proof {
                assert(spec_sizes[first as int] == child_sizes@[first as int]@);
                assert(child_h@ == spec_sizes[first as int].height);
                assert(runtime_child_visible_at(
                    padding_top@, spec_sizes, spacing@, first as nat, scroll_y@, viewport_h@));
            }

            let mut y_pos2 = y_pos.add(&child_h).add(spacing);
            let mut end: usize = first + 1;
            proof {
                assert(spec_sizes[first as int] == child_sizes@[first as int]@);
            }

            while end < n
                invariant
                    first < end,
                    end <= n,
                    n == child_sizes@.len(),
                    padding_top.wf_spec(),
                    spacing.wf_spec(),
                    scroll_y.wf_spec(),
                    viewport_h.wf_spec(),
                    scroll_bottom.wf_spec(),
                    scroll_bottom@ == scroll_y@.add(viewport_h@),
                    y_pos2.wf_spec(),
                    y_pos2@ == child_y_position(padding_top@, spec_sizes, spacing@, end as nat),
                    forall|i: int| 0 <= i < child_sizes@.len() ==>
                        (#[trigger] child_sizes@[i]).wf_spec(),
                    forall|j: int| 0 <= j < n ==>
                        (#[trigger] spec_sizes[j]) == child_sizes@[j]@,
                    spec_sizes.len() == n,
                    forall|i: nat| first as nat <= i && i < end as nat ==>
                        #[trigger] runtime_child_visible_at(
                            padding_top@, spec_sizes, spacing@, i, scroll_y@, viewport_h@),
                decreases n - end,
            {
                assert(child_sizes@[end as int].wf_spec());
                let child_h2 = child_sizes[end].height.copy();
                let bottom2 = y_pos2.add(&child_h2);

                if !(scroll_y.lt(&bottom2) && y_pos2.lt(&scroll_bottom)) {
                    break;
                }

                proof {
                    assert(spec_sizes[end as int] == child_sizes@[end as int]@);
                    assert(child_h2@ == spec_sizes[end as int].height);
                    assert(runtime_child_visible_at(
                        padding_top@, spec_sizes, spacing@, end as nat, scroll_y@, viewport_h@));
                }

                let y_next = y_pos2.add(&child_h2).add(spacing);
                proof {
                    assert(spec_sizes[end as int] == child_sizes@[end as int]@);
                }
                y_pos2 = y_next;
                end = end + 1;
            }

            proof {
                //  Connect ghost spec_sizes to the ensures-level Seq::new
                let ensures_sizes = Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
                assert(spec_sizes =~= ensures_sizes);
            }
            return (first, end);
        }

        //  Not visible: advance
        let y_next = y_pos.add(&child_h).add(spacing);
        proof {
            assert(spec_sizes[first as int] == child_sizes@[first as int]@);
        }
        y_pos = y_next;
        first = first + 1;
    }

    //  No visible children
    (0, 0)
}

} //  verus!
