use vstd::prelude::*;
use verus_rational::RuntimeRational;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::partial_order::PartialOrder;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::RuntimeWidget;
use crate::runtime::widget::layout_widget_exec;
use crate::runtime::measure::measure_widget_exec;
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;
use crate::layout::*;
use crate::layout::listview::*;
use crate::measure::measure_children;

verus! {

/// Layout a ListView widget at runtime.
///
/// 1. Measure all children to get their heights
/// 2. Scan for visible range [first, end) using cumulative heights
/// 3. Layout only visible children
/// 4. Position visible children at (0, child_y(i) - scroll_y)
/// 5. Return limits.resolve(viewport)
pub fn layout_listview_widget_exec(
    limits: &RuntimeLimits,
    spacing: &RuntimeRational,
    scroll_y: &RuntimeRational,
    viewport: &RuntimeSize,
    children: &Vec<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeNode)
    requires
        limits.wf_spec(),
        spacing.wf_spec(),
        scroll_y.wf_spec(),
        viewport.wf_spec(),
        fuel > 0,
        forall|i: int| 0 <= i < children@.len() ==>
            (#[trigger] children@[i]).wf_spec((fuel - 1) as nat),
    ensures
        out.wf_spec(),
        out@ == ({
            let spec_wc = Seq::new(children@.len() as nat, |i: int| children@[i].model());
            let spec_w = Widget::ListView {
                spacing: spacing@,
                scroll_y: scroll_y@,
                viewport: viewport@,
                children: spec_wc,
            };
            layout_widget::<RationalModel>(limits@, spec_w, fuel as nat)
        }),
    decreases fuel, 0nat,
{
    proof { reveal(layout_listview_body); }
    let n = children.len();

    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(children@.len() as nat, |j: int| children@[j].model());

    // Child limits: (zero, Size(viewport.width, viewport.height))
    let child_min = RuntimeSize::zero_exec();
    let child_max = RuntimeSize::new(
        copy_rational(&viewport.width),
        copy_rational(&viewport.height),
    );
    let child_limits = RuntimeLimits::new(child_min, child_max);

    let ghost spec_child_limits = Limits::<RationalModel> {
        min: Size::zero_size(),
        max: Size::new(viewport@.width, viewport@.height),
    };

    // Step 1: Measure all children to get their sizes
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut mi: usize = 0;

    while mi < n
        invariant
            0 <= mi <= n,
            n == children@.len(),
            child_limits.wf_spec(),
            child_limits@ == spec_child_limits,
            fuel > 0,
            child_sizes@.len() == mi as int,
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] children@[j]).model(),
            forall|j: int| 0 <= j < mi ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == crate::measure::measure_widget::<RationalModel>(
                        spec_child_limits, spec_wc[j], (fuel - 1) as nat)
            },
        decreases n - mi,
    {
        let cs = measure_widget_exec(&child_limits, &children[mi], fuel - 1);
        child_sizes.push(cs);
        mi = mi + 1;
    }

    let ghost spec_sizes: Seq<Size<RationalModel>> =
        measure_children::<RationalModel>(spec_child_limits, spec_wc, (fuel - 1) as nat);

    proof {
        let computed_sizes = Seq::new(child_sizes@.len() as nat, |j: int| child_sizes@[j]@);
        assert(computed_sizes.len() == spec_sizes.len());
        assert forall|j: int| 0 <= j < computed_sizes.len() implies
            computed_sizes[j] == spec_sizes[j]
        by {}
        assert(computed_sizes =~= spec_sizes);
    }

    // Step 2: Find first visible index via linear scan
    let scroll_bottom = scroll_y.add(&viewport.height);
    let mut first: usize = 0;
    let mut cur_y = RuntimeRational::from_int(0);
    let mut first_visible_at_cur: bool = false;

    while first < n && !first_visible_at_cur
        invariant
            0 <= first <= n,
            n == children@.len(),
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            spacing.wf_spec(),
            scroll_y.wf_spec(),
            viewport.wf_spec(),
            scroll_bottom.wf_spec(),
            scroll_bottom@ == scroll_y@.add_spec(viewport@.height),
            cur_y.wf_spec(),
            cur_y@ == listview_child_y::<RationalModel>(spec_sizes, spacing@, first as nat),
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> child_sizes@[j]@ == spec_sizes[j],
            // All items before first are NOT visible (bottom <= scroll_y)
            forall|k: nat| k < first as nat ==>
                !scroll_y@.lt(listview_child_bottom::<RationalModel>(spec_sizes, spacing@, k)),
            // If we found a visible one, record it
            first_visible_at_cur ==> (first < n && scroll_y@.lt(
                listview_child_bottom::<RationalModel>(spec_sizes, spacing@, first as nat))),
        decreases n - first, (if first_visible_at_cur { 0int } else { 1int }),
    {
        let child_h = copy_rational(&child_sizes[first].height);
        let bottom = cur_y.add(&child_h);

        proof {
            assert(child_sizes@[first as int]@ == spec_sizes[first as int]);
            assert(child_h@ == spec_sizes[first as int].height);
            assert(bottom@ == listview_child_bottom::<RationalModel>(spec_sizes, spacing@, first as nat));
        }

        if scroll_y.lt(&bottom) {
            first_visible_at_cur = true;
        } else {
            // Advance: next y = bottom + spacing
            cur_y = bottom.add(spacing);
            first = first + 1;
        }
    }

    proof {
        // After loop: first == n (no visible) or first_visible_at_cur
        if first_visible_at_cur {
            assert(scroll_y@.lt(listview_child_bottom::<RationalModel>(spec_sizes, spacing@, first as nat)));
        }
        lemma_first_visible_loop_matches::<RationalModel>(spec_sizes, spacing@, scroll_y@, first as nat);
    }

    // Step 3: Find end visible index via linear scan
    let mut end: usize = 0;
    let mut end_y = RuntimeRational::from_int(0);
    let mut end_past_visible: bool = false;

    while end < n && !end_past_visible
        invariant
            0 <= end <= n,
            n == children@.len(),
            n == child_sizes@.len(),
            spec_sizes.len() == n as nat,
            spacing.wf_spec(),
            scroll_y.wf_spec(),
            viewport.wf_spec(),
            scroll_bottom.wf_spec(),
            scroll_bottom@ == scroll_y@.add_spec(viewport@.height),
            end_y.wf_spec(),
            end_y@ == listview_child_y::<RationalModel>(spec_sizes, spacing@, end as nat),
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> child_sizes@[j]@ == spec_sizes[j],
            // All items before end have top < scroll_bottom
            forall|k: nat| k < end as nat ==>
                !scroll_y@.add_spec(viewport@.height).le_spec(
                    listview_child_y::<RationalModel>(spec_sizes, spacing@, k)),
            end_past_visible ==> (end < n && scroll_y@.add_spec(viewport@.height).le_spec(
                listview_child_y::<RationalModel>(spec_sizes, spacing@, end as nat))),
        decreases n - end, (if end_past_visible { 0int } else { 1int }),
    {
        if scroll_bottom.le(&end_y) {
            end_past_visible = true;
        } else {
            // Advance
            let child_h = copy_rational(&child_sizes[end].height);
            end_y = end_y.add(&child_h).add(spacing);
            end = end + 1;
        }
    }

    proof {
        if end_past_visible {
            assert(scroll_y@.add_spec(viewport@.height).le_spec(
                listview_child_y::<RationalModel>(spec_sizes, spacing@, end as nat)));
        }
        lemma_end_visible_loop_matches::<RationalModel>(spec_sizes, spacing@, scroll_y@, viewport@.height, end as nat);
    }

    // Step 4: Layout visible children
    let count: usize = if end >= first { end - first } else { 0 };
    let mut visible_nodes: Vec<RuntimeNode> = Vec::new();
    let mut vi: usize = 0;

    while vi < count
        invariant
            0 <= vi <= count,
            count == (if end >= first { end - first } else { 0 }),
            first <= n,
            end <= n,
            n == children@.len(),
            child_limits.wf_spec(),
            child_limits@ == spec_child_limits,
            fuel > 0,
            visible_nodes@.len() == vi as int,
            forall|j: int| 0 <= j < children@.len() ==>
                (#[trigger] children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] children@[j]).model(),
            forall|j: int| 0 <= j < vi ==> {
                &&& (#[trigger] visible_nodes@[j]).wf_spec()
                &&& visible_nodes@[j]@ == layout_widget::<RationalModel>(
                        spec_child_limits, spec_wc[(first + j) as int], (fuel - 1) as nat)
            },
        decreases count - vi,
    {
        let child_idx = first + vi;
        let cn = layout_widget_exec(&child_limits, &children[child_idx], fuel - 1);
        visible_nodes.push(cn);
        vi = vi + 1;
    }

    // Step 5: Build positioned children
    let mut positioned: Vec<RuntimeNode> = Vec::new();
    let mut k: usize = 0;

    // Compute child_y(first) by accumulation
    let mut pos_y = RuntimeRational::from_int(0);
    {
        let mut fi: usize = 0;
        while fi < first
            invariant
                0 <= fi <= first,
                first <= n,
                n == child_sizes@.len(),
                spacing.wf_spec(),
                pos_y.wf_spec(),
                pos_y@ == listview_child_y::<RationalModel>(spec_sizes, spacing@, fi as nat),
                forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
                forall|j: int| 0 <= j < n ==> child_sizes@[j]@ == spec_sizes[j],
            decreases first - fi,
        {
            let h = copy_rational(&child_sizes[fi].height);
            pos_y = pos_y.add(&h).add(spacing);
            fi = fi + 1;
        }
    }

    let ghost spec_first = listview_first_visible::<RationalModel>(spec_sizes, spacing@, scroll_y@);
    let ghost spec_end = listview_end_visible::<RationalModel>(spec_sizes, spacing@, scroll_y@, viewport@.height);
    let ghost spec_cn = listview_widget_child_nodes::<RationalModel>(
        spec_child_limits, spec_wc, spec_first, spec_end, (fuel - 1) as nat);

    while k < count
        invariant
            0 <= k <= count,
            count == (if end >= first { end - first } else { 0 }),
            first <= n,
            end <= n,
            n == children@.len(),
            n == child_sizes@.len(),
            spacing.wf_spec(),
            scroll_y.wf_spec(),
            viewport.wf_spec(),
            pos_y.wf_spec(),
            pos_y@ == listview_child_y::<RationalModel>(spec_sizes, spacing@, (first + k) as nat),
            visible_nodes@.len() == count as int,
            positioned@.len() == k as int,
            first as nat == spec_first,
            end as nat == spec_end,
            forall|j: int| 0 <= j < n ==> (#[trigger] child_sizes@[j]).wf_spec(),
            forall|j: int| 0 <= j < n ==> child_sizes@[j]@ == spec_sizes[j],
            forall|j: int| 0 <= j < count ==> {
                &&& (#[trigger] visible_nodes@[j]).wf_spec()
                &&& visible_nodes@[j]@ == layout_widget::<RationalModel>(
                        spec_child_limits, spec_wc[(first + j) as int], (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < k ==> {
                &&& (#[trigger] positioned@[j]).wf_shallow()
                &&& positioned@[j]@ == Node::<RationalModel> {
                    x: RationalModel::from_int_spec(0),
                    y: listview_child_y::<RationalModel>(spec_sizes, spacing@, (first + j) as nat)
                        .sub_spec(scroll_y@),
                    size: visible_nodes@[j]@.size,
                    children: visible_nodes@[j]@.children,
                }
            },
        decreases count - k,
    {
        let child_y_offset = pos_y.sub(scroll_y);
        let x = RuntimeRational::from_int(0);
        let child_size = visible_nodes[k].size.copy_size();

        let ghost child_spec_node = layout_widget::<RationalModel>(
            spec_child_limits, spec_wc[(first + k) as int], (fuel - 1) as nat);

        let positioned_child = RuntimeNode {
            x,
            y: child_y_offset,
            size: child_size,
            children: Vec::new(),
            model: Ghost(Node::<RationalModel> {
                x: RationalModel::from_int_spec(0),
                y: listview_child_y::<RationalModel>(spec_sizes, spacing@, (first + k) as nat)
                    .sub_spec(scroll_y@),
                size: child_spec_node.size,
                children: child_spec_node.children,
            }),
        };

        proof {
            assert(positioned_child.wf_shallow());
        }

        positioned.push(positioned_child);

        // Advance pos_y
        let h = copy_rational(&child_sizes[first + k].height);
        pos_y = pos_y.add(&h).add(spacing);
        k = k + 1;
    }

    // Step 6: Build the parent node
    let resolved = limits.resolve_exec(viewport.copy_size());
    let px = RuntimeRational::from_int(0);
    let py = RuntimeRational::from_int(0);

    let ghost parent_model = layout_widget::<RationalModel>(
        limits@,
        Widget::ListView {
            spacing: spacing@,
            scroll_y: scroll_y@,
            viewport: viewport@,
            children: spec_wc,
        },
        fuel as nat,
    );

    let out = RuntimeNode {
        x: px,
        y: py,
        size: resolved,
        children: positioned,
        model: Ghost(parent_model),
    };

    proof {
        assert(spec_first == first as nat);
        assert(spec_end == end as nat);
        assert(spec_cn.len() == count as nat);
        assert(out.children@.len() == parent_model.children.len());

        assert forall|j: int| 0 <= j < out.children@.len() implies
            (#[trigger] out.children@[j]).wf_shallow() &&
            out.children@[j]@ == out@.children[j]
        by {
            assert(positioned@[j].wf_shallow());
        }
    }

    out
}

// ── Loop-to-spec correspondence helpers ──────────────────────────────

/// The imperative first-visible loop matches the recursive spec.
proof fn lemma_first_visible_loop_matches<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    result: nat,
)
    requires
        result <= child_sizes.len(),
        // All items before `result` have bottom <= scroll_y
        forall|k: nat| k < result ==>
            !scroll_y.lt(listview_child_bottom(child_sizes, spacing, k)),
        // Either result == total, or result's bottom > scroll_y
        result < child_sizes.len() ==>
            scroll_y.lt(listview_child_bottom(child_sizes, spacing, result)),
    ensures
        result == listview_first_visible(child_sizes, spacing, scroll_y),
    decreases child_sizes.len(),
{
    lemma_first_visible_from_loop_matches(child_sizes, spacing, scroll_y, result, 0);
}

proof fn lemma_first_visible_from_loop_matches<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    result: nat,
    from: nat,
)
    requires
        from <= result,
        result <= child_sizes.len(),
        forall|k: nat| from <= k && k < result ==>
            !scroll_y.lt(listview_child_bottom(child_sizes, spacing, k)),
        result < child_sizes.len() ==>
            scroll_y.lt(listview_child_bottom(child_sizes, spacing, result)),
    ensures
        result == listview_first_visible_from(child_sizes, spacing, scroll_y, from),
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        // result must be child_sizes.len()
    } else if scroll_y.lt(listview_child_bottom(child_sizes, spacing, from)) {
        // from is the first visible => result == from
    } else {
        lemma_first_visible_from_loop_matches(child_sizes, spacing, scroll_y, result, from + 1);
    }
}

/// The imperative end-visible loop matches the recursive spec.
proof fn lemma_end_visible_loop_matches<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
    result: nat,
)
    requires
        result <= child_sizes.len(),
        // All items before `result` have top < scroll_bottom
        forall|k: nat| k < result ==>
            !scroll_y.add(viewport_h).le(listview_child_y(child_sizes, spacing, k)),
        // Either result == total, or result's top >= scroll_bottom
        result < child_sizes.len() ==>
            scroll_y.add(viewport_h).le(listview_child_y(child_sizes, spacing, result)),
    ensures
        result == listview_end_visible(child_sizes, spacing, scroll_y, viewport_h),
    decreases child_sizes.len(),
{
    lemma_end_visible_from_loop_matches(child_sizes, spacing, scroll_y, viewport_h, result, 0);
}

proof fn lemma_end_visible_from_loop_matches<T: OrderedRing>(
    child_sizes: Seq<Size<T>>,
    spacing: T,
    scroll_y: T,
    viewport_h: T,
    result: nat,
    from: nat,
)
    requires
        from <= result,
        result <= child_sizes.len(),
        forall|k: nat| from <= k && k < result ==>
            !scroll_y.add(viewport_h).le(listview_child_y(child_sizes, spacing, k)),
        result < child_sizes.len() ==>
            scroll_y.add(viewport_h).le(listview_child_y(child_sizes, spacing, result)),
    ensures
        result == listview_end_visible_from(child_sizes, spacing, scroll_y, viewport_h, from),
    decreases child_sizes.len() - from,
{
    if from >= child_sizes.len() {
        // result must be child_sizes.len()
    } else {
        let scroll_bottom = scroll_y.add(viewport_h);
        if scroll_bottom.le(listview_child_y(child_sizes, spacing, from)) {
            // from is the end => result == from
        } else {
            lemma_end_visible_from_loop_matches(child_sizes, spacing, scroll_y, viewport_h, result, from + 1);
        }
    }
}

} // verus!
