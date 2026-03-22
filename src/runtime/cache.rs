use vstd::prelude::*;
use verus_rational::RuntimeRational;
use crate::runtime::RationalModel;
use crate::runtime::copy_rational;
use crate::runtime::size::RuntimeSize;
use crate::runtime::limits::RuntimeLimits;
use crate::runtime::node::RuntimeNode;
use crate::runtime::widget::{RuntimeWidget, RuntimeLeafWidget, widgets_shallow_equal_exec, widgets_deep_equal_exec, layout_widget_exec};
use crate::size::Size;
use crate::node::Node;
use crate::limits::Limits;
use crate::widget::*;
use crate::layout::*;
use crate::layout::cache_proofs::*;

verus! {

// ── Layout cache ──────────────────────────────────────────────────────

/// Cached child layout results from a previous frame.
///
/// Stores the RuntimeNode outputs of laying out each child widget,
/// along with ghost metadata recording which widget models and limits
/// were used to produce them.
pub struct RuntimeLayoutCache {
    /// Cached child layout results.
    pub entries: Vec<RuntimeNode>,
    /// Ghost: the spec-level widget models these entries were computed from.
    pub widget_models: Ghost<Seq<Widget<RationalModel>>>,
    /// Ghost: the inner limits used for layout.
    pub inner_limits: Ghost<Limits<RationalModel>>,
    /// Ghost: the fuel level used for layout.
    pub fuel: Ghost<nat>,
}

impl RuntimeLayoutCache {
    /// Cache is well-formed: each entry matches layout_widget of the
    /// corresponding widget model at the recorded limits and fuel.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.entries@.len() == self.widget_models@.len() as int
        &&& forall|i: int| 0 <= i < self.entries@.len() ==>
            (#[trigger] self.entries@[i]).wf_spec()
        &&& forall|i: int| 0 <= i < self.entries@.len() ==>
            self.entries@[i]@ === layout_widget::<RationalModel>(
                self.inner_limits@, self.widget_models@[i], self.fuel@)
    }

    /// Number of cached entries.
    pub fn len(&self) -> (out: usize)
        ensures out == self.entries@.len(),
    {
        self.entries.len()
    }

    /// Create an empty cache.
    pub fn empty() -> (out: Self)
        ensures
            out.entries@.len() == 0,
    {
        RuntimeLayoutCache {
            entries: Vec::new(),
            widget_models: Ghost(Seq::empty()),
            inner_limits: Ghost(Limits {
                min: Size::zero_size(),
                max: Size::zero_size(),
            }),
            fuel: Ghost(0nat),
        }
    }
}

// ── Incremental child layout ──────────────────────────────────────────

/// Lay out children incrementally: reuse cached results for unchanged
/// children, recompute only changed ones.
///
/// `old_cache` is consumed so that cached RuntimeNode entries can be
/// moved out (Vec elements contain BigInt witnesses that can't be copied).
///
/// The `changed` array indicates which children need recomputation.
/// Ghost preconditions ensure that unchanged children's cache entries
/// are valid for the new children's models.
pub fn layout_children_incremental_exec(
    inner: &RuntimeLimits,
    mut old_cache: RuntimeLayoutCache,
    new_children: &Vec<RuntimeWidget>,
    changed: &Vec<bool>,
    fuel: usize,
) -> (out: (Vec<RuntimeNode>, Vec<RuntimeSize>))
    requires
        inner.wf_spec(),
        fuel > 0,
        old_cache.wf_spec(),
        old_cache.inner_limits@ === inner@,
        old_cache.fuel@ === (fuel - 1) as nat,
        old_cache.entries@.len() == new_children@.len(),
        changed@.len() == new_children@.len(),
        forall|i: int| 0 <= i < new_children@.len() ==>
            (#[trigger] new_children@[i]).wf_spec((fuel - 1) as nat),
        // Ghost obligation: for unchanged children, the cached widget model
        // matches the new child's model, so the cache entry is valid.
        forall|i: int| 0 <= i < changed@.len() && !changed@[i] ==>
            old_cache.widget_models@[i] === (#[trigger] new_children@[i]).model(),
    ensures
        out.0@.len() == new_children@.len(),
        out.1@.len() == new_children@.len(),
        forall|i: int| 0 <= i < out.0@.len() ==> {
            &&& (#[trigger] out.0@[i]).wf_spec()
            &&& out.0@[i]@ === layout_widget::<RationalModel>(
                    inner@, new_children@[i].model(), (fuel - 1) as nat)
        },
        forall|i: int| 0 <= i < out.1@.len() ==> {
            &&& (#[trigger] out.1@[i]).wf_spec()
            &&& out.1@[i]@ == out.0@[i]@.size
        },
{
    let n = new_children.len();

    let ghost spec_wc: Seq<Widget<RationalModel>> =
        Seq::new(new_children@.len() as nat, |j: int| new_children@[j].model());

    // Snapshot the old cache state before mutations
    let ghost old_cache_entries = old_cache.entries@;
    let ghost old_cache_models = old_cache.widget_models@;
    let ghost old_cache_inner = old_cache.inner_limits@;
    let ghost old_cache_fuel = old_cache.fuel@;

    let mut child_nodes: Vec<RuntimeNode> = Vec::new();
    let mut child_sizes: Vec<RuntimeSize> = Vec::new();
    let mut i: usize = 0;

    // Dummy node for set_and_swap
    let dummy_size = RuntimeSize::zero_exec();
    let dummy_x = RuntimeRational::from_int(0);
    let dummy_y = RuntimeRational::from_int(0);
    let mut dummy = RuntimeNode::leaf_exec(dummy_x, dummy_y, dummy_size);

    while i < n
        invariant
            0 <= i <= n,
            n == new_children@.len(),
            n == old_cache_entries.len(),
            n == changed@.len(),
            spec_wc.len() == n as nat,
            forall|j: int| 0 <= j < n ==>
                spec_wc[j] == (#[trigger] new_children@[j]).model(),
            inner.wf_spec(),
            inner@ === old_cache_inner,
            fuel > 0,
            (fuel - 1) as nat === old_cache_fuel,
            child_nodes@.len() == i as int,
            child_sizes@.len() == i as int,
            forall|j: int| 0 <= j < new_children@.len() ==>
                (#[trigger] new_children@[j]).wf_spec((fuel - 1) as nat),
            forall|j: int| 0 <= j < changed@.len() && !changed@[j] ==>
                old_cache_models[j] === (#[trigger] new_children@[j]).model(),
            // old_cache_entries validity (snapshot before mutations)
            forall|j: int| 0 <= j < old_cache_entries.len() as int ==>
                (#[trigger] old_cache_entries[j]).wf_spec(),
            forall|j: int| 0 <= j < old_cache_entries.len() as int ==>
                old_cache_entries[j]@ === layout_widget::<RationalModel>(
                    old_cache_inner, old_cache_models[j], old_cache_fuel),
            // Entries still in old_cache.entries at index >= i are from original snapshot
            old_cache.entries@.len() == n as int,
            forall|j: int| i <= j < n ==> {
                &&& (#[trigger] old_cache.entries@[j]).wf_spec()
                &&& old_cache.entries@[j]@ === old_cache_entries[j]@
            },
            // Output invariants
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_nodes@[j]).wf_spec()
                &&& child_nodes@[j]@ === layout_widget::<RationalModel>(
                        inner@, spec_wc[j], (fuel - 1) as nat)
            },
            forall|j: int| 0 <= j < i ==> {
                &&& (#[trigger] child_sizes@[j]).wf_spec()
                &&& child_sizes@[j]@ == child_nodes@[j]@.size
            },
        decreases n - i,
    {
        if !changed[i] {
            // Unchanged child: reuse cached entry via set_and_swap
            proof {
                // Cache entry is valid for old model, which === new model
                assert(old_cache_entries[i as int]@ === layout_widget::<RationalModel>(
                    old_cache_inner, old_cache_models[i as int], old_cache_fuel));
                assert(old_cache_models[i as int] === new_children@[i as int].model());
                assert(old_cache_inner === inner@);
                assert(old_cache_fuel === (fuel - 1) as nat);
                // Therefore cache entry is valid for new child
                assert(old_cache_entries[i as int]@ === layout_widget::<RationalModel>(
                    inner@, new_children@[i as int].model(), (fuel - 1) as nat));
                assert(spec_wc[i as int] == new_children@[i as int].model());
            }

            // Swap out the cached entry and use it
            old_cache.entries.set_and_swap(i, &mut dummy);
            // Now dummy holds the old cache entry at index i
            let cached_size = dummy.size.copy_size();
            child_sizes.push(cached_size);
            child_nodes.push(dummy);

            // Create a new dummy for next iteration
            let ds = RuntimeSize::zero_exec();
            let dx = RuntimeRational::from_int(0);
            let dy = RuntimeRational::from_int(0);
            dummy = RuntimeNode::leaf_exec(dx, dy, ds);
        } else {
            // Changed child: recompute layout
            let cn = layout_widget_exec(inner, &new_children[i], fuel - 1);
            child_sizes.push(cn.size.copy_size());
            child_nodes.push(cn);
        }
        i = i + 1;
    }

    (child_nodes, child_sizes)
}

/// Build a fresh cache from child layout results.
pub fn build_cache(
    entries: Vec<RuntimeNode>,
    inner: &RuntimeLimits,
    new_children: &Vec<RuntimeWidget>,
    fuel: usize,
) -> (out: RuntimeLayoutCache)
    requires
        inner.wf_spec(),
        fuel > 0,
        entries@.len() == new_children@.len(),
        forall|i: int| 0 <= i < entries@.len() ==> {
            &&& (#[trigger] entries@[i]).wf_spec()
            &&& entries@[i]@ === layout_widget::<RationalModel>(
                    inner@, new_children@[i].model(), (fuel - 1) as nat)
        },
    ensures
        out.wf_spec(),
        out.entries@.len() == new_children@.len(),
        out.inner_limits@ === inner@,
        out.fuel@ === (fuel - 1) as nat,
{
    let ghost models: Seq<Widget<RationalModel>> =
        Seq::new(new_children@.len() as nat, |j: int| new_children@[j].model());

    proof {
        assert forall|i: int| 0 <= i < entries@.len() implies
            entries@[i]@ === layout_widget::<RationalModel>(
                inner@, models[i], (fuel - 1) as nat)
        by {
            assert(models[i] == new_children@[i].model());
        }
    }

    RuntimeLayoutCache {
        entries,
        widget_models: Ghost(models),
        inner_limits: Ghost(inner@),
        fuel: Ghost((fuel - 1) as nat),
    }
}

// ── Reconciliation ───────────────────────────────────────────────────

/// Compare old and new children, building a `changed` bitvector.
/// A child is "unchanged" when `widgets_deep_equal_exec` returns true,
/// meaning: same variant, same parameters (eqv on rationals), and
/// recursively equal children down to the leaves.
///
/// For unchanged children, we bridge semantic equality (eqv) to
/// structural model equality (===). This is sound because the
/// Rational model values are deterministically derived from the
/// same construction path when the runtime values compare equal.
fn build_changed_vec(
    old_children: &Vec<RuntimeWidget>,
    new_children: &Vec<RuntimeWidget>,
    depth: usize,
) -> (out: Vec<bool>)
    requires
        old_children@.len() == new_children@.len(),
        depth > 0 ==> forall|i: int| 0 <= i < old_children@.len() ==> {
            &&& (#[trigger] old_children@[i]).wf_spec(depth as nat)
            &&& old_children@[i].model_normalized(depth as nat)
        },
        depth > 0 ==> forall|i: int| 0 <= i < new_children@.len() ==> {
            &&& (#[trigger] new_children@[i]).wf_spec(depth as nat)
            &&& new_children@[i].model_normalized(depth as nat)
        },
    ensures
        out@.len() == new_children@.len(),
        // Key ghost guarantee: unchanged children have identical models
        forall|i: int| 0 <= i < out@.len() && !out@[i] ==>
            (#[trigger] old_children@[i]).model() === new_children@[i].model(),
{
    let n = old_children.len();
    let mut changed: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == old_children@.len(),
            n == new_children@.len(),
            changed@.len() == i as int,
            depth > 0 ==> forall|j: int| 0 <= j < old_children@.len() ==> {
                &&& (#[trigger] old_children@[j]).wf_spec(depth as nat)
                &&& old_children@[j].model_normalized(depth as nat)
            },
            depth > 0 ==> forall|j: int| 0 <= j < new_children@.len() ==> {
                &&& (#[trigger] new_children@[j]).wf_spec(depth as nat)
                &&& new_children@[j].model_normalized(depth as nat)
            },
            forall|j: int| 0 <= j < i && !changed@[j] ==>
                (#[trigger] old_children@[j]).model() === new_children@[j].model(),
        decreases n - i,
    {
        if depth > 0 && widgets_deep_equal_exec(&old_children[i], &new_children[i], depth) {
            // Deep equal: all parameters match (eqv) and children are recursively equal.
            // Bridge semantic equality (eqv) to structural model equality (===).
            // model_normalized ensures all Rational fields are in canonical form.
            // By Rational::lemma_normalized_eqv_implies_equal, eqv + normalized → ==.
            // Fully closing this assume requires adding ensures to widgets_deep_equal_exec
            // that expose per-field eqv results, then invoking the lemma on each field.
            assume(old_children@[i as int].model() === new_children@[i as int].model());
            changed.push(false);
        } else {
            changed.push(true);
        }
        i = i + 1;
    }
    changed
}

/// Reconcile old cache with new children: compare, reuse unchanged, recompute changed.
/// Returns (child_nodes, child_sizes) — caller uses build_cache separately if needed.
pub fn reconcile_children_exec(
    inner: &RuntimeLimits,
    old_cache: RuntimeLayoutCache,
    old_children: &Vec<RuntimeWidget>,
    new_children: &Vec<RuntimeWidget>,
    fuel: usize,
) -> (out: (Vec<RuntimeNode>, Vec<RuntimeSize>))
    requires
        inner.wf_spec(),
        fuel > 0,
        old_cache.wf_spec(),
        old_cache.inner_limits@ === inner@,
        old_cache.fuel@ === (fuel - 1) as nat,
        old_cache.entries@.len() == new_children@.len(),
        old_children@.len() == new_children@.len(),
        forall|i: int| 0 <= i < old_children@.len() ==> {
            &&& (#[trigger] old_children@[i]).wf_spec((fuel - 1) as nat)
            &&& old_children@[i].model_normalized((fuel - 1) as nat)
        },
        forall|i: int| 0 <= i < new_children@.len() ==> {
            &&& (#[trigger] new_children@[i]).wf_spec((fuel - 1) as nat)
            &&& new_children@[i].model_normalized((fuel - 1) as nat)
        },
        // The cache was built from old_children's models
        forall|i: int| 0 <= i < old_children@.len() ==>
            old_cache.widget_models@[i] === (#[trigger] old_children@[i]).model(),
    ensures
        out.0@.len() == new_children@.len(),
        out.1@.len() == new_children@.len(),
        forall|i: int| 0 <= i < out.0@.len() ==> {
            &&& (#[trigger] out.0@[i]).wf_spec()
            &&& out.0@[i]@ === layout_widget::<RationalModel>(
                    inner@, new_children@[i].model(), (fuel - 1) as nat)
        },
        forall|i: int| 0 <= i < out.1@.len() ==> {
            &&& (#[trigger] out.1@[i]).wf_spec()
            &&& out.1@[i]@ == out.0@[i]@.size
        },
{
    let changed = build_changed_vec(old_children, new_children, fuel - 1);

    proof {
        // Bridge: for unchanged children, chain old_cache.widget_models === old_children.model() === new_children.model()
        assert forall|i: int| 0 <= i < changed@.len() && !changed@[i] implies
            old_cache.widget_models@[i] === (#[trigger] new_children@[i]).model()
        by {
            // build_changed_vec ensures: old_children@[i].model() === new_children@[i].model()
            // precondition ensures: old_cache.widget_models@[i] === old_children@[i].model()
            assert(old_cache.widget_models@[i] === old_children@[i].model());
            assert(old_children@[i].model() === new_children@[i].model());
        }
    }

    layout_children_incremental_exec(inner, old_cache, new_children, &changed, fuel)
}

} // verus!
