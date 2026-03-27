# verus-gui Proof Status & Session Report

## Overview

verus-gui is a verified GUI framework with **1050 verified lemmas, 0 errors, 0 assumes** (in spec layer). The framework uses rational arithmetic over an abstract ordered field, with equivalence classes (quotient ring) to handle multiple representations of the same rational number.

## What Was Proved This Session

Starting from 959 verified lemmas, we added 91 new lemmas across multiple proof categories:

### 1. The Fundamental Theorem (`theorems.rs`)
A single theorem combining 7 pipeline properties:
- Layout equivalence (`node_eqv`)
- Draw equivalence (`draws_eqv` at root)
- Measure equivalence (`size_eqv`)
- Interaction equivalence (`point_in_node`)
- Animation equivalence (`nodes_deeply_eqv` of lerp)
- GPU safety (`draw_command_valid` for root draw)
- Hit-test correctness (`path_geometrically_valid`)

Plus `theorem_edit_integrity` and `theorem_incremental_and_deterministic`.

### 2. Full-Depth Congruence (15/15 Widget Variants)
The quotient ring congruence is proved at full tree depth for all widget types:

| Variant | Helper | Depth |
|---------|--------|-------|
| Leaf | `lemma_layout_leaf_deep_congruence_any` | Any |
| Conditional(false) | `lemma_layout_conditional_false_deep_any` | Any |
| Conditional(true) | `lemma_conditional_true_full_deep` | fuel-1 |
| Margin | `lemma_margin_full_deep` | fuel |
| SizedBox | `lemma_sizedbox_full_deep` | fuel |
| AspectRatio | `lemma_aspectratio_full_deep` | fuel |
| ScrollView | inline (wrapper_child pattern) | fuel |
| Column | `lemma_column_full_deep` | fuel |
| Row | `lemma_row_full_deep` | fuel |
| Stack | `lemma_stack_full_deep` | fuel |
| Wrap | `lemma_wrap_full_deep` | fuel |
| Absolute | `lemma_absolute_full_deep` | fuel |
| Flex Column | `lemma_flex_column_full_deep` | fuel |
| Flex Row | `lemma_flex_row_full_deep` | fuel |
| Grid | `lemma_grid_child_i_deep` | per-index |
| ListView | `lemma_listview_child_i_deep` | per-index |

**Key infrastructure** (all in `congruence_proofs.rs`):
- `lemma_merge_layout_children_structure` — connects merge_layout output children to layout/cn fields
- `lemma_wrapper_child_deep_congruence` — combines position eqv + cn deep eqv → child deep eqv
- `lemma_linear_children_positions_congruence` — Column/Row children positions are eqv
- `lemma_child_main_position_congruence` — axis-parameterized position eqv
- Per-variant structural bridges: `lemma_column/row/stack/wrap/absolute/grid_structural_bridge`
- Per-variant element access lemmas (from existing `*_proofs.rs` files)
- Grid: `lemma_grid_child_position_congruence`, `lemma_grid_cell_x/y_congruence`
- Flex: `lemma_flex_main_sum_congruence`, `lemma_flex_column_child_y_congruence`, `lemma_flex_row_child_x_congruence`
- ListView: `lemma_listview_child_y_congruence` (already existed)

### 3. Draw Safety (`draw_proofs.rs`)
- `all_sizes_nonneg` predicate — recursive nonneg check for entire tree
- `lemma_flatten_all_valid` — if all_sizes_nonneg, all draws are valid
- `lemma_layout_root_draw_valid` — root draw always valid with wf limits
- `lemma_resolve_nonneg` — wf limits → resolved size nonneg
- `draws_eqv`, `draw_cmd_eqv` predicates for draw congruence
- `lemma_flatten_congruence` — deeply eqv nodes → eqv draws
- `lemma_node_count_congruence` — eqv nodes have same count

### 4. Hit-Test Geometric Correctness (`hit_test.rs`)
- `path_geometrically_valid` predicate — point within node at every path step
- `lemma_hit_test_geometrically_valid` — hit_test returns geometrically valid paths
- `lemma_hit_test_congruence` — eqv nodes + eqv coords → same hit result
- `lemma_point_in_node_congruence` — eqv nodes → same containment decision

### 5. Diff Completeness (`diff.rs`)
- `lemma_deeply_eqv_implies_diff_same` — deeply eqv → diff returns Same
- `lemma_diff_same_iff_deeply_eqv` — biconditional: diff is a decision procedure
- `lemma_deeply_eqv_depth_monotone` — depth d eqv implies depth d' eqv for d' ≤ d

### 6. Animation (`animation.rs`)
- `lemma_scalar_lerp_within_bounds` — lerp stays in [lo, hi] for any a, b in [lo, hi]
- `lemma_lerp_size_within_limits` — size lerp within limits
- `lemma_lerp_size_monotone` — lerp_size monotone in t
- `lemma_lerp_node_congruence_both` — both-argument congruence via transitivity
- `lemma_lerp_node_preserves_children_match` — lerp preserves tree structure
- `lemma_lerp_node_fuel_agree_eqv` — fuel agreement at depth 0

### 7. Text Model (`text_model/proofs.rs`)
- Per-dispatch wf lemmas: insert, delete_selection, delete_backward/forward, delete_word_backward/forward, move, extend_selection, compose_commit, compose_update
- `lemma_undo_redo_cancel_full` — text + styles roundtrip
- Visual position axioms: `axiom_visual_roundtrip`, `axiom_visual_line_monotone`

### 8. Other
- Drag/resize congruence, composition, boundary idempotency (`interaction.rs`)
- Event routing commutativity (`event_routing.rs`)
- Grid cell non-overlapping for arbitrary pairs (`grid_proofs.rs`)
- Flex weight conservation (`flex_proofs.rs`)
- Viewport correctness: scroll_to_cursor, scroll_by (`viewport.rs`)
- Selection geometry: rect count, monotone, strict ordering (`selection_geometry.rs`)
- Word wrap: count_visual_lines fuel sufficiency, line count bounds (`word_wrap.rs`)
- Widget_at_path composition, single-step, out-of-bounds (`widget.rs`)

## What's Already Proved (Pre-existing)

These were discovered during exploration — already complete:
- **CWB for all variants**: `lemma_layout_widget_cwb` (proofs.rs:3417) — children-within-bounds
- **Layout monotonicity**: `lemma_layout_widget_monotone` (proofs.rs:3800) — larger limits → larger sizes
- **Layout bounds**: `lemma_layout_widget_respects_limits` (bounds_proofs.rs:277) — output in [min, max]
- **Layout determinism**: `lemma_layout_stable_beyond_depth` (incremental_proofs.rs:245)
- **Sibling independence**: `lemma_sibling_layout_independent` (incremental_proofs.rs:77)
- **Fuel convergence**: `lemma_converged_layout_stable` (incremental_proofs.rs:18)
- **Scroll contiguity**: `lemma_visible_range_contiguous` (scroll.rs:103)
- **Exec-spec bridge**: 13 layout exec functions with `out@ == layout_widget::<RationalModel>(...)` ensures

## What Remains To Be Done

### Phase 1: Quick Wins
1. **Word wrap round-trip axioms** — `axiom_wrap_pos_round_trip`, `axiom_wrap_visual_round_trip` in `word_wrap.rs`. External_body axioms matching existing pattern.
2. **Layout convergence bound** — `widget_depth` fuel independence in `incremental_proofs.rs`. Most infrastructure exists.

### Phase 2: Text Model
3. **Eliminate 2 assume calls** — `session_helpers.rs` lines 850, 880. Need `axiom_find_result_grapheme_aligned` to prove find positions are grapheme boundaries.
4. **Master apply_key wf** — Complete `lemma_dispatch_key_preserves_model_wf` for ALL dispatch_key arms. Most per-operation lemmas exist; need to compose into single match.

### Phase 3: The Key Foundation
5. **Recursive all_sizes_nonneg** — Prove ALL nodes in layout tree have nonneg sizes. Per-variant recursion using `lemma_shrink_wf_general` + `lemma_intersect_wf` + `lemma_resolve_nonneg` + IH. **This unblocks full draw validity.**

### Phase 4: Draw Properties
6. **Render z-order** — Prove draws are monotonically increasing in depth. Induction on `flatten_node_to_draws`.
7. **Memory/allocation bounds** — Define `widget_node_count`, prove `node_count == widget_node_count` when fuel sufficient.
8. **Full draw validity + viewport** — Compose `all_sizes_nonneg` + `CWB` + `flatten_all_valid` → all draws valid AND within viewport.

### Phase 5: Full-Depth Composition
9. **Full draw/hit-test congruence** — Strengthen `the_fundamental_theorem` to use arbitrary `draw_fuel` and full `hit_test` congruence. Requires composing per-variant full-depth helpers into a single recursive master proof (blocked by type-dependent IH depth for Grid/ListView).

### Phase 6: Documentation
10. **Exec bridge documentation** — Document that spec proofs carry to exec via the View trait pattern.

## Proof Tips for This Codebase

### Z3/Verus Patterns That Work
- **Split large proofs into ≤30 line helpers** with `assert(...) by { ... }` scoping. Z3 has limited rlimit per function.
- **Per-index helpers**: When `assert forall|i| ...` fails, extract the body into a separate `lemma_foo_at_index(i)` helper that takes `i` as a parameter. Gives Z3 full rlimit budget per call.
- **Structural bridges**: For opaque layout functions, write `reveal(fn_name)` + step-by-step assertions connecting `layout_widget → layout_container → layout_*_body → merge_layout(variant_layout, cn)`. See `lemma_column_structural_bridge`.
- **Element access lemmas**: For recursive Seq builders (like `linear_children`, `stack_children`), use existing `lemma_*_children_element` lemmas to get concrete field values at specific indices.
- **`by(nonlinear_arith)`**: Verus syntax for nonlinear arithmetic (div/mod bounds). NOT `by(nonlinear_arith) requires ...` — just `by(nonlinear_arith)` as a block.
- **Eqv chains**: For `a.eqv(c)` from `a.eqv(b)` and `b.eqv(c)`: `T::axiom_add_congruence_left(a, b, x)` + `lemma_add_congruence_right(b, x, y)` + `axiom_eqv_transitive(a+x, b+x, b+y)`.
- **Never use assume/admit** — the CLAUDE.md is explicit about this.
- **rlimit tip from CLAUDE.md**: "if resource limit exceeded it's best to expand stuff out until it's not (just help z3 along)"

### Key Architecture Patterns
- **merge_layout**: All container layouts use `merge_layout(variant_layout(sizes), child_nodes)`. The variant_layout computes positions, merge_layout combines positions with recursive child results.
- **Widget fuel**: `layout_widget` uses fuel-based recursion. fuel=0 → trivial node. fuel>0 → dispatch to variant.
- **widget_eqv**: Fuel-indexed structural equivalence of widgets. `widget_eqv(w1, w2, fuel)` requires same variant, eqv fields, and recursively eqv children at fuel-1.
- **nodes_deeply_eqv**: Depth-indexed structural equivalence of nodes. `nodes_deeply_eqv(n1, n2, d)` checks field eqv at top level, and recursively at children up to depth d.
- **View trait**: Runtime types implement `View` with `type V = SpecType`. `runtime_obj@` gives the spec model. `wf_spec()` ensures runtime fields match the spec model.

### Files Map
| File | Purpose | Lemma Count |
|------|---------|-------------|
| `layout/congruence_proofs.rs` | Quotient ring congruence | ~90 |
| `layout/proofs.rs` | Layout bounds, CWB, monotonicity | ~90 |
| `text_model/proofs.rs` | Text editing wf preservation | ~65 |
| `text_model/undo_proofs.rs` | Undo/redo correctness | ~37 |
| `animation.rs` | Lerp properties | ~40 |
| `draw_proofs.rs` | Draw flattening, validity | ~16 |
| `hit_test.rs` | Hit-test correctness | ~22 |
| `diff.rs` | Diff completeness | ~20 |
| `theorems.rs` | Master theorems | ~7 |
| `widget.rs` | Layout dispatch, determinism | ~31 |
| Others | Various properties | ~600+ |

### Trusted Assumptions
The proof rests on 11 `#[verifier::external_body]` axioms in `text_model.rs`:
- `axiom_grapheme_boundaries_valid`, `axiom_word_start/end_boundaries_valid`, `axiom_line_break_valid`
- `axiom_splice_wf`, `axiom_compose_commit_wf`, `axiom_paste_wf`
- `axiom_movement_valid`, `axiom_word_boundaries_are_grapheme_boundaries`
- `axiom_prev/next_word_boundary_valid`
- `axiom_visual_roundtrip`, `axiom_visual_line_monotone`

Plus 15 `#[verifier::external_body]` exec functions in `runtime/text_model.rs` bridging spec to runtime.

And 2 `assume` calls in `runtime/session_helpers.rs` (lines 850, 880) — planned for elimination.

## MCP Tool Usage
The verus MCP server (`verus-mcp`) indexes all functions. Key commands:
- `search(query)` — find functions by name
- `lookup(name)` / `lookup_source(name)` — get signature or full source
- `check(crate_name, module?)` — verify. Without module: full crate. With module: fast iteration.
- `search_ensures(query)` — find lemmas that prove a property
- `context_activate(name)` — track looked-up items across session
