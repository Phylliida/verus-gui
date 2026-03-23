# verus-gui Status & Next Steps

**Status: 919 verified, 0 errors, 0 admits, 2 intentional assumes**

## Completed

### Core Layout System
- [x] Column, Row, Stack, Flex, Grid, Wrap, Absolute, ListView (spec + proofs + runtime)
- [x] Unified linear layout (axis-parameterized column/row)
- [x] Widget composition enum (Leaf/Wrapper/Container stratification)
- [x] Fuel convergence and monotonicity proofs
- [x] Measure pass with `lemma_measure_is_layout_size`
- [x] Layout monotonicity (widening limits widens size)
- [x] Constraint layout foundation (ChildConstraint, distribute, bounds proof)

### Layout Congruence (50+ lemmas, ALL 16 variants)
- [x] Primitive congruence: min, max, clamp, resolve, sub, align_offset
- [x] Padding/Limits congruence: horizontal, vertical, shrink, intersect
- [x] Body congruence: column, row, stack, wrap, grid, absolute, flex, listview
- [x] sum_heights, sum_widths, sum_main, sum_weights, repeated_add congruence
- [x] child_y_position congruence
- [x] wrap_cursor inductive congruence (with le_congruence_iff for branch congruence)
- [x] absolute_max_right/max_bottom congruence
- [x] lt_congruence_iff (from le_congruence_iff + eqv transitivity)
- [x] ListView: listview_child_y, listview_child_bottom, first/end_visible congruence
- [x] Master theorem: `lemma_layout_widget_size_congruence` — all 16 variants
- [x] Full node congruence: `lemma_layout_widget_node_congruence` — x, y, size eqv + children.len() — all 16 variants
- [x] Measure congruence: `lemma_measure_widget_congruence`
- [x] Bridge lemmas for Column/Row/Stack/Wrap/Absolute (step-by-step Z3 expansion)
- [x] Per-variant children count lemmas (8 container variants)
- [x] `widget_eqv` predicate covering all 16 widget variants

### Cache System
- [x] `widgets_shallow_equal_exec` — parameter comparison
- [x] `widgets_deep_equal_exec` — recursive comparison with model equality ensures (all 16 variants)
- [x] `model_normalized` predicate on RuntimeWidget
- [x] Incremental layout cache (`RuntimeLayoutCache`, `layout_children_incremental_exec`)
- [x] Reconciliation (`build_changed_vec`, `reconcile_children_exec`)
- [x] Dynamic reconciliation for variable-length children
- [x] Key-based child matching (`match_children_by_key`)

### Widget Normalization (fully verified, zero external_body)
- [x] `RuntimeRational::normalize()` with `normalized_spec()` guarantee
- [x] `RuntimeSize/Padding/Limits::normalize_exec()` building blocks
- [x] `normalize_widget_exec` — all 16 variants, split into leaf/wrapper/container helpers
- [x] Vec helpers with set_and_swap: widget, flex, absolute, size
- [x] Ghost weight-eqv tracking for Flex sum_weights nonzero preservation
- [x] `sum_weights_congruence` lemma

### Event System
- [x] Hit testing (spec + runtime + path validity proofs)
- [x] Event routing (focused_text_input_id_exec, node_local_coords_exec) — zero assumes
- [x] Interaction (drag/resize with clamping proofs)

### Text Editing
- [x] TextModel with cursor, selection, composition, paragraph styles
- [x] Cursor movement, text operations, undo/redo, find/replace
- [x] Word wrap (line counting, visual position mapping)
- [x] Unicode boundary exec bridges (grapheme, word start/end, line break)
- [x] Find next/prev exec with proven spec correspondence (5 assumes → 0)
- [x] Bridge lemmas: find_next_scan_matches_first, find_next_scan_exhausted, find_prev_scan_matches_last, find_prev_scan_exhausted

### Scroll
- [x] Visibility predicates and contiguous range proof
- [x] child_y_position monotonicity
- [x] Offset invariance (`child_y(pt + delta, k) eqv child_y(pt, k) + delta`)
- [x] Content height independence of scroll offset (with reusable eqv helpers)

### Other
- [x] Node diffing with reflexivity, symmetry, transitivity
- [x] Animation (scalar/size/node lerp with convex combination bounds)
- [x] Layout determinism (`lemma_layout_deterministic`)
- [x] Zero-children composition lemmas
- [x] Pre-existing flex_column/row invariant bugs fixed
- [x] text_input_config_eq assume closed (option_usize_eq helper)

## Remaining trust boundaries (intentional)

- 2 assumes: `session.model.wf_spec()` after find_next/find_prev sets anchor/focus — requires proving found position is at a grapheme boundary (Unicode semantic property, not closable without spec changes)
- ~10 external_body axioms: Unicode boundary validity, splice wf, visual layout mapping (foundational axioms about Unicode)
- 6 external_body bridges: Unicode exec bridges for grapheme, word, line break, visual layout (trusted runtime implementations)

## Possible Future Work

### Deeper Verification
- [ ] Full `nodes_deeply_eqv` — recursive child-by-child eqv (current theorem proves top-level node_eqv; extending to deep requires inductive child position/size congruence)
- [ ] Grapheme boundary guarantee for find positions — would close the last 2 assumes
- [ ] Constraint layout: grow/shrink distribution, full layout body function, runtime exec

### Code Quality
- [ ] Add ensures to `widgets_shallow_equal_exec` to eliminate re-comparison in deep_equal
- [ ] Extract container congruence template (shared shrink→IH→bridge→body pattern)
- [ ] Move `widget_eqv` to widget.rs for co-location with types
- [ ] Generalize bridge lemmas (Column/Row/Stack/Wrap/Absolute share same pattern)

### Features
- [ ] Key-based cache reconciliation integration (matching function exists, needs layout reuse logic)
- [ ] Accessibility tree generation from widget tree
- [ ] Verified renderer bridge (vulkan_bridge.rs)
