# verus-gui Status & Next Steps

**Status: 893 verified, 0 errors, 0 assumes, 0 admits**

## Completed

### Core Layout System
- [x] Column, Row (spec + proofs + runtime)
- [x] Stack, Flex, Grid, Wrap, Absolute, ListView (spec + proofs + runtime)
- [x] Unified linear layout (axis-parameterized column/row)
- [x] Widget composition enum (Leaf/Wrapper/Container stratification)
- [x] Fuel convergence and monotonicity proofs
- [x] Measure pass with `lemma_measure_is_layout_size`
- [x] Layout monotonicity (widening limits widens size)

### Layout Congruence (33 lemmas)
- [x] Primitive congruence: min, max, clamp, resolve, sub, align_offset
- [x] Padding/Limits congruence: horizontal, vertical, shrink, intersect
- [x] Body congruence: column, row, stack, wrap, grid, absolute, flex, listview
- [x] sum_heights, sum_widths, sum_main, sum_weights, repeated_add congruence
- [x] child_y_position congruence
- [x] wrap_cursor inductive congruence (with le_congruence_iff for branch congruence)
- [x] absolute_max_right/max_bottom congruence
- [x] Master theorem: `lemma_layout_widget_size_congruence` — all 16 variants proved
- [x] Bridge lemmas for Column/Row/Stack/Wrap/Absolute (step-by-step Z3 expansion)

### Cache System
- [x] `widgets_shallow_equal_exec` — parameter comparison
- [x] `widgets_deep_equal_exec` — recursive comparison with model equality ensures (all 16 variants)
- [x] `model_normalized` predicate on RuntimeWidget
- [x] Incremental layout cache (`RuntimeLayoutCache`, `layout_children_incremental_exec`)
- [x] Reconciliation (`build_changed_vec`, `reconcile_children_exec`)
- [x] Dynamic reconciliation for variable-length children

### Widget Normalization
- [x] `RuntimeRational::normalize()` with `normalized_spec()` guarantee
- [x] `RuntimeSize/Padding/Limits::normalize_exec()` building blocks
- [x] `normalize_widget_exec` — all 16 variants, zero trust gaps
- [x] Vec helpers with set_and_swap: widget, flex, absolute, size
- [x] Ghost weight-eqv tracking for Flex sum_weights nonzero preservation

### Event System
- [x] Hit testing (spec + runtime + path validity proofs)
- [x] Event routing (focused_text_input_id_exec, node_local_coords_exec)
- [x] All `assume(false)` eliminated in event routing
- [x] Interaction (drag/resize with clamping proofs)

### Text Editing
- [x] TextModel with cursor, selection, composition, paragraph styles
- [x] Cursor movement, text operations, undo/redo, find/replace
- [x] Word wrap (line counting, visual position mapping)
- [x] Unicode boundary exec bridges (grapheme, word start/end, line break)

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

## Possible Future Work

### Code Quality
- [ ] Add ensures to `widgets_shallow_equal_exec` to eliminate re-comparison in deep_equal
- [ ] Extract container congruence template (shared shrink→IH→bridge→body pattern)
- [ ] Move `widget_eqv` and eqv predicates to widget.rs for co-location with types
- [ ] Generalize bridge lemmas (Column/Row/Stack/Wrap/Absolute share same pattern)
- [ ] Use `calc!` macro for eqv chains (if Verus adds support for custom relations)

### Features
- [ ] Key-based structural diffing for cache reconciliation (React-style)
- [ ] Layout congruence for full Node (not just size) — enables eqv-based cache
- [ ] Runtime validation tests for external_body Unicode bridges
- [ ] Accessibility tree generation from widget tree
