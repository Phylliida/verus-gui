# verus-gui

Formally verified GUI layout engine in [Verus](https://verus-lang.github.io/verus/).

**919 verified functions, 0 errors, 0 admits, 0 closable assumes.**

## What it does

verus-gui provides a complete, formally verified specification and runtime implementation for GUI layout, rendering, event handling, and text editing:

- **Layout engine** — 8 layout strategies (Column, Row, Stack, Flex, Grid, Wrap, Absolute, ListView) with padding, spacing, alignment
- **Measurement** — Calculate preferred widget sizes within constraints, with proof that measure == layout.size
- **Rendering** — Flatten hierarchical layout into draw commands with depth ordering
- **Event dispatch** — Hit testing, pointer/keyboard event routing, focus management
- **Text editing** — Rich text model with cursor, selection, IME composition, undo/redo, find/replace, word wrap
- **Incremental layout** — Cache system with deep widget comparison, normalization, key-based matching, and dynamic reconciliation
- **Animation** — Verified linear interpolation and convex combination primitives
- **Constraint layout** — Foundation for CSS flexbox-style min/max/flex_basis constraints

## Architecture

```
src/
  Core specs (generic over T: OrderedField)
    size.rs, limits.rs, node.rs, padding.rs, alignment.rs
    layout.rs + layout/*.rs     — 8 layout strategies + proofs
    layout/congruence_proofs.rs — 50+ lemmas: full layout congruence theorem
    layout/constraint.rs        — Constraint layout spec + bounds proof
    widget.rs                   — Widget enum, layout_widget, fuel convergence
    measure.rs                  — Measure pass + equivalence proof
    hit_test.rs                 — Point-in-node, path validity
    scroll.rs                   — Scroll visibility + invariance proofs
    event.rs, event_routing.rs  — Event dispatch specs
    text_model.rs + text_model/*.rs — Text editing model
    text_model/find_proofs.rs   — Find next/prev correctness + bridge lemmas
    diff.rs                     — Node diffing with reflexivity/symmetry/transitivity
    animation.rs                — Lerp, convex combination

  Runtime (exec, RuntimeRational-backed)
    runtime/
      widget.rs       — RuntimeWidget, deep comparison with model equality
                        ensures, fully verified normalization (all 16 variants)
      cache.rs        — Incremental layout cache, reconciliation,
                        dynamic variable-length reconciliation, key-based matching
      event_routing.rs — Proven runtime event dispatch (zero assumes)
      hit_test.rs     — Runtime hit testing with spec correspondence
      text_model.rs   — Runtime text editing + Unicode boundary bridges
      session_helpers.rs — Find exec with proven spec correspondence
      ...             — Per-layout runtime implementations
```

## Key verified properties

### Layout congruence (50+ lemmas, all 16 widget variants)
The crown jewel: **equivalent rational representations produce equivalent layout results.**
- `lemma_layout_widget_size_congruence` — eqv widgets → eqv layout sizes
- `lemma_layout_widget_node_congruence` — eqv widgets → full `node_eqv` (x, y, size eqv + children.len() equal)
- `lemma_measure_widget_congruence` — eqv widgets → eqv measure sizes
- Proved bottom-up from primitives: `min`/`max`/`clamp`/`resolve`/`sub`/`align_offset` congruence → `sum_heights`/`sum_widths`/`sum_main`/`repeated_add` congruence → layout body congruence → master theorem
- ListView visible range congruence: `listview_first/end_visible` produce same indices for eqv inputs (via `lt_congruence_iff` + `listview_child_y` congruence + `measure_widget` congruence)
- Bridge lemmas connect `layout_widget` → `layout_container` → body functions using step-by-step Z3 expansion

### Layout
- **Determinism** — `layout_widget(lim, w, fuel1) == layout_widget(lim, w, fuel2)` once fuel exceeds tree depth
- **Monotonicity** — Widening limits widens output size
- **Composition** — Zero-children layouts produce childless nodes; column == linear(Vertical)
- **Children count** — Per-variant lemmas proving `layout_widget(...).children.len()` for all 8 container types

### Scroll
- **Offset invariance** — `child_y(pt + delta, k) eqv child_y(pt, k) + delta`
- **Content height independence** — Content height is independent of scroll offset (via reusable eqv helpers: `sub_self_eqv_zero`, `add_sub_cancel_right`, `child_y_eqv_cy0_add_pt`)
- **Visible range contiguity** — Visible children form a contiguous range

### Cache system
- **Deep comparison** — `widgets_deep_equal_exec` with model equality ensures: `(out && model_normalized(a) && model_normalized(b)) ==> a.model() === b.model()`
- **Normalization** — `normalize_widget_exec` verified for all 16 variants (zero external_body), with set_and_swap Vec consumption and ghost weight-eqv tracking for Flex `sum_weights` nonzero preservation
- **Key-based matching** — `match_children_by_key` with proven contract: matched pairs have equal keys, indices in bounds
- **Dynamic reconciliation** — `reconcile_children_dynamic_exec` handles variable-length children
- **Incremental reuse** — Unchanged children reuse cached layout results

### Event routing
- **Spec correspondence** — Runtime `focused_text_input_id_exec` and `node_local_coords_exec` proven equivalent to spec (zero assumes)
- **Path validity** — Hit test always returns valid widget tree paths
- **Hit test exec** — Runtime hit testing with `wf_deep` and spec correspondence

### Text model
- **Unicode bridges** — 4 exec functions bridging uninterpreted boundary specs to unicode-segmentation crate (grapheme, word start/end, line break)
- **Find correctness** — `find_next_exec`/`find_prev_exec` proven equivalent to spec via bridge lemmas (`find_next_scan_matches_first`, `find_next_scan_exhausted`, `find_prev_scan_matches_last`, `find_prev_scan_exhausted`)
- **Undo/redo** — `undo(redo(m)) == m`
- **Permitted characters** — Operations preserve permitted character set

### Rational normalization (verus-rational)
- `RuntimeRational::normalize()` guarantees `out@.normalized_spec()` — canonical form
- `Rational::lemma_normalized_eqv_implies_equal` — normalized + eqv → structurally equal
- `model_normalized` predicate on RuntimeWidget — tracks canonical form through widget tree

## Trust boundaries

| Category | Count | Nature |
|----------|-------|--------|
| Assumes | 2 | Intentional: `session.model.wf_spec()` after find (grapheme boundary design) |
| Admits | 0 | None |
| External body (axioms) | ~10 | Unicode boundary validity, splice wf, visual layout mapping |
| External body (bridges) | 6 | Unicode exec bridges (grapheme, word, line break, visual layout) |
| External body (other) | 1 | `dead_session` (requires false, unreachable code) |

## Dependencies

- [vstd](https://verus-lang.github.io/verus/) — Verus standard library
- [verus-algebra](../verus-algebra) — Ordered ring/field traits and lemmas
- [verus-bigint](../verus-bigint) — Verified arbitrary-precision integers
- [verus-rational](../verus-rational) — Verified rational arithmetic with normalization
- [unicode-segmentation](https://crates.io/crates/unicode-segmentation) — Unicode boundary detection (runtime only)
