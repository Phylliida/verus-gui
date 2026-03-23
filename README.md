# verus-gui

Formally verified GUI layout engine in [Verus](https://verus-lang.github.io/verus/).

**893 verified functions, 0 errors, 0 assumes, 0 admits.**

## What it does

verus-gui provides a complete, formally verified specification and runtime implementation for GUI layout, rendering, event handling, and text editing:

- **Layout engine** — 8 layout strategies (Column, Row, Stack, Flex, Grid, Wrap, Absolute, ListView) with padding, spacing, alignment
- **Measurement** — Calculate preferred widget sizes within constraints, with proof that measure == layout.size
- **Rendering** — Flatten hierarchical layout into draw commands with depth ordering
- **Event dispatch** — Hit testing, pointer/keyboard event routing, focus management
- **Text editing** — Rich text model with cursor, selection, IME composition, undo/redo, find/replace, word wrap
- **Incremental layout** — Cache system for efficient re-layout of unchanged subtrees
- **Animation** — Verified linear interpolation and convex combination primitives

## Architecture

```
src/
  Core specs (generic over T: OrderedField)
    size.rs, limits.rs, node.rs, padding.rs, alignment.rs
    layout.rs + layout/*.rs     — 8 layout strategies + proofs
    widget.rs                   — Widget enum, layout_widget, fuel convergence
    measure.rs                  — Measure pass + equivalence proof
    hit_test.rs                 — Point-in-node, path validity
    scroll.rs                   — Scroll visibility + invariance proofs
    event.rs, event_routing.rs  — Event dispatch specs
    text_model.rs + text_model/*.rs — Text editing model
    diff.rs                     — Node diffing with reflexivity/symmetry/transitivity
    animation.rs                — Lerp, convex combination

  Runtime (exec, RuntimeRational-backed)
    runtime/
      widget.rs     — RuntimeWidget, deep comparison, normalization
      cache.rs      — Incremental layout cache + reconciliation
      event_routing.rs — Proven runtime event dispatch
      hit_test.rs   — Runtime hit testing
      text_model.rs — Runtime text editing + Unicode bridges
      ...           — Per-layout runtime implementations
```

## Key verified properties

### Layout
- **Determinism** — `layout_widget(lim, w, fuel1) == layout_widget(lim, w, fuel2)` once fuel exceeds tree depth
- **Congruence** — Equivalent rational representations produce equivalent layout results (33 lemmas, all 16 widget variants)
- **Monotonicity** — Widening limits widens output size
- **Composition** — Zero-children layouts produce childless nodes; column == linear(Vertical)

### Scroll
- **Offset invariance** — `child_y(pt + delta, k) eqv child_y(pt, k) + delta`
- **Content height independence** — Content height is independent of scroll offset
- **Visible range contiguity** — Visible children form a contiguous range

### Cache
- **Deep comparison** — Recursive widget comparison with model equality ensures
- **Normalization** — `normalize_widget_exec` produces `model_normalized` widgets (all 16 variants, zero trust gaps)
- **Incremental reuse** — Unchanged children reuse cached layout results

### Event routing
- **Spec correspondence** — Runtime `focused_text_input_id_exec` and `node_local_coords_exec` proven equivalent to spec
- **Path validity** — Hit test always returns valid widget tree paths

### Text model
- **Unicode bridges** — 4 exec functions bridging uninterpreted boundary specs to unicode-segmentation crate
- **Undo/redo** — `undo(redo(m)) == m`
- **Permitted characters** — Operations preserve permitted character set

## Dependencies

- [vstd](https://verus-lang.github.io/verus/) — Verus standard library
- [verus-algebra](../verus-algebra) — Ordered ring/field traits and lemmas
- [verus-bigint](../verus-bigint) — Verified arbitrary-precision integers
- [verus-rational](../verus-rational) — Verified rational arithmetic with normalization
- [unicode-segmentation](https://crates.io/crates/unicode-segmentation) — Unicode boundary detection (runtime only)
