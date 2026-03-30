# Layer Primitive Design

## Motivation: Minimal Primitives for Composable UI

Research across Flutter, Chrome's Blink compositor, Vello (Raph Levien), SwiftUI,
Jetpack Compose, and the Haskell `diagrams` library reveals a convergent insight:

**Transform, Clip, and Opacity are not three separate concerns — they are three
parameters of a single "layer" primitive.**

Chrome's compositor team discovered that all visual effects decompose into three
independent property trees that compose along the widget hierarchy:

1. **Transform tree** — affine (or projective) transforms
2. **Clip tree** — rectangular, rounded-rect, or path-based clips
3. **Effect tree** — opacity, blend mode, filter, mask

These three trees are orthogonal. Any combination of parameters is valid, and
omitting a parameter means "inherit from parent" (identity transform, no clip,
full opacity).

### Vello's Scene API — The Modern Minimal Realization

Vello unifies this into 7 rendering operations:

```
fill(path, brush)
stroke(path, brush, style)
draw_image(image, rect)
draw_glyphs(font, glyphs, positions)
push_layer(blend_mode, alpha, transform, clip_shape)
pop_layer()
append(child_scene, transform)
```

The `push_layer` operation is the key: it takes optional transform, clip, and
alpha parameters, pushes them onto a compositing stack, and `pop_layer` restores
the previous state. Children are drawn within this modified context.

### What verus-gui Already Has

The existing widget set covers the convergent layout basis:

| Layout mode         | verus-gui widget                     | Status |
|---------------------|--------------------------------------|--------|
| Linear (Row/Column) | Column, Row, Flex                    | ✓      |
| ZStack (overlay)    | Stack                                | ✓      |
| Grid (2D tracks)    | Grid                                 | ✓      |
| Flow (wrapping)     | Wrap                                 | ✓      |
| Scroll (viewport)   | ScrollView, ListView                 | ✓      |
| Single-child mods   | Margin, SizedBox, AspectRatio        | ✓      |
| Conditional          | Conditional                          | ✓      |
| Absolute positioning | Absolute                             | ✓      |

What's missing is a **rendering composition** primitive. Currently, draw commands
are bare rectangles with (x, y, width, height, depth). There is no way to:

- Apply an affine transform to a subtree
- Clip children to an arbitrary shape
- Set opacity on a subtree
- Compose these effects

### The Gap: One Widget, Three Features

Adding a single `Layer` wrapper widget fills this entire gap:

```
Layer { transform: Option<AffineTransform2D<T>>, clip: Option<Rect<T>>, alpha: Option<T>, child }
```

This gives:
- **Transform** = Layer with just a transform
- **Clip** = Layer with just a clip rect
- **Opacity** = Layer with just an alpha
- **Clip + Transform** = Layer with both (e.g., rotated clip region)
- **Fade + Clip** = Layer with alpha + clip (e.g., frosted glass region)
- **Full composition** = all three parameters

### Baseline Alignment (Layout Protocol Extension)

The second gap is **baseline alignment** for mixed-height text and form fields.
This requires extending the layout protocol, not adding a widget:

- Children report a `baseline: Option<T>` in their layout result (Node)
- `Alignment::Baseline` aligns children on their reported baseline
- Row/Flex with `Alignment::Baseline` produces correct mixed-text alignment

This is how Flutter (`CrossAxisAlignment.baseline`) and SwiftUI
(`.firstTextBaseline`) handle it. It's a protocol extension, not a new widget.

### Derived Widgets (No New Primitives Needed)

Several "missing" web features compose from existing + Layer:

| Feature           | Composition                                              |
|-------------------|----------------------------------------------------------|
| Popover/Overlay   | Stack + Layer(clip=none) to escape parent clip           |
| Tooltip           | Conditional + Stack + Layer(clip=none)                   |
| Sticky            | ScrollView + clamped offset (spec function on scroll_y)  |
| Snap scroll       | ScrollView + quantized scroll offset (spec function)     |
| Carousel          | Row + ScrollView + snap                                  |
| Dropdown          | Conditional + Absolute + Layer(clip=none)                |
| Modal/Dialog      | Stack (full-size overlay child) + Layer(alpha for dimming)|
| Card with shadow  | Stack + Layer(alpha) for shadow + Margin for elevation   |
| Rounded corners   | Layer(clip=RoundedRect)                                  |

---

## Layer Primitive Specification

### Widget Definition

```rust
WrapperWidget::Layer {
    transform: Option<Mat3x3<T>>,  // 2D affine as 3x3 matrix (from verus-linalg)
    clip: Option<Rect<T>>,         // clip rectangle in local coordinates
    alpha: T,                      // opacity in [0, 1], default = 1
    child: Box<Widget<T>>,
}
```

Using `Mat3x3<T>` from verus-linalg for the transform allows full affine
transforms (translate, rotate, scale, skew) with existing verified matrix
algebra.

### Layout Behavior

Layer does **not** affect layout. The child is laid out with the same constraints
as if the Layer weren't there. The transform/clip/alpha are purely visual:

```
layout_layer(limits, transform, clip, alpha, child, fuel):
    child_node = layout_widget(limits, child, fuel)
    return Node {
        x: zero, y: zero,
        size: child_node.size,  // pass through child's size
        children: [child_node],
        layer: Some(LayerInfo { transform, clip, alpha }),
    }
```

This matches Flutter's behavior: `Transform` and `Opacity` widgets don't change
the child's layout constraints or reported size.

### Draw Command Extension

DrawCommand needs a layer context:

```rust
pub struct DrawCommand<T> {
    pub x: T, pub y: T,
    pub width: T, pub height: T,
    pub depth: nat,
    pub layer_stack: Seq<LayerInfo<T>>,  // accumulated layer context
}

pub struct LayerInfo<T> {
    pub transform: Mat3x3<T>,   // accumulated transform (identity if none)
    pub clip: Option<Rect<T>>,  // clip in world coordinates
    pub alpha: T,               // accumulated alpha (product of ancestors)
}
```

### Hit-Test Behavior

Hit-testing must:
1. **Invert the transform** — map the click point from parent coords to local coords
2. **Respect the clip** — reject clicks outside the clip region
3. **Ignore alpha** — opacity doesn't affect interactivity (a transparent widget is still clickable)

```
hit_test_layer(node, px, py, transform, clip, fuel):
    // Step 1: transform the point into local coordinates
    local_p = inverse(transform) * (px, py)

    // Step 2: check clip
    if clip is Some(rect) && !point_in_rect(local_p, rect):
        return None

    // Step 3: hit-test child with local coordinates
    hit_test(child_node, local_p.x, local_p.y, fuel)
```

### Flatten Behavior

Flattening pushes the layer context onto the draw commands:

```
flatten_layer(node, offset_x, offset_y, depth, layer_stack, fuel):
    new_stack = layer_stack.push(node.layer_info)
    // Self draw command with new_stack
    // Children flattened with accumulated transform applied to offsets
```

---

## Verification Properties

### Transform Properties

1. **Composition associativity**: `(A * B) * C == A * (B * C)` — from verus-linalg
2. **Identity**: Layer with identity transform === no Layer
3. **Inverse correctness**: `inv(A) * A * p == p` — hit-test round-trip
4. **Hit-test inversion**: if hit_test returns a path, the original click point
   maps to a point inside the child after applying the inverse transform chain
5. **Draw coordinate correctness**: draw commands have correct world-space
   coordinates after applying the accumulated transform

### Clip Properties

1. **Clip intersection**: nested clips produce the intersection
   `clip(R1, clip(R2, child)) == clip(intersect(R1, R2), child)`
2. **Hit-test respects clip**: points outside clip → hit_test returns None
3. **Clip containment**: draw commands are within the clip bounds (or
   the GPU clips them — document which model we use)
4. **Identity clip**: Layer with no clip === no Layer (for clip parameter)

### Alpha/Opacity Properties

1. **Range preservation**: alpha ∈ [0, 1] → accumulated alpha ∈ [0, 1]
2. **Composition**: nested alphas multiply: `alpha(a, alpha(b, child))` has
   effective alpha `a * b`
3. **Identity**: alpha = 1 === no opacity change
4. **Zero**: alpha = 0 → invisible (but still in layout, still receives hits
   unless we decide otherwise)
5. **Lerp in range**: animation interpolation of alpha stays in [0, 1]
   (from existing `lemma_scalar_lerp_within_bounds`)

### Congruence Properties

1. **Layer congruence**: eqv transform/clip/alpha + eqv child → eqv output
2. **Draw congruence**: extends existing `draws_eqv` to include layer context
3. **Hit-test congruence**: eqv layers produce same hit-test result

### GPU Safety

1. **Nonneg dimensions**: Layer doesn't change child size, so existing
   `all_sizes_nonneg` proof carries through
2. **Transform preserves validity**: draw commands remain valid after transform
   (nonneg width/height is a property of the child, not the transform)
3. **Clip is well-formed**: clip rect has nonneg dimensions

### Fundamental Theorem Extension

The fundamental theorem (`the_fundamental_theorem` and
`theorem_full_pipeline_congruence`) should extend to include:

- Layer congruence in the quotient ring
- Transform composition correctness
- Hit-test inversion through layer stack

---

## Implementation Plan

### Phase 1: Core Layer Widget
1. Add `LayerInfo<T>` struct with transform (Mat3x3), clip (Option<Rect>), alpha
2. Add `WrapperWidget::Layer` variant
3. Implement `layout_layer` — pass-through layout
4. Extend `DrawCommand` with layer context
5. Extend `flatten_node_to_draws` to accumulate layer stack
6. Verify: all existing theorems still hold (Layer is a passthrough for layout)

### Phase 2: Hit-Test
7. Implement `hit_test_layer` with transform inversion + clip check
8. Prove hit-test inversion correctness (uses verus-linalg inverse lemmas)
9. Prove clip rejection correctness
10. Extend `lemma_hit_test_geometrically_valid` to handle Layer

### Phase 3: Congruence
11. Define `layer_eqv` (eqv transform, clip, alpha)
12. Extend `widget_eqv` for Layer variant
13. Prove layout congruence (passthrough — should be easy)
14. Prove draw congruence with layer context
15. Prove hit-test congruence through layers
16. Extend full-depth congruence

### Phase 4: Alpha Properties
17. Prove alpha composition (multiplication)
18. Prove alpha range preservation [0, 1]
19. Prove alpha lerp stays in range (animation)

### Phase 5: Fundamental Theorem
20. Extend `the_fundamental_theorem` with Layer
21. Extend `theorem_full_pipeline_congruence`
22. Extend `theorem_full_draw_validity`

### Dependencies
- verus-linalg: Mat3x3 inverse, determinant, multiply (already exists)
- verus-linalg: Vec2 transform by Mat3x3 (may need to add)
- Rect type: may already exist in verus-geometry or need a simple definition

---

## References

- Chrome Blink compositor: transform/clip/effect property tree factorization
- Vello Scene API: `push_layer(blend, alpha, transform, clip)` as unified primitive
- Flutter: `Transform`, `ClipRect`, `Opacity` as separate widgets that could be one
- SwiftUI: `.transformEffect()`, `.clipped()`, `.opacity()` as view modifiers
- Haskell `diagrams` (Yorgey): monoid structure under `atop`, envelope-based composition
- CSS Compositing and Blending Level 1: `isolation`, `mix-blend-mode`, `opacity`
- Raph Levien, "Reactive UI" (2019): pipeline architecture for UI frameworks
