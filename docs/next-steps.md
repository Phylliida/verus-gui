# verus-gui Next Steps

Status: 192 verified, 0 errors, 0 assume(false)

## Completed Phases

- [x] Phase 1: Center alignment fix
- [x] Phase 2: Stack, Flex, Grid layouts (spec + proofs)
- [x] Phase 3: Runtime primitives (size, limits, padding, node)
- [x] Phase 4: Runtime column + row
- [x] Phase 5: Runtime stack, flex, grid
- [x] Phase 6: Row content width monotone lemma
- [x] Phase 7: Wrap layout (spec + proofs + runtime)
- [x] Phase 8: Widget composition enum (spec only)
- [x] Phase 9: Fuel monotonicity (widget_converged, fuel monotone lemma, layout_widget_full)
- [x] Phase 10: Wrap proof properties (cursor nonneg, position bounds, same-line non-overlap)
- [x] Phase 11: Runtime widget exec (RuntimeWidget enum, layout_widget_exec, merge_layout_exec)
- [x] Phase 12: Measure pass (measure_widget spec + lemma_measure_is_layout_size + measure_widget_exec)

## Phase 13: Flex/Grid Widget Variants

- [ ] **13a. `FlexItem` wrapper** — `{ weight: T, child: Widget<T> }`
- [ ] **13b. `Widget::Flex` variant** — flex layout with FlexItem children
- [ ] **13c. `Widget::Grid` variant** — grid layout with col_widths, row_heights, 2D children

## Phase 14: Additional Layout Types

- [ ] **14a. Absolute positioning** — children specify exact (x, y) offsets
- [ ] **14b. Margin wrapper** — spacing outside the box (composes with padding)
