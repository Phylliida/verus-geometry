# Runtime Verification Optimization Notes

Findings from optimizing verus-geometry runtime exec verification time.

**Baseline:** 61s wall clock, 126s SMT time, 343 verified
**After:** ~27s wall clock, ~51s SMT time, 343 verified (0 errors)

Note: SMT time has high run-to-run variance (2x). Use rlimit (deterministic) for comparisons.

## 1. Extract branchy computations into helper functions

**Target:** `ray_hits_aabb3_exec` (22.9s), `ray_hits_aabb2_exec` (6.9s)
**Result:** runtime::ray module rlimit 17.1M → 2.4M (-86%)

The 3D AABB test had a 7-way if/else (which axes are non-parallel?) combined with other branches in the same function. Z3 explores all path products, causing exponential blowup.

**Fix:** Extract `slab_t_enter_3d_exec` and `slab_t_exit_3d_exec` (and 2D variants) into separate functions. Each verifies in isolation — the path products stay within each helper rather than multiplying across the whole function.

This is the single highest-ROI optimization pattern for Verus runtime code: if a function has N branch points, Z3 explores O(2^N) paths. Splitting into two functions with N/2 branches each reduces to O(2^(N/2) + 2^(N/2)) = O(2^(N/2+1)).

## 2. Remove passthrough quantifiers from inner loops

**Target:** `is_convex_polygon_exec` (18.1s)
**Result:** runtime::polygon module rlimit 51.4M → 26.5M (-48%)

The inner loop carried a quantifier restating that all *previous outer iterations* still hold:

```rust
//  REMOVED — Verus preserves facts about non-modified variables
forall|ii: int, jj: int|
    0 <= ii < i && 0 <= jj < polygon.model().len() ==> {
        let next_ii = polygon_next_index(n, ii);
        !orient2d_negative(polygon.model()[ii], polygon.model()[next_ii], polygon.model()[jj])
    },
```

Since the inner loop only modifies `j` (not `i` or `polygon`), Verus/Z3 automatically preserves the outer loop's quantifier over `[0, i)`. Threading it through the inner loop invariant is redundant and expensive.

**Rule:** If an inner loop doesn't modify the variables in an outer quantifier, don't restate that quantifier in the inner loop invariant.

## 3. Use `Seq::new` instead of `Seq::map` for view conversions

**Target:** All polygon functions (entire module)
**Result:** Wall clock 55s → 27s (-51%), SMT time 119s → 51s (-57%)

Changed `RuntimePolygon2::model()`:

```rust
//  BEFORE — Seq::map requires axiom unfolding
pub open spec fn model(&self) -> Seq<Point2<RationalModel>> {
    self.vertices@.map(|_i: int, v: RuntimePoint2| v@)
}

//  AFTER — Seq::new triggers fire automatically
pub open spec fn model(&self) -> Seq<Point2<RationalModel>> {
    Seq::new(self.vertices@.len(), |i: int| self.vertices@[i]@)
}
```

Z3 has a built-in trigger for `Seq::new(n, f)[k] == f(k)` that fires automatically on element access. `Seq::map` requires additional axiom unfolding steps. Since `polygon.model()[k]` appears in every loop invariant and proof assertion across ~11 polygon functions, this single change had an outsized effect.

**Caveat:** Even with `Seq::new`, explicit unfolding assertions are still needed when the index is freshly computed inside a loop body (e.g., `k = next(next(i))`):

```rust
proof {
    assert(polygon.model()[k as int] == polygon.vertices@[k as int]@);
    lemma_orient2d_sign_matches::<RationalModel>(vi@, vj@, vk@);
}
```

Functions where only `i` and `j = next(i)` are accessed (point-in-polygon, winding) don't need these — the loop variable indices are already in scope and Z3 can trigger on them directly.

## 4. DON'T remove explicit prefix assertions (failed experiment)

Attempted to simplify proof blocks in `point_in_convex_polygon_boundary_inclusive_exec` by removing explicit `assert(polygon_prefix_has_positive_sign(..., i+1))` assertions, expecting Z3 to derive prefix updates from the witnesses alone.

**Result:** rlimit 7M → 18M (+157%). Reverted.

Z3 needs the explicit assertions to guide its search. The witness (`polygon_edge_orient_sign(..., i) == Positive`) alone isn't enough — Z3 must also be told that the existential prefix predicate holds for `i+1`. This is cheap to state but expensive for Z3 to derive.

**Rule:** Don't remove explicit proof hints from loop bodies even when they seem redundant. Profile before and after with rlimit (deterministic), not SMT time (high variance).

## 5. Replace `polygon.model().len()` with `n as int` in quantifiers

**Target:** `is_locally_convex_polygon_exec` (9.0M rlimit), all polygon invariant quantifiers
**Result:** `is_locally_convex_polygon_exec` rlimit 9.0M → 4.1M (-54%), polygon module total 26.6M → 23.0M (-14%)

Invariant quantifiers referenced `polygon.model().len() as int` which expands to `Seq::new(self.vertices@.len(), ...).len()`. Z3 must apply the `Seq::new(n, f).len() == n` axiom every time it instantiates the quantifier. Since `n == polygon.vertices@.len()` is already in the invariant, replacing with `n as int` avoids the axiom application entirely:

```rust
//  BEFORE — Z3 must prove Seq::new(n, f).len() == n on each instantiation
forall|k: int| 0 <= k < i ==> {
    let j = polygon_next_index(polygon.model().len() as int, k);
    ...
}

//  AFTER — n is already a concrete usize, no axiom needed
forall|k: int| 0 <= k < i ==> {
    let j = polygon_next_index(n as int, k);
    ...
}
```

**Rule:** In loop invariant quantifiers, prefer concrete local variables (`n as int`) over expressions that require axiom unfolding (`polygon.model().len() as int`), even when they're definitionally equal.

## 6. Remove empty proof blocks

Empty `proof { //  comment }` blocks left over from removing assertions can be safely deleted — they add no verification cost but add noise. However, don't remove proof blocks that contain *any* assertions, even ones that look redundant (see finding 4).

## Summary of rlimit reductions

| Module | Original | Final | Reduction |
|---|---|---|---|
| runtime::ray | 17.1M | 2.4M | -86% |
| runtime::polygon | 51.4M | 23.0M | -55% |
| Total (all modules) | ~85M | ~57M | -33% |

Remaining costs are inherent complexity (deep symbolic expressions from cross/dot products, prefix-existential proof obligations) that would require algorithmic proof restructuring rather than syntactic optimizations.
