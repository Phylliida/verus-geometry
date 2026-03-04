# Convexity Spec Redesign: Star Polygon Counterexample

## Problem

The original `is_convex_polygon` definition (convexity.rs) checked only **local**
consecutive triples:

```rust
forall|i: int| 0 <= i < n ==>
    !orient2d_negative(polygon[i], polygon[next(i)], polygon[next(next(i))])
```

This admits self-intersecting **star polygons** that have all left turns at each
vertex but are not geometrically convex.

## Counterexample: {5/2} Pentagram

Consider the vertices of a regular pentagram traversed in star order:

```
A = (0, 10)
D = (-5, -8)
B = (9, 3)
E = (-9, 3)
C = (5, -8)
```

Polygon: [A, D, B, E, C] — this traces the 5-pointed star {5/2}.

### Local convexity holds (all 5 consecutive triples)

orient2d(a, b, c) = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

1. **orient2d(A, D, B)**:
   (-5 - 0)(3 - 10) - (-8 - 10)(9 - 0)
   = (-5)(-7) - (-18)(9) = 35 + 162 = **197 > 0**

2. **orient2d(D, B, E)**:
   (9 - (-5))(3 - (-8)) - (3 - (-8))(-9 - (-5))
   = (14)(11) - (11)(-4) = 154 + 44 = **198 > 0**

3. **orient2d(B, E, C)**:
   (-9 - 9)(-8 - 3) - (3 - 3)(5 - 9)
   = (-18)(-11) - (0)(-4) = 198 - 0 = **198 > 0**

4. **orient2d(E, C, A)**:
   (5 - (-9))(10 - 3) - (-8 - 3)(0 - (-9))
   = (14)(7) - (-11)(9) = 98 + 99 = **197 > 0**

5. **orient2d(C, A, D)**:
   (0 - 5)(-8 - (-8)) - (10 - (-8))(-5 - 5)
   = (-5)(0) - (18)(-10) = 0 + 180 = **180 > 0**

All five are strictly positive, so the old `is_convex_polygon` and even
`is_strictly_convex_polygon` would accept this polygon.

### Vertex A is NOT inside the polygon

Check vertex A = (0, 10) against all edges:

- **Edge D->B**: orient2d(D, B, A) = orient2d((-5,-8), (9,3), (0,10))
  = (9-(-5))(10-(-8)) - (3-(-8))(0-(-5))
  = (14)(18) - (11)(5) = 252 - 55 = **197 > 0** (Positive)

- **Edge B->E**: orient2d(B, E, A) = orient2d((9,3), (-9,3), (0,10))
  = (-9-9)(10-3) - (3-3)(0-9)
  = (-18)(7) - (0)(-9) = **-126 < 0** (Negative!)

Since vertex A sees both Positive and Negative signs across edges, it is NOT
inside the polygon by `point_in_convex_polygon_boundary_inclusive`. This means
`lemma_vertex_in_convex_polygon` is **false as stated** with the old local-only
definition.

## Root Cause

Local convexity (consecutive triples only) is equivalent to "all turns are
left turns." For simple polygons this implies global convexity, but for
self-intersecting polygons it does not. A star polygon like {5/2} has winding
number 2 around its center — every vertex turn is a left turn, but the shape
is not convex.

The key insight: **local convexity + simple polygon = global convexity**, but
the old spec did not require simplicity. Adding a simplicity check would be
complex. Instead, we directly define global convexity.

## Fix: Global Half-Plane Definition

A polygon is convex if and only if **every vertex lies on the non-negative
side of every directed edge**:

```rust
pub open spec fn is_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& forall|i: int, j: int| 0 <= i < polygon.len() && 0 <= j < polygon.len() ==> {
        let next_i = polygon_next_index(polygon.len() as int, i);
        !orient2d_negative(polygon[i], polygon[next_i], polygon[j])
    }
}
```

This is O(n^2) to check but is the standard mathematical definition: the polygon
is the intersection of half-planes defined by its edges.

Similarly for strict convexity (non-adjacent vertices are strictly positive):

```rust
pub open spec fn is_strictly_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& is_convex_polygon(polygon)
    &&& forall|i: int, j: int|
        0 <= i < polygon.len() && 0 <= j < polygon.len()
        && j != i && j != polygon_next_index(polygon.len() as int, i) ==> {
        let next_i = polygon_next_index(polygon.len() as int, i);
        orient2d_positive(polygon[i], polygon[next_i], polygon[j])
    }
}
```

## Impact

### Spec layer (convexity.rs)
- Old `is_convex_polygon` renamed to `is_locally_convex_polygon`
- Old `is_strictly_convex_polygon` renamed to `is_locally_strictly_convex_polygon`
- New `is_convex_polygon` uses global half-plane definition
- New `is_strictly_convex_polygon` adds strict positivity for non-adjacent vertices
- New lemma: `lemma_convex_implies_locally_convex` (trivial: consecutive triples are a special case of all pairs)
- Updated lemma: `lemma_strictly_convex_implies_convex` (from new strict to new convex)
- `lemma_vertex_in_convex_polygon` becomes trivial (direct from global definition)

### Runtime layer (runtime/polygon.rs)
- `is_convex_polygon_exec` changes from O(n) to O(n^2) double loop
- `is_strictly_convex_polygon_exec` similarly O(n^2)
- Old O(n) checks preserved as `is_locally_convex_polygon_exec`

### Deferred lemma resolution
- `lemma_vertex_in_convex_polygon` no longer needs the orient2d decomposition identity or fan induction — it follows directly from the global definition
- The `assume(false)` is eliminated

### No external impact
- No callers of these specs exist outside verus-geometry (verified via MCP dependency search)
- verus-topology does not reference these predicates
