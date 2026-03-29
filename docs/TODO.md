# verus-geometry — Implementation TODO

Formally verified geometric predicates in Rust + Verus, parameterized over
any `Ring` (from verus-algebra).

This crate is **predicates only**: orientation, collinearity, coplanarity,
sidedness, intersection classification. It does NOT contain curves, surfaces,
BREP evaluation, or runtime numeric types — those belong downstream.

## Crate layering

```
verus-algebra (Ring, OrderedRing, Field traits + lemmas)
  └→ verus-linalg (Vec2, Vec3, Vec4, Mat3 + ops)
       └→ verus-geometry              ← this crate (predicates & lemmas)
            └→ verus-topology         (combinatorial mesh, Euler operators)
            └→ verus-brep-kernel      (BREP evaluation, surfaces, intersections)
```

## What we have now

291 verified items, 0 errors, 0 assumes/admits.

| Module | Contents | Status |
|---|---|---|
| `point2.rs` | `Point2<T>`, equivalence, `sub2`, `add_vec2`, self-zero + translation lemmas | Done |
| `point3.rs` | `Point3<T>`, equivalence, `sub3`, `add_vec3`, self-zero + translation lemmas | Done |
| `orient2d.rs` | `det2d`, `orient2d`, det2d helpers (antisymmetric, congruence, sub_left, scale_right, self_zero), public lemmas (swap, degenerate, cyclic, translation) | Done |
| `orient3d.rs` | `orient3d` via triple product, 6 public lemmas (swap_cd, swap_bc, cycle_bcd, degenerate_ab/cd, translation) | Done |
| `orientation_sign.rs` | `OrientationSign` enum, `orient2d/3d_sign`, `scalar_sign`, positive/negative/zero predicates, trichotomy, swap, degenerate, positive-scaling lemmas | Done |
| `collinearity.rs` | `collinear2d/3d`, `coplanar`, permutation/degenerate lemmas, three-points-coplanar, collinear3d→2D-projections | Done |
| `sidedness.rs` | Point vs line/plane predicates, trichotomy, swap, segment-plane crossing | Done |
| `segment_intersection.rs` | `SegmentIntersection2dKind` enum, classification spec, proper-implies-straddle, denominator-nonzero, exhaustive, collinear-overlap-collinear, 2D intersection point spec + on-line proof | Done |
| `convex_polygon.rs` | Point-in-convex-polygon (boundary-inclusive + strict), prefix step lemmas, superset lemma | Done |
| `intersection3d.rs` | Segment-plane parameter/point specs, denominator-nonzero, 0<t<1 bounds, intersection-point-on-plane, affine combination, 2D projection, point-in-triangle, segment-triangle intersection spec + combined properties lemma | Done |
| `segment_polygon.rs` | Segment-convex polygon overlap spec, prefix edge hit lemma, endpoint-inside-implies-overlap | Done |
| `convexity.rs` | `is_convex_polygon` (global half-plane), `is_strictly_convex_polygon`, `is_locally_convex_polygon`, `is_locally_strictly_convex_polygon`, convex-implies-locally-convex, strictly-convex-implies-convex, vertex-in-convex-polygon lemmas | Done |
| `face_normal.rs` | Normal orthogonality to edges, normal swap-negation, `faces_consistently_oriented` spec | Done |
| `aabb.rs` | `point_in_aabb2/3`, `aabb2/3_separated` specs, separation-implies-no-common-point lemmas (2D & 3D) | Done |
| `barycentric.rs` | Barycentric coordinate specs (unnormalized & normalized), orient2d repeated_ac, vertex-sum lemmas (a, b, c) | Done |
| `segment_distance.rs` | Line-line closest approach specs + perpendicularity proof: `gram_entries`, `gram_determinant`, `closest_parameter_s/t`, `line_line_squared_distance`, `lemma_closest_points_perpendicular` | Done |
| `incircle.rs` | Incircle2d predicate: `incircle2d`, `incircle2d_sign`, positive/negative/cocircular predicates, degenerate + trichotomy + sign lemmas | Done |
| `area.rs` | Signed polygon area (shoelace): `cross_origin`, `signed_area_2x_prefix`, `signed_area_2x`, det2d bridge + prefix unfold lemmas | Done |
| `winding.rs` | Winding number point-in-polygon: `winding_edge`, `winding_number`, `point_in_polygon`, prefix unfold lemma | Done |

Everything is generic over `T: Ring` — no concrete numeric types.

## What the old vcad-geometry had (reference for parity)

The old crate (~7,300 lines) had significantly more, all over concrete
`RuntimeScalar`/`RuntimePoint` types rather than generic Ring:

- Orientation predicates (orient2d, orient3d) with sign extraction
- Collinearity (2D and 3D) and coplanarity
- Sidedness predicates (point above/below/on plane)
- Segment-plane intersection with parameter calculation
- Point-in-convex-polygon (2D, boundary-inclusive and strict)
- Segment-segment intersection (2D, with classification enum)
- Segment-triangle intersection (3D)
- Segment-polygon overlap (2D)
- Runtime refinement modules pairing specs to exec implementations
- Phase 5 upstream lemmas (~1,400 lines of helper lemmas)

---

## Phase 1 — Sign extraction & classification

Currently we have `orient2d` and `orient3d` as Ring-valued spec functions.
For downstream use (topology checks, intersection classification), we need
to extract the sign and classify.

### 1.1 Orientation sign (requires OrderedRing)

```
pub enum OrientationSign { Positive, Zero, Negative }

spec fn orient2d_sign<T: OrderedRing>(a, b, c: Point2<T>) -> OrientationSign
spec fn orient3d_sign<T: OrderedRing>(a, b, c, d: Point3<T>) -> OrientationSign
```

- [x] Define `OrientationSign` enum
- [x] `orient2d_sign` spec: classify sign of `orient2d(a, b, c)`
- [x] `orient3d_sign` spec: classify sign of `orient3d(a, b, c, d)`
- [x] Lemma: sign is invariant under positive scaling
- [x] Lemma: swap reverses sign (lift existing swap lemmas to sign level)
- [x] Lemma: degenerate cases give Zero (lift existing degenerate lemmas)

### 1.2 Strict positivity / negativity predicates

Useful shorthand:

```
spec fn orient2d_positive<T: OrderedRing>(a, b, c) -> bool {
    T::zero().lt(orient2d(a, b, c))
}
```

- [x] `orient2d_positive`, `orient2d_negative`, `orient2d_zero` predicates
- [x] `orient3d_positive`, `orient3d_negative`, `orient3d_zero` predicates
- [x] Lemma: exactly one of {positive, negative, zero} holds (trichotomy)

---

## Phase 2 — Collinearity & coplanarity

### 2.1 Collinearity (2D)

```
spec fn collinear2d<T: OrderedRing>(a, b, c: Point2<T>) -> bool {
    orient2d(a, b, c).eqv(T::zero())
}
```

- [x] `collinear2d` spec
- [x] Lemma: reflexive — `collinear2d(a, a, c)` (from degenerate_ab)
- [x] Lemma: symmetric — permutation invariance (from cyclic + swap)
- [x] Lemma: if collinear and a != b, c is an affine combination of a and b

### 2.2 Collinearity (3D)

3D collinearity can't use orient2d. Instead: `cross(b-a, c-a) ≡ Vec3::zero()`.

- [x] `collinear3d` spec via cross product zero
- [x] Lemma: collinear3d(a, a, c) always holds
- [x] Lemma: collinear3d is permutation-invariant
- [x] Lemma: collinear3d implies all 2D projections are collinear

### 2.3 Coplanarity

```
spec fn coplanar<T: OrderedRing>(a, b, c, d: Point3<T>) -> bool {
    orient3d(a, b, c, d).eqv(T::zero())
}
```

- [x] `coplanar` spec
- [x] Lemma: any 3 points are coplanar with themselves
- [x] Lemma: permutation rules (from orient3d swap/cycle lemmas)
- [x] Lemma: collinear3d(a, b, c) implies coplanar(a, b, c, d) for any d

---

## Phase 3 — Sidedness predicates

These determine which side of a line (2D) or plane (3D) a point lies on.

### 3.1 Point vs. line (2D)

- [x] `point_left_of_line(p, a, b)` — orient2d(a, b, p) > 0
- [x] `point_right_of_line(p, a, b)` — orient2d(a, b, p) < 0
- [x] `point_on_line(p, a, b)` — orient2d(a, b, p) ≡ 0
- [x] Lemma: exactly one holds (trichotomy)
- [x] Lemma: swapping a, b flips left/right

### 3.2 Point vs. plane (3D)

- [x] `point_above_plane(p, a, b, c)` — orient3d(a, b, c, p) > 0
- [x] `point_below_plane(p, a, b, c)` — orient3d(a, b, c, p) < 0
- [x] `point_on_plane(p, a, b, c)` — orient3d(a, b, c, p) ≡ 0
- [x] Lemma: exactly one holds
- [x] Lemma: swapping two plane vertices flips above/below

### 3.3 Segment-plane crossing

- [x] `segment_crosses_plane_strict(d, e, a, b, c)` — endpoints on opposite sides
- [x] Lemma: crossing implies d and e are not on the plane
- [x] Lemma: crossing implies d and e have opposite orientation signs

---

## Phase 4 — Intersection predicates (2D)

### 4.1 Segment-segment intersection classification

```
pub enum SegmentIntersectionKind {
    Disjoint,
    Proper,           //  interiors cross
    EndpointTouch,    //  endpoint meets other segment
    CollinearOverlap, //  collinear and overlapping
}
```

- [x] Define classification enum
- [x] `segment_intersection_kind_2d(a, b, c, d)` spec
- [x] Algorithm: 4-way orientation test
      - `o1 = orient2d_sign(a, b, c)`, `o2 = orient2d_sign(a, b, d)`
      - `o3 = orient2d_sign(c, d, a)`, `o4 = orient2d_sign(c, d, b)`
      - Proper: o1 != o2 && o3 != o4 && all nonzero
      - Collinear: all zero, then check 1D overlap
      - EndpointTouch: some zero, others consistent
      - Disjoint: otherwise
- [x] Lemma: classification is exhaustive (exactly one case)
- [x] Lemma: Proper implies segments straddle each other
- [x] Lemma: Disjoint implies no shared point exists

### 4.2 Segment intersection point (for Proper and EndpointTouch)

- [x] `segment_intersection_point_2d(a, b, c, d)` — compute witness point
- [x] For Proper: parameter `t = orient2d(c,d,a) / (orient2d(c,d,a) - orient2d(c,d,b))`, point = `a + t*(b-a)`
- [x] Lemma: witness point lies on segment AB (on-line + bounding box via affine combination)
- [x] Lemma: witness point lies on segment CD (CD parameter + uniqueness proof)
- [x] Lemma: denominator is nonzero for Proper case
- [x] Lemma: intersection point lies on line(a, b) (orient2d(a,b,p) ≡ 0)

---

## Phase 5 — Point-in-polygon (2D)

### 5.1 Convex polygon containment

- [x] `point_in_convex_polygon_boundary_inclusive(p, polygon)` spec
      — NOT (has both positive and negative edge orientations)
- [x] `point_strictly_in_convex_polygon(p, polygon)` spec
      — all edge orientations same sign, none zero
- [x] Lemma: boundary-inclusive is a superset of strict
- [x] Lemma: vertices of the polygon are boundary-inclusive (via `lemma_vertex_in_convex_polygon`)
- [x] Precondition documentation: polygon must be convex with consistent winding

### 5.2 General polygon containment (winding number / ray casting)

This is harder and may not be needed immediately. Defer unless required.

- [ ] Decide: winding number vs. ray casting approach
- [ ] Implement if needed for boolean operations

---

## Phase 6 — Intersection predicates (3D)

### 6.1 Segment-plane intersection

- [x] `segment_plane_intersection_parameter(d, e, a, b, c)` — returns parameter t (requires OrderedField)
- [x] `segment_plane_intersection_point(d, e, a, b, c)` — returns point (requires OrderedField)
- [x] Lemma: denominator is nonzero when segment strictly crosses plane
- [x] Lemma: returned point lies on the plane
- [x] Lemma: 0 < t < 1 for strict crossing
- [x] Lemma: point is affine combination of d and e at parameter t

### 6.2 Segment-triangle intersection

- [x] `segment_triangle_intersects_strict(seg_start, seg_end, tri_a, tri_b, tri_c)`
- [x] Algorithm: compute plane intersection point, project to 2D, test containment
- [x] Point-in-triangle via 2D projection (`point_in_triangle_on_plane`)
- [x] 2D projection helpers (`project_drop_x/y/z`, `project_by_axis`, `triangle_projection_axis`)
- [x] Lemma: segment-triangle implies crossing + endpoints off plane
- [x] Lemma: if intersection exists, the point lies on the plane, is strictly between endpoints (0<t<1), is the affine combination (1-t)*d+t*e, and is in the triangle

### 6.3 Segment-convex polygon overlap

- [x] `segment_overlaps_convex_polygon(seg_start, seg_end, polygon)` spec
      — endpoint inside OR hits any edge
- [x] Lemma: if either endpoint is inside the polygon, there is overlap
- [x] Prefix step lemma for edge hit induction

---

## Phase 7 — Runtime refinement layer

All of the above is spec-level. For actual computation we need exec functions
paired with their specs. This is where concrete numeric types come in.

### 7.1 Decide the approach

Two options:

**Option A: Generic exec functions with Ring + exec bounds**
- Pro: stays generic, one codebase
- Con: Verus may struggle with generic exec + proof obligations simultaneously

**Option B: Concrete exec functions over RuntimeRational (or RuntimeInterval)**
- Pro: simpler verification, matches old crate pattern
- Con: less reusable, need separate instantiations

- [x] Decided: Option B — concrete exec functions over RuntimeRational

### 7.2 Implement exec functions

For each predicate in Phases 1-6:
- [ ] Exec function calling runtime arithmetic
- [ ] Postcondition: output matches spec applied to input views (`self@`)
- [ ] Well-formedness preconditions on inputs

### 7.3 AABB utilities (for broad-phase)

- [x] `point_in_aabb2/3` — point containment specs
- [x] `aabb2/3_separated` — separation predicate specs
- [x] Lemma: separation implies no common point (2D and 3D)
- [x] `point_in_aabb2_exec`, `point_in_aabb3_exec` — exec point containment
- [x] `aabb2_separated_exec`, `aabb3_separated_exec` — exec separation tests

---

## Phase 8 — New predicates & correctness proofs

### 8.1 Point-on-segment lemmas

- [x] `lemma_weighted_average_bounds` — 0 ≤ t ≤ 1 implies min(a,b) ≤ a+t*(b-a) ≤ max(a,b)
- [x] `lemma_endpoint_a_on_segment`, `lemma_endpoint_b_on_segment`
- [x] `lemma_affine_combination_on_segment` — affine point with 0≤t≤1 is on segment
- [x] `lemma_proper_intersection_on_segment_ab` — proper intersection lies on segment AB
- [x] `lemma_proper_intersection_on_segment_cd` — proper intersection lies on segment CD (via CD parameter + uniqueness)

### 8.2 Convexity predicates

- [x] `is_convex_polygon` — global half-plane: every vertex non-negative for every edge (see docs/convexity-redesign.md)
- [x] `is_strictly_convex_polygon` — convex + non-adjacent vertices strictly positive
- [x] `is_locally_convex_polygon` — all consecutive triples have non-negative orientation (necessary but not sufficient)
- [x] `is_locally_strictly_convex_polygon` — all consecutive triples have strictly positive orientation
- [x] `lemma_convex_implies_locally_convex`
- [x] `lemma_locally_strictly_convex_implies_locally_convex`
- [x] `lemma_strictly_convex_implies_convex`
- [x] `lemma_vertex_in_convex_polygon` — vertex of convex polygon is boundary-inclusive (trivial from global definition)

### 8.3 Face normal predicates

- [x] `lemma_normal_orthogonal_to_edges` — triangle normal is orthogonal to both edges
- [x] `lemma_normal_swap_bc` — swapping b and c negates the normal
- [x] `faces_consistently_oriented` spec predicate
- [x] `lemma_consistent_orientation_symmetric` — consistent orientation is symmetric (proved via orient3d even-permutation lemma)

### 8.4 Barycentric coordinates

- [x] `barycentric_unnorm_2d` — unnormalized barycentric coordinate spec
- [x] `barycentric_coords_2d` — normalized barycentric coordinate spec (OrderedField)
- [x] `lemma_orient2d_repeated_ac` — orient2d(a, b, a) ≡ 0
- [x] `lemma_barycentric_sum_at_vertex_a/b/c` — unnormalized sum at each vertex equals orient2d(a,b,c)
- [x] `lemma_barycentric_partition_of_unity` — orient2d(b,c,p) + orient2d(c,a,p) + orient2d(a,b,p) ≡ orient2d(a,b,c)
- [x] `lemma_barycentric_reconstruction` — p ≡ u*a + v*b + w*c for normalized barycentric coordinates

### 8.5 Line-line closest approach (3D)

- [x] `line_point_3d`, `gram_entries`, `gram_determinant` specs
- [x] `closest_parameter_s`, `closest_parameter_t` specs
- [x] `line_line_squared_distance` spec
- [x] `lemma_closest_points_perpendicular` — closest-approach vector is orthogonal to both line directions

### 8.6 Disjoint-implies-no-shared-point

- [x] `lemma_shared_point_implies_not_disjoint` — contrapositive form

---

## Proof strategy notes

### Leveraging the Ring abstraction

The current design (generic over Ring) is powerful: proofs work for any
concrete type. But some predicates (sign extraction, sidedness) need
`OrderedRing` or `OrderedField`. Plan:

- Phases 1-2 lemmas that only need Ring stay generic
- Phases 3-6 require OrderedRing for sign comparisons
- Phase 7 runtime uses concrete OrderedField instances

### Reuse from verus-algebra

Many proof steps reduce to algebraic identities already proven:
- Distributivity, commutativity, associativity → ring_lemmas
- Sign of products → ordered_ring_lemmas / ordered_field_lemmas
- Min/max for AABB → min_max module
- Triangle inequality for distance bounds → inequalities module

### Reuse from verus-linalg

- Dot product properties → for sidedness (dot(n, p) determines side)
- Cross product properties → for collinearity3d and orient3d decomposition
- Scale properties → for intersection parameter computation

### Proof difficulty estimates

| Item | Difficulty | Notes |
|---|---|---|
| Sign extraction | Easy | Wraps existing orient + ordered_ring trichotomy |
| Collinearity 2D | Easy | orient2d == 0 |
| Collinearity 3D | Medium | Cross product zero, needs component-wise proof |
| Coplanarity | Easy | orient3d == 0 |
| Sidedness (point vs plane) | Easy | Sign of orient3d |
| Segment crossing (strict) | Medium | Two-sided sign argument |
| Segment intersection 2D (classification) | Hard | 4 orientation tests, case explosion |
| Segment intersection 2D (witness point) | Hard | Nonzero denominator proof, parameter bounds |
| Point-in-convex-polygon | Medium | Loop invariant over edge orientations |
| Segment-plane intersection | Medium | Algebraic parameter computation |
| Segment-triangle intersection | Hard | Combines plane intersection + 2D projection + containment |
| AABB operations | Easy | Direct interval comparisons |

---

## Trust surface

| Trusted | Why | Mitigation |
|---|---|---|
| `vstd` | Verus standard library | Maintained by Verus team |
| `verus-algebra` axioms | Ring/Field axiom soundness | Axioms match standard math definitions |
| `verus-linalg` | Vector operation specs | 533+ verified items, 0 assumes |

Everything in this crate: verified, no `unsafe`, no `assume`.
Enforced by `--forbid-trusted-escapes` in CI.

---

## Milestones

| Milestone | Phases | What it enables |
|---|---|---|
| **M1: Classification predicates** | 1-2 | Collinearity/coplanarity checks for topology validation |
| **M2: Sidedness & crossing** | 3 | Segment-plane crossing for face intersection detection |
| **M3: 2D intersection** | 4-5 | Segment intersection + polygon containment for boolean ops |
| **M4: 3D intersection** | 6 | Segment-triangle intersection for mesh self-intersection detection |
| **M5: Runtime layer** | 7 | Executable predicates for actual computation |
| **M6: Extended predicates** | 8 | Convexity, face normals, AABB, barycentric, distance |

**M1 is needed first** — verus-topology's geometric validation layer depends
on collinearity and coplanarity. **M3 is the big one** for boolean operations.

---

## Phase 9 — Next-generation predicates & proofs

### 9.1 Runtime 2D segment intersection point (OrderedField)

The spec `segment_intersection_point_2d` and `segment_intersection_parameter_2d` exist,
but there is no exec function to compute them at runtime. Classification-only is
insufficient for CSG/clipping — we need the actual intersection coordinates.

- [x] `segment_intersection_parameter_2d_exec(a, b, c, d) -> RuntimeRational`
      — ensures `out@ == segment_intersection_parameter_2d(a@, b@, c@, d@)`
      — requires: proper intersection (denominator nonzero)
- [x] `segment_intersection_point_2d_exec(a, b, c, d) -> RuntimePoint2`
      — ensures `out@ == segment_intersection_point_2d(a@, b@, c@, d@)`
      — computes `a + t * (b - a)` at runtime
- [x] `segment_intersection_parameter_cd_2d_exec` — the CD-side parameter (needed for overlap queries)
- [x] `segment_intersection_point_cd_2d_exec` — intersection point on CD

### 9.2 Incircle predicate (2D Delaunay)

The companion to orient2d for Delaunay triangulation. Tests whether point d lies
inside the circumcircle of triangle (a, b, c). This is a 3×3 determinant of the
"lifted" coordinates — no mat4x4 needed.

```
spec fn incircle2d<T: OrderedRing>(a, b, c, d: Point2<T>) -> T {
    //  | ax-dx  ay-dy  (ax-dx)²+(ay-dy)² |
    //  | bx-dx  by-dy  (bx-dx)²+(by-dy)² |
    //  | cx-dx  cy-dy  (cx-dx)²+(cy-dy)² |
    det3_lifted(a - d, b - d, c - d)
}
```

- [x] `incircle2d` spec (Ring-valued, sign gives inside/outside/on)
- [x] `incircle2d_sign` spec (OrderedRing → OrientationSign)
- [x] `incircle2d_positive/negative/cocircular` predicates
- [x] Lemma: degenerate when d coincides with a, b, or c (gives zero)
- [x] Lemma: trichotomy — exactly one of {positive, negative, cocircular} holds
- [x] Lemma: sign classification matches predicates
- [x] `incircle2d_sign_exec` — runtime sign classification
- [x] `incircle2d_compute` — runtime determinant computation
- [ ] Lemma: sign reverses under swap of any two of {a, b, c} (antisymmetry)
- [ ] Lemma: sign invariance under uniform translation
- [ ] Lemma: relation to orient2d — positive incircle when orient2d(a,b,c) > 0 means d is inside CCW circle

### 9.3 Signed polygon area

`signed_area(P) = (1/2) * Σ orient2d(origin, P[i], P[i+1])`. This is the fundamental
area computation and links orientation to magnitude.

For spec purposes we use the unnormalized (2×area) form to stay in Ring:

```
spec fn double_signed_area<T: Ring>(polygon: Seq<Point2<T>>) -> T {
    //  sum of orient2d(zero, polygon[i], polygon[next(i)]) for all i
}
```

- [x] `cross_origin` spec — shoelace term for two points
- [x] `signed_area_2x_prefix` spec — recursive prefix sum
- [x] `signed_area_2x` spec (Ring — no division needed)
- [x] `signed_area_2x_exec` for RuntimePolygon2
- [x] `lemma_cross_origin_is_det2d` — relates cross_origin to det2d
- [x] `lemma_prefix_unfold` — prefix sum step
- [ ] Lemma: triangle area equals orient2d(a, b, c) (3-vertex special case — needs ~30 algebraic steps)
- [ ] Lemma: reversing polygon negates area (orientation flip)
- [ ] Lemma: area-orientation consistency — for a convex polygon,
      `polygon_has_positive_sign ⟹ signed_area_2x positive` (and vice versa)
- [ ] Lemma: translation invariance — translating all vertices preserves area

### 9.4 General point-in-polygon (winding number)

For non-convex polygons. The winding number approach counts signed crossings
of a ray from p to infinity against polygon edges.

```
spec fn winding_number<T: OrderedRing>(p: Point2<T>, polygon: Seq<Point2<T>>) -> int
spec fn point_in_polygon<T: OrderedRing>(p: Point2<T>, polygon: Seq<Point2<T>>) -> bool {
    winding_number(p, polygon) != 0
}
```

- [x] `winding_edge` spec — +1 if upward left-crossing, -1 if downward right-crossing, 0 otherwise
- [x] `winding_number_prefix` spec — recursive prefix sum
- [x] `winding_number` spec — sum of edge crossing signs
- [x] `point_in_polygon` / `point_outside_polygon` specs — nonzero/zero winding number
- [x] `lemma_winding_prefix_unfold` — prefix sum step
- [x] `winding_edge_exec` — runtime edge contribution
- [x] `winding_number_exec` — runtime winding number with overflow bounds
- [x] `point_in_polygon_exec` — runtime point-in-polygon test
- [ ] Lemma: for convex polygon, `point_in_polygon ⟺ point_in_convex_polygon_boundary_inclusive`
      (connects general and convex-specific predicates)
- [ ] Lemma: winding number is invariant under cyclic vertex permutation
- [ ] Lemma: point outside AABB has winding number 0 (connects to broad-phase)

### 9.5 Ray-AABB intersection

BVH traversal primitive. Tests whether a ray from origin+direction intersects an AABB.
Uses slab method (interval intersection per axis).

- [ ] `ray_intersects_aabb2` spec (OrderedField — needs division for slab bounds)
- [ ] `ray_intersects_aabb3` spec
- [ ] Lemma: if AABB is separated from ray origin's AABB, result is consistent
- [ ] `ray_intersects_aabb2_exec`, `ray_intersects_aabb3_exec`

### 9.6 Point-segment distance (clamped)

Closest point on a segment (not the infinite line). Needed for proximity queries.

- [ ] `closest_point_on_segment_2d` spec (OrderedField — clamp parameter to [0,1])
- [ ] `closest_point_on_segment_3d` spec
- [ ] `squared_distance_point_segment_2d/3d` spec
- [ ] Lemma: closest point lies on segment (parameter in [0,1])
- [ ] Lemma: closest point minimizes distance (dot-product optimality condition)
- [ ] Exec functions for 2D and 3D

### 9.7 Point-triangle distance (3D) — Voronoi region classification

Classifies the closest feature (vertex/edge/face) and computes squared distance.

- [ ] `triangle_voronoi_region` spec — which region the projection falls in
- [ ] `closest_point_on_triangle_3d` spec
- [ ] `squared_distance_point_triangle_3d` spec
- [ ] Lemma: closest point is on the triangle
- [ ] Exec functions

### 9.8 Ray-triangle intersection (Möller-Trumbore)

Extends segment-triangle to rays. Critical for picking and visibility.

- [ ] `ray_triangle_parameter` spec (OrderedField)
- [ ] `ray_triangle_intersects` spec — parameter ≥ 0 and barycentric coords in-bounds
- [ ] Lemma: intersection point lies on both ray and triangle plane
- [ ] Lemma: barycentric coords of intersection are non-negative and sum to 1
- [ ] Exec functions

### 9.9 Triangle-triangle intersection (3D) — deferred until mat4x4 done

Core primitive for mesh boolean operations. Uses orient3d to classify each
triangle's vertices against the other's plane, then computes the intersection
segment.

- [ ] `triangle_triangle_intersects` spec
- [ ] Lemma: if both triangles are on the same plane, reduce to 2D overlap
- [ ] Lemma: general case — intersection is a segment (or empty/point)
- [ ] Exec functions

### 9.10 Insphere predicate (3D Delaunay) — deferred until mat4x4 done

4×4 determinant testing whether point e lies inside the circumsphere of
tetrahedron (a, b, c, d). Analogous to incircle but one dimension up.

- [ ] `insphere3d` spec
- [ ] Sign classification + antisymmetry lemmas
- [ ] Exec function

---

## Priority order for Phase 9

| Priority | Item | Effort | Unlocks |
|---|---|---|---|
| **P0** | 9.1 Runtime intersection point | Small | CSG, clipping, any intersection computation |
| **P1** | 9.2 Incircle | Medium | Delaunay triangulation |
| **P2** | 9.3 Signed area | Small-Medium | Polygon validity, orientation checks |
| **P3** | 9.4 General point-in-polygon | Medium | Non-convex polygon workflows |
| **P4** | 9.5 Ray-AABB | Small | BVH traversal |
| **P5** | 9.6 Point-segment distance | Small-Medium | Proximity queries |
| **P6** | 9.7 Point-triangle distance | Medium | Collision detection, mesh repair |
| **P7** | 9.8 Ray-triangle | Medium | Picking, visibility |
| **P8** | 9.9 Triangle-triangle | Hard | Mesh booleans (needs mat4x4) |
| **P9** | 9.10 Insphere | Medium | 3D Delaunay (needs mat4x4) |
