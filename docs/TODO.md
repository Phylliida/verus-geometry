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

117 verified items, 0 errors, 0 assumes/admits.

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
    Proper,           // interiors cross
    EndpointTouch,    // endpoint meets other segment
    CollinearOverlap, // collinear and overlapping
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
- [ ] Lemma: Disjoint implies no shared point exists

### 4.2 Segment intersection point (for Proper and EndpointTouch)

- [x] `segment_intersection_point_2d(a, b, c, d)` — compute witness point
- [x] For Proper: parameter `t = orient2d(c,d,a) / (orient2d(c,d,a) - orient2d(c,d,b))`, point = `a + t*(b-a)`
- [ ] Lemma: witness point lies on both segments (on-line AB done; on-line CD done; bounding box remaining)
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
- [ ] Lemma: vertices of the polygon are boundary-inclusive
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

- [ ] Decide approach (probably Option B initially, generalize later)

### 7.2 Implement exec functions

For each predicate in Phases 1-6:
- [ ] Exec function calling runtime arithmetic
- [ ] Postcondition: output matches spec applied to input views (`self@`)
- [ ] Well-formedness preconditions on inputs

### 7.3 AABB utilities (for broad-phase)

- [ ] `Aabb2` / `Aabb3` — axis-aligned bounding boxes
- [ ] `aabb_overlap(a, b)` — broad-phase intersection test
- [ ] `aabb_contains_point(box, p)` — containment test
- [ ] These are simple interval comparisons — should be easy to verify

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
| `verus-linalg` | Vector operation specs | 195+ verified items, 0 assumes |

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

**M1 is needed first** — verus-topology's geometric validation layer depends
on collinearity and coplanarity. **M3 is the big one** for boolean operations.
