use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::point3::*;

verus! {

// =========================================================================
// AABB specs
// =========================================================================

/// Point p is inside the 2D axis-aligned bounding box [min, max].
pub open spec fn point_in_aabb2<T: OrderedRing>(
    p: Point2<T>, min: Point2<T>, max: Point2<T>,
) -> bool {
    min.x.le(p.x) && p.x.le(max.x)
    && min.y.le(p.y) && p.y.le(max.y)
}

/// Point p is inside the 3D axis-aligned bounding box [min, max].
pub open spec fn point_in_aabb3<T: OrderedRing>(
    p: Point3<T>, min: Point3<T>, max: Point3<T>,
) -> bool {
    min.x.le(p.x) && p.x.le(max.x)
    && min.y.le(p.y) && p.y.le(max.y)
    && min.z.le(p.z) && p.z.le(max.z)
}

/// Two 3D AABBs are separated along some axis.
pub open spec fn aabb3_separated<T: OrderedRing>(
    min_a: Point3<T>, max_a: Point3<T>,
    min_b: Point3<T>, max_b: Point3<T>,
) -> bool {
    max_a.x.lt(min_b.x) || max_b.x.lt(min_a.x)
    || max_a.y.lt(min_b.y) || max_b.y.lt(min_a.y)
    || max_a.z.lt(min_b.z) || max_b.z.lt(min_a.z)
}

/// Two 2D AABBs are separated along some axis.
pub open spec fn aabb2_separated<T: OrderedRing>(
    min_a: Point2<T>, max_a: Point2<T>,
    min_b: Point2<T>, max_b: Point2<T>,
) -> bool {
    max_a.x.lt(min_b.x) || max_b.x.lt(min_a.x)
    || max_a.y.lt(min_b.y) || max_b.y.lt(min_a.y)
}

// =========================================================================
// AABB lemmas
// =========================================================================

/// Helper: a ≤ b and b < c is contradictory with c ≤ a.
pub proof fn lemma_le_lt_contradiction<T: OrderedRing>(a: T, b: T, c: T)
    requires
        a.le(b),
        b.lt(c),
        c.le(a),
    ensures
        false,
{
    // b < c → b ≤ c ∧ ¬(b ≡ c)
    T::axiom_lt_iff_le_and_not_eqv(b, c);
    // c ≤ a ≤ b → c ≤ b
    T::axiom_le_transitive(c, a, b);
    // b ≤ c ∧ c ≤ b → b ≡ c
    T::axiom_le_antisymmetric(b, c);
    // Contradiction: ¬(b ≡ c) but b ≡ c
}

/// If two 3D AABBs are separated, no point can be in both.
pub proof fn lemma_aabb3_separation_implies_no_common_point<T: OrderedRing>(
    p: Point3<T>,
    min_a: Point3<T>, max_a: Point3<T>,
    min_b: Point3<T>, max_b: Point3<T>,
)
    requires
        aabb3_separated(min_a, max_a, min_b, max_b),
        point_in_aabb3(p, min_a, max_a),
    ensures
        !point_in_aabb3(p, min_b, max_b),
{
    if point_in_aabb3(p, min_b, max_b) {
        // p in aabb_a: min_a.c ≤ p.c ≤ max_a.c
        // p in aabb_b: min_b.c ≤ p.c ≤ max_b.c
        // Separation: some axis has max_a.c < min_b.c or max_b.c < min_a.c
        // Contradiction: p.c ≤ max_a.c < min_b.c ≤ p.c
        if max_a.x.lt(min_b.x) {
            lemma_le_lt_contradiction::<T>(p.x, max_a.x, min_b.x);
        } else if max_b.x.lt(min_a.x) {
            lemma_le_lt_contradiction::<T>(p.x, max_b.x, min_a.x);
        } else if max_a.y.lt(min_b.y) {
            lemma_le_lt_contradiction::<T>(p.y, max_a.y, min_b.y);
        } else if max_b.y.lt(min_a.y) {
            lemma_le_lt_contradiction::<T>(p.y, max_b.y, min_a.y);
        } else if max_a.z.lt(min_b.z) {
            lemma_le_lt_contradiction::<T>(p.z, max_a.z, min_b.z);
        } else {
            lemma_le_lt_contradiction::<T>(p.z, max_b.z, min_a.z);
        }
    }
}

/// If two 2D AABBs are separated, no point can be in both.
pub proof fn lemma_aabb2_separation_implies_no_common_point<T: OrderedRing>(
    p: Point2<T>,
    min_a: Point2<T>, max_a: Point2<T>,
    min_b: Point2<T>, max_b: Point2<T>,
)
    requires
        aabb2_separated(min_a, max_a, min_b, max_b),
        point_in_aabb2(p, min_a, max_a),
    ensures
        !point_in_aabb2(p, min_b, max_b),
{
    if point_in_aabb2(p, min_b, max_b) {
        if max_a.x.lt(min_b.x) {
            lemma_le_lt_contradiction::<T>(p.x, max_a.x, min_b.x);
        } else if max_b.x.lt(min_a.x) {
            lemma_le_lt_contradiction::<T>(p.x, max_b.x, min_a.x);
        } else if max_a.y.lt(min_b.y) {
            lemma_le_lt_contradiction::<T>(p.y, max_a.y, min_b.y);
        } else {
            lemma_le_lt_contradiction::<T>(p.y, max_b.y, min_a.y);
        }
    }
}

} // verus!
