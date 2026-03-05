use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_linalg::vec2::Vec2;
use crate::point2::*;
use crate::orient2d::*;
use crate::convex_polygon::polygon_next_index;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// Cross product of two points treated as position vectors from origin:
/// cross_origin(p, q) = p.x * q.y - p.y * q.x
pub open spec fn cross_origin<T: Ring>(p: Point2<T>, q: Point2<T>) -> T {
    p.x.mul(q.y).sub(p.y.mul(q.x))
}

/// Recursive prefix sum of shoelace terms for edges [0, k).
/// Each term is cross_origin(polygon[i], polygon[(i+1) % n]).
pub open spec fn signed_area_2x_prefix<T: Ring>(
    polygon: Seq<Point2<T>>, k: int,
) -> T
    recommends
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
    decreases k,
{
    if k <= 0 {
        T::zero()
    } else {
        let i = k - 1;
        let j = polygon_next_index(polygon.len() as int, i);
        signed_area_2x_prefix(polygon, i).add(cross_origin(polygon[i], polygon[j]))
    }
}

/// Twice the signed area of a simple polygon (shoelace formula).
/// Positive for CCW winding, negative for CW, zero for degenerate.
pub open spec fn signed_area_2x<T: Ring>(polygon: Seq<Point2<T>>) -> T
    recommends polygon.len() >= 3,
{
    signed_area_2x_prefix(polygon, polygon.len() as int)
}

// ---------------------------------------------------------------------------
// Lemma: cross_origin relates to det2d
// ---------------------------------------------------------------------------

/// cross_origin(p, q) ≡ det2d(Vec2{p.x, p.y}, Vec2{q.x, q.y})
pub proof fn lemma_cross_origin_is_det2d<T: Ring>(p: Point2<T>, q: Point2<T>)
    ensures
        cross_origin(p, q).eqv(
            det2d(Vec2 { x: p.x, y: p.y }, Vec2 { x: q.x, y: q.y })
        ),
{
    // Both expand to p.x.mul(q.y).sub(p.y.mul(q.x))
    T::axiom_eqv_reflexive(cross_origin(p, q));
}

// ---------------------------------------------------------------------------
// Prefix sum unfold (for exec loop invariant)
// ---------------------------------------------------------------------------

/// Adding one more edge term to the prefix sum.
pub proof fn lemma_prefix_unfold<T: Ring>(
    polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 < k <= polygon.len(),
    ensures
        signed_area_2x_prefix(polygon, k) ==
            signed_area_2x_prefix(polygon, k - 1).add(
                cross_origin(
                    polygon[k - 1],
                    polygon[polygon_next_index(polygon.len() as int, k - 1)]
                )
            ),
{
    // Direct from definition
}

// NOTE: lemma_triangle_area_is_orient2d (signed_area_2x([a,b,c]) ≡ orient2d(a,b,c))
// is a valid Ring identity but requires ~30 explicit distributivity/commutativity steps.
// Deferred for a later pass.

} // verus!
