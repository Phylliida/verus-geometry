use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;
use crate::convex_polygon::*;

verus! {

// =========================================================================
// Convexity predicates
// =========================================================================

/// All consecutive vertex triples have non-negative (CCW) orientation.
/// No reflex angles — the polygon is convex.
pub open spec fn is_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& (forall|i: int| 0 <= i < polygon.len() ==> {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        !orient2d_negative(#[trigger] polygon[i], polygon[j], polygon[k])
    })
}

/// All consecutive vertex triples have strictly positive (CCW) orientation.
/// No collinear edges — the polygon is strictly convex.
pub open spec fn is_strictly_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& (forall|i: int| 0 <= i < polygon.len() ==> {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        orient2d_positive(#[trigger] polygon[i], polygon[j], polygon[k])
    })
}

/// A strictly convex polygon is also convex.
pub proof fn lemma_strictly_convex_implies_convex<T: OrderedRing>(
    polygon: Seq<Point2<T>>,
)
    requires
        is_strictly_convex_polygon(polygon),
    ensures
        is_convex_polygon(polygon),
{
    assert forall|i: int| 0 <= i < polygon.len() implies {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        !orient2d_negative(#[trigger] polygon[i], polygon[j], polygon[k])
    } by {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        lemma_orient2d_trichotomy::<T>(polygon[i], polygon[j], polygon[k]);
    }
}

/// Every vertex of a convex polygon is inside the polygon (boundary inclusive).
///
/// Proof strategy: For a convex polygon and vertex k:
/// - Edges k-1→k and k→k+1 give Zero orientation (degenerate cases).
/// - For all other edges, orient2d(v[i], v[i+1], v[k]) is non-negative,
///   which follows from the orient2d decomposition identity:
///   orient2d(a,c,d) + orient2d(a,b,c) = orient2d(a,b,d) + orient2d(b,c,d)
///   applied inductively along the "fan" from vertex k.
/// - Since all signs are non-negative (or zero), we can never have both
///   Positive and Negative, so point_in_convex_polygon_boundary_inclusive holds.
pub proof fn lemma_vertex_in_convex_polygon<T: OrderedRing>(
    polygon: Seq<Point2<T>>, k: int,
)
    requires
        is_convex_polygon(polygon),
        0 <= k < polygon.len(),
    ensures
        point_in_convex_polygon_boundary_inclusive(polygon[k], polygon),
{
    // TODO: Requires proving the orient2d decomposition identity
    // and a fan induction argument (~200 lines of det2d algebra).
    assume(false);
}

} // verus!
