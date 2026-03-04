use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;
use crate::convex_polygon::*;

verus! {

// =========================================================================
// Local convexity predicates (consecutive triples only)
// =========================================================================

/// All consecutive vertex triples have non-negative (CCW) orientation.
/// WARNING: This is necessary but NOT sufficient for true convexity —
/// it admits star polygons (see docs/convexity-redesign.md).
pub open spec fn is_locally_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& (forall|i: int| 0 <= i < polygon.len() ==> {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        !orient2d_negative(#[trigger] polygon[i], polygon[j], polygon[k])
    })
}

/// All consecutive vertex triples have strictly positive (CCW) orientation.
/// WARNING: This is necessary but NOT sufficient for true strict convexity —
/// it admits star polygons (see docs/convexity-redesign.md).
pub open spec fn is_locally_strictly_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& (forall|i: int| 0 <= i < polygon.len() ==> {
        let j = polygon_next_index(polygon.len() as int, i);
        let k = polygon_next_index(polygon.len() as int, j);
        orient2d_positive(#[trigger] polygon[i], polygon[j], polygon[k])
    })
}

// =========================================================================
// Global convexity predicates (half-plane definition)
// =========================================================================

/// Every vertex lies on the non-negative side of every directed edge.
/// This is the standard mathematical definition: the polygon is the
/// intersection of half-planes defined by its edges.
pub open spec fn is_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& polygon.len() >= 3
    &&& (forall|i: int, j: int|
        0 <= i < polygon.len() && 0 <= j < polygon.len() ==> {
        let next_i = polygon_next_index(polygon.len() as int, i);
        !orient2d_negative(#[trigger] polygon[i], polygon[next_i], #[trigger] polygon[j])
    })
}

/// Every non-adjacent vertex is strictly on the positive side of every
/// directed edge, and the polygon is (globally) convex.
pub open spec fn is_strictly_convex_polygon<T: OrderedRing>(polygon: Seq<Point2<T>>) -> bool {
    &&& is_convex_polygon(polygon)
    &&& (forall|i: int, j: int|
        0 <= i < polygon.len() && 0 <= j < polygon.len()
        && j != i && j != polygon_next_index(polygon.len() as int, i) ==> {
        let next_i = polygon_next_index(polygon.len() as int, i);
        orient2d_positive(#[trigger] polygon[i], polygon[next_i], #[trigger] polygon[j])
    })
}

// =========================================================================
// Relationships between local and global convexity
// =========================================================================

/// Global convexity implies local convexity (consecutive triples are
/// a special case of all pairs).
pub proof fn lemma_convex_implies_locally_convex<T: OrderedRing>(
    polygon: Seq<Point2<T>>,
)
    requires
        is_convex_polygon(polygon),
    ensures
        is_locally_convex_polygon(polygon),
{
    let n = polygon.len() as int;
    assert forall|i: int| 0 <= i < polygon.len() implies {
        let j = polygon_next_index(n, i);
        let k = polygon_next_index(n, j);
        !orient2d_negative(#[trigger] polygon[i], polygon[j], polygon[k])
    } by {
        let j = polygon_next_index(n, i);
        let k = polygon_next_index(n, j);
        // k is a vertex, so the global condition with edge (i, j) and vertex k applies.
        // We need: 0 <= k < n. polygon_next_index always returns a value in [0, n).
        assert(0 <= k < n);
        // The global condition gives !orient2d_negative(polygon[i], polygon[j], polygon[k])
        // since polygon[j] == polygon[next_i] by definition of j.
        assert(!orient2d_negative(polygon[i], polygon[j], polygon[k]));
    }
}

/// A locally strictly convex polygon is also locally convex.
pub proof fn lemma_locally_strictly_convex_implies_locally_convex<T: OrderedRing>(
    polygon: Seq<Point2<T>>,
)
    requires
        is_locally_strictly_convex_polygon(polygon),
    ensures
        is_locally_convex_polygon(polygon),
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

/// A strictly convex polygon is also convex (global versions).
pub proof fn lemma_strictly_convex_implies_convex<T: OrderedRing>(
    polygon: Seq<Point2<T>>,
)
    requires
        is_strictly_convex_polygon(polygon),
    ensures
        is_convex_polygon(polygon),
{
    // Direct from definition: is_strictly_convex_polygon includes is_convex_polygon.
}

// =========================================================================
// Vertex-in-polygon lemma (now trivial from global definition)
// =========================================================================

/// Every vertex of a convex polygon is inside the polygon (boundary inclusive).
///
/// With the global half-plane definition, this is immediate: every vertex
/// is on the non-negative side of every edge (by definition), so no vertex
/// can see both Positive and Negative signs, which is exactly the
/// point_in_convex_polygon_boundary_inclusive predicate.
pub proof fn lemma_vertex_in_convex_polygon<T: OrderedRing>(
    polygon: Seq<Point2<T>>, k: int,
)
    requires
        is_convex_polygon(polygon),
        0 <= k < polygon.len(),
    ensures
        point_in_convex_polygon_boundary_inclusive(polygon[k], polygon),
{
    let p = polygon[k];
    let n = polygon.len() as int;

    // We need: !(has_positive && has_negative)
    // i.e., NOT (exists edge with Positive AND exists edge with Negative).
    //
    // From is_convex_polygon, for all edges i:
    //   !orient2d_negative(polygon[i], polygon[next(i)], polygon[k])
    // This means no edge gives Negative orientation for vertex k.
    // So polygon_has_negative_sign(p, polygon) is false.

    // Show that no edge has negative sign for point p = polygon[k]
    assert forall|i: int| 0 <= i < n implies
        polygon_edge_orient_sign(p, polygon, i) != OrientationSign::Negative
    by {
        let next_i = polygon_next_index(n, i);
        // From is_convex_polygon: !orient2d_negative(polygon[i], polygon[next_i], polygon[k])
        assert(!orient2d_negative(polygon[i], polygon[next_i], polygon[k]));
        // polygon_edge_orient_sign(p, polygon, i) = orient2d_sign(polygon[i], polygon[next_i], p)
        // and p == polygon[k], so this is orient2d_sign(polygon[i], polygon[next_i], polygon[k])
        lemma_orient2d_sign_matches::<T>(polygon[i], polygon[next_i], p);
        // orient2d_sign == Negative iff orient2d_negative, and we have !orient2d_negative
    }

    // Therefore polygon_has_negative_sign(p, polygon) is false
    // (no witness exists in [0, n))
    assert(!polygon_has_negative_sign(p, polygon));
}

} // verus!
