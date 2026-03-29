use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;

verus! {

//  =========================================================================
//  Polygon indexing helpers
//  =========================================================================

///  Next vertex index, wrapping around.
pub open spec fn polygon_next_index(len: int, i: int) -> int
    recommends
        len > 0,
        0 <= i < len,
{
    if i + 1 < len { i + 1 } else { 0 }
}

//  =========================================================================
//  Edge orientation sign
//  =========================================================================

///  Orientation sign of point p with respect to edge i->(i+1) of the polygon.
pub open spec fn polygon_edge_orient_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, i: int,
) -> OrientationSign
    recommends
        polygon.len() >= 3,
        0 <= i < polygon.len(),
{
    orient2d_sign(
        polygon[i],
        polygon[polygon_next_index(polygon.len() as int, i)],
        p,
    )
}

//  =========================================================================
//  Prefix predicates — has any edge in [0, upto) with given sign?
//  =========================================================================

///  Some edge in [0, upto) has Positive orientation with p.
pub open spec fn polygon_prefix_has_positive_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, upto: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len(),
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Positive
}

///  Some edge in [0, upto) has Negative orientation with p.
pub open spec fn polygon_prefix_has_negative_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, upto: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len(),
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Negative
}

///  Some edge in [0, upto) has Zero orientation with p.
pub open spec fn polygon_prefix_has_zero_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, upto: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len(),
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Zero
}

//  =========================================================================
//  Full-polygon predicates
//  =========================================================================

///  Some edge has Positive orientation with p.
pub open spec fn polygon_has_positive_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    polygon_prefix_has_positive_sign(p, polygon, polygon.len() as int)
}

///  Some edge has Negative orientation with p.
pub open spec fn polygon_has_negative_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    polygon_prefix_has_negative_sign(p, polygon, polygon.len() as int)
}

///  Some edge has Zero orientation with p (p on an edge).
pub open spec fn polygon_has_zero_sign<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    polygon_prefix_has_zero_sign(p, polygon, polygon.len() as int)
}

//  =========================================================================
//  Main containment predicates
//  =========================================================================

///  Point p is inside or on the boundary of a convex polygon.
///
///  Precondition (not enforced): polygon is convex with consistent winding.
///  Algorithm: p is NOT (left of some edge AND right of some other edge).
pub open spec fn point_in_convex_polygon_boundary_inclusive<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_sign(p, polygon) && polygon_has_negative_sign(p, polygon))
}

///  Point p is strictly inside a convex polygon (excludes boundary).
///
///  Precondition (not enforced): polygon is convex with consistent winding.
///  All edge orientations have the same nonzero sign.
pub open spec fn point_strictly_in_convex_polygon<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_sign(p, polygon) && polygon_has_negative_sign(p, polygon))
    &&& !polygon_has_zero_sign(p, polygon)
}

//  =========================================================================
//  Prefix step lemmas (inductive structure for loop invariants)
//  =========================================================================

///  Inductive step for prefix positive sign.
pub proof fn lemma_prefix_positive_step<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, i: int,
)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len(),
    ensures
        polygon_prefix_has_positive_sign(p, polygon, i + 1)
            == (polygon_prefix_has_positive_sign(p, polygon, i)
                || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Positive),
{
    if polygon_prefix_has_positive_sign(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1
            && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Positive;
        if j < i {
            assert(polygon_prefix_has_positive_sign(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Positive);
        }
    }
    if polygon_prefix_has_positive_sign(p, polygon, i)
        || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Positive
    {
        if polygon_prefix_has_positive_sign(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i
                && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Positive;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_positive_sign(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_positive_sign(p, polygon, i + 1));
        }
    }
}

///  Inductive step for prefix negative sign.
pub proof fn lemma_prefix_negative_step<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, i: int,
)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len(),
    ensures
        polygon_prefix_has_negative_sign(p, polygon, i + 1)
            == (polygon_prefix_has_negative_sign(p, polygon, i)
                || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Negative),
{
    if polygon_prefix_has_negative_sign(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1
            && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Negative;
        if j < i {
            assert(polygon_prefix_has_negative_sign(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Negative);
        }
    }
    if polygon_prefix_has_negative_sign(p, polygon, i)
        || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Negative
    {
        if polygon_prefix_has_negative_sign(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i
                && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Negative;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_negative_sign(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_negative_sign(p, polygon, i + 1));
        }
    }
}

///  Inductive step for prefix zero sign.
pub proof fn lemma_prefix_zero_step<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>, i: int,
)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len(),
    ensures
        polygon_prefix_has_zero_sign(p, polygon, i + 1)
            == (polygon_prefix_has_zero_sign(p, polygon, i)
                || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Zero),
{
    if polygon_prefix_has_zero_sign(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1
            && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Zero;
        if j < i {
            assert(polygon_prefix_has_zero_sign(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Zero);
        }
    }
    if polygon_prefix_has_zero_sign(p, polygon, i)
        || polygon_edge_orient_sign(p, polygon, i) == OrientationSign::Zero
    {
        if polygon_prefix_has_zero_sign(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i
                && polygon_edge_orient_sign(p, polygon, j) == OrientationSign::Zero;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_zero_sign(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_zero_sign(p, polygon, i + 1));
        }
    }
}

//  =========================================================================
//  Containment relationship lemmas
//  =========================================================================

///  Boundary-inclusive is a superset of strict.
pub proof fn lemma_strict_implies_boundary_inclusive<T: OrderedRing>(
    p: Point2<T>, polygon: Seq<Point2<T>>,
)
    requires
        point_strictly_in_convex_polygon(p, polygon),
    ensures
        point_in_convex_polygon_boundary_inclusive(p, polygon),
{
    //  Direct from definitions: strict adds !has_zero on top of boundary-inclusive.
}

} //  verus!
