use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec2::ops::norm_sq as norm_sq2;
use verus_linalg::vec3::ops::norm_sq as norm_sq3;
use crate::point2::*;
use crate::point3::*;
use crate::orient2d::orient2d;
use crate::closest_point::*;

verus! {

// ---------------------------------------------------------------------------
// Min helpers
// ---------------------------------------------------------------------------

/// Minimum of two values in an ordered ring.
pub open spec fn min_of<T: OrderedRing>(a: T, b: T) -> T {
    if a.le(b) { a } else { b }
}

/// Minimum of three values.
pub open spec fn min_of_three<T: OrderedRing>(a: T, b: T, c: T) -> T {
    min_of(a, min_of(b, c))
}

// ---------------------------------------------------------------------------
// 2D: Point in triangle
// ---------------------------------------------------------------------------

/// Point q is inside triangle (a, b, c), boundary inclusive.
///
/// Uses orient2d sign consistency: all three sub-orientations must have the
/// same sign (all ≥ 0 or all ≤ 0).
pub open spec fn point_in_triangle_2d<T: OrderedRing>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    let o1 = orient2d(a, b, q);
    let o2 = orient2d(b, c, q);
    let o3 = orient2d(c, a, q);
    (T::zero().le(o1) && T::zero().le(o2) && T::zero().le(o3))
    || (o1.le(T::zero()) && o2.le(T::zero()) && o3.le(T::zero()))
}

// ---------------------------------------------------------------------------
// 2D: Point-triangle squared distance
// ---------------------------------------------------------------------------

/// Squared distance from point q to triangle (a, b, c) in 2D.
///
/// If q is inside or on the boundary, distance is zero.
/// Otherwise, returns the minimum of the three edge squared distances.
pub open spec fn squared_distance_point_triangle_2d<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> T
    recommends
        !norm_sq2(sub2(b, a)).eqv(T::zero()),
        !norm_sq2(sub2(c, b)).eqv(T::zero()),
        !norm_sq2(sub2(a, c)).eqv(T::zero()),
{
    if point_in_triangle_2d(q, a, b, c) {
        T::zero()
    } else {
        let d_ab = squared_distance_point_segment_2d(q, a, b);
        let d_bc = squared_distance_point_segment_2d(q, b, c);
        let d_ca = squared_distance_point_segment_2d(q, c, a);
        min_of_three(d_ab, d_bc, d_ca)
    }
}

// ---------------------------------------------------------------------------
// 3D: Point-triangle edge squared distance (conservative)
// ---------------------------------------------------------------------------

/// Minimum squared distance from point q to the three edges of triangle
/// (a, b, c) in 3D. This is a conservative upper bound on the true
/// point-triangle distance — it is exact when the closest point lies on
/// an edge or vertex, but may overestimate when the closest point is
/// the interior projection.
pub open spec fn min_edge_squared_distance_3d<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> T
    recommends
        !norm_sq3(sub3(b, a)).eqv(T::zero()),
        !norm_sq3(sub3(c, b)).eqv(T::zero()),
        !norm_sq3(sub3(a, c)).eqv(T::zero()),
{
    let d_ab = squared_distance_point_segment_3d(q, a, b);
    let d_bc = squared_distance_point_segment_3d(q, b, c);
    let d_ca = squared_distance_point_segment_3d(q, c, a);
    min_of_three(d_ab, d_bc, d_ca)
}

} // verus!
