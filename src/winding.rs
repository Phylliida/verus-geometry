use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::orient2d::*;
use crate::convex_polygon::polygon_next_index;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// Winding contribution of a single directed edge (p0→p1) with respect to
/// query point q, using the standard crossing-number rule:
///
///   +1  if p0.y ≤ q.y < p1.y  AND  orient2d(p0, p1, q) > 0   (upward left-crossing)
///   -1  if p1.y ≤ q.y < p0.y  AND  orient2d(p0, p1, q) < 0   (downward right-crossing)
///    0  otherwise
pub open spec fn winding_edge<T: OrderedRing>(
    q: Point2<T>, p0: Point2<T>, p1: Point2<T>,
) -> int {
    let o = orient2d(p0, p1, q);
    if p0.y.le(q.y) && q.y.lt(p1.y) && T::zero().lt(o) {
        1int
    } else if p1.y.le(q.y) && q.y.lt(p0.y) && o.lt(T::zero()) {
        -1int
    } else {
        0int
    }
}

/// Recursive prefix sum of winding contributions for edges [0, k).
pub open spec fn winding_number_prefix<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
) -> int
    recommends
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        let i = k - 1;
        let j = polygon_next_index(polygon.len() as int, i);
        winding_number_prefix(q, polygon, i)
            + winding_edge(q, polygon[i], polygon[j])
    }
}

/// Winding number of query point q with respect to polygon.
pub open spec fn winding_number<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> int
    recommends polygon.len() >= 3,
{
    winding_number_prefix(q, polygon, polygon.len() as int)
}

/// Point is inside polygon (nonzero winding number).
pub open spec fn point_in_polygon<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    winding_number(q, polygon) != 0int
}

/// Point is outside polygon (zero winding number).
pub open spec fn point_outside_polygon<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    winding_number(q, polygon) == 0int
}

// ---------------------------------------------------------------------------
// Prefix unfold lemma
// ---------------------------------------------------------------------------

/// Adding one more edge contribution to the winding prefix sum.
pub proof fn lemma_winding_prefix_unfold<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 < k <= polygon.len(),
    ensures
        winding_number_prefix(q, polygon, k) ==
            winding_number_prefix(q, polygon, k - 1)
                + winding_edge(
                    q,
                    polygon[k - 1],
                    polygon[polygon_next_index(polygon.len() as int, k - 1)]
                ),
{
    // Direct from definition
}

} // verus!
