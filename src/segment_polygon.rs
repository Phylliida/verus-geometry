use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::segment_intersection::*;
use crate::convex_polygon::*;

verus! {

// =========================================================================
// 6.3 — Segment-convex polygon overlap (2D)
// =========================================================================

/// Does the segment hit polygon edge i (non-disjoint intersection)?
pub open spec fn segment_hits_polygon_edge<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>, i: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= i < polygon.len(),
{
    let j = polygon_next_index(polygon.len() as int, i);
    !(segment_intersection_kind_2d(seg_start, seg_end, polygon[i], polygon[j])
        == SegmentIntersection2dKind::Disjoint)
}

/// Does the segment hit any polygon edge in [0, upto)?
pub open spec fn segment_prefix_hits_polygon_edge<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>, upto: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len(),
{
    exists|i: int| 0 <= i < upto
        && segment_hits_polygon_edge(seg_start, seg_end, polygon, i)
}

/// Does the segment hit any polygon edge?
pub open spec fn segment_hits_some_polygon_edge<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, polygon.len() as int)
}

/// Segment overlaps a convex polygon: either an endpoint is inside the
/// polygon (boundary-inclusive) or the segment hits at least one edge.
pub open spec fn segment_overlaps_convex_polygon<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>,
) -> bool {
    &&& polygon.len() >= 3
    &&& (
        point_in_convex_polygon_boundary_inclusive(seg_start, polygon)
        || point_in_convex_polygon_boundary_inclusive(seg_end, polygon)
        || segment_hits_some_polygon_edge(seg_start, seg_end, polygon)
    )
}

// =========================================================================
// Lemmas
// =========================================================================

/// Inductive step for prefix edge hits.
pub proof fn lemma_prefix_hits_edge_step<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>, i: int,
)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len(),
    ensures
        segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i + 1)
            == (segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i)
                || segment_hits_polygon_edge(seg_start, seg_end, polygon, i)),
{
    if segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1
            && segment_hits_polygon_edge(seg_start, seg_end, polygon, j);
        if j < i {
            assert(segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i));
        } else {
            assert(j == i);
            assert(segment_hits_polygon_edge(seg_start, seg_end, polygon, i));
        }
    }
    if segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i)
        || segment_hits_polygon_edge(seg_start, seg_end, polygon, i)
    {
        if segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i) {
            let j = choose|j: int| 0 <= j < i
                && segment_hits_polygon_edge(seg_start, seg_end, polygon, j);
            assert(0 <= j < i + 1);
            assert(segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(segment_prefix_hits_polygon_edge(seg_start, seg_end, polygon, i + 1));
        }
    }
}

/// If either endpoint is inside the polygon, there is overlap.
pub proof fn lemma_endpoint_inside_implies_overlap<T: OrderedRing>(
    seg_start: Point2<T>, seg_end: Point2<T>,
    polygon: Seq<Point2<T>>,
)
    requires
        point_in_convex_polygon_boundary_inclusive(seg_start, polygon)
        || point_in_convex_polygon_boundary_inclusive(seg_end, polygon),
    ensures
        segment_overlaps_convex_polygon(seg_start, seg_end, polygon),
{
    // Direct from definition: endpoint inside implies polygon.len() >= 3
    // (since boundary_inclusive requires len >= 3) and the disjunction holds.
}

} // verus!
