#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::polygon::RuntimePolygon2;
#[cfg(verus_keep_ghost)]
use super::segment::segment_intersection_kind_2d_exec;
#[cfg(verus_keep_ghost)]
use super::polygon::point_in_convex_polygon_boundary_inclusive_exec;
#[cfg(verus_keep_ghost)]
use crate::segment_intersection::SegmentIntersection2dKind;
#[cfg(verus_keep_ghost)]
use crate::segment_polygon::*;
#[cfg(verus_keep_ghost)]
use crate::convex_polygon::*;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// SegmentIntersection2dKind helper (avoid derived PartialEq)
// ---------------------------------------------------------------------------

fn is_disjoint(k: &SegmentIntersection2dKind) -> (out: bool)
    ensures out == (*k == SegmentIntersection2dKind::Disjoint),
{
    match k {
        SegmentIntersection2dKind::Disjoint => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Segment overlaps convex polygon
// ---------------------------------------------------------------------------

/// Does the segment overlap the convex polygon?
pub fn segment_overlaps_convex_polygon_exec(
    seg_start: &RuntimePoint2, seg_end: &RuntimePoint2,
    polygon: &RuntimePolygon2,
) -> (out: bool)
    requires
        seg_start.wf_spec(),
        seg_end.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == segment_overlaps_convex_polygon::<RationalModel>(
            seg_start@, seg_end@, polygon.model(),
        ),
{
    // Check endpoint containment
    let start_in = point_in_convex_polygon_boundary_inclusive_exec(seg_start, polygon);
    if start_in {
        return true;
    }
    let end_in = point_in_convex_polygon_boundary_inclusive_exec(seg_end, polygon);
    if end_in {
        return true;
    }

    // Check edge hits
    let n = polygon.len();
    let mut has_hit = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            seg_start.wf_spec(),
            seg_end.wf_spec(),
            polygon.wf_spec(),
            has_hit == segment_prefix_hits_polygon_edge::<RationalModel>(
                seg_start@, seg_end@, polygon.model(), i as int,
            ),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let kind = segment_intersection_kind_2d_exec(seg_start, seg_end, vi, vj);

        proof {
            assert(polygon.model()[i as int] == polygon.vertices@[i as int]@);
            assert(polygon.model()[j as int] == polygon.vertices@[j as int]@);
        }

        let not_disjoint = !is_disjoint(&kind);
        if not_disjoint {
            has_hit = true;
        }

        proof {
            // Update prefix predicate
            if has_hit {
                if not_disjoint {
                    assert(segment_hits_polygon_edge::<RationalModel>(
                        seg_start@, seg_end@, polygon.model(), i as int,
                    ));
                }
                assert(segment_prefix_hits_polygon_edge::<RationalModel>(
                    seg_start@, seg_end@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_hit {
                // Neither the old prefix nor the current edge hit
                assert(!segment_prefix_hits_polygon_edge::<RationalModel>(
                    seg_start@, seg_end@, polygon.model(), (i + 1) as int,
                ));
            }
        }

        i = i + 1;
    }

    has_hit
}

} // verus!
