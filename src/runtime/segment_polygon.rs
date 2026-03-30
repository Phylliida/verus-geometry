#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

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
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
verus! {

pub fn is_disjoint(k: &SegmentIntersection2dKind) -> (out: bool)
    ensures out == (*k == SegmentIntersection2dKind::Disjoint),
{
    match k {
        SegmentIntersection2dKind::Disjoint => true,
        _ => false,
    }
}

pub fn segment_overlaps_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    seg_start: &RuntimePoint2<R, V>, seg_end: &RuntimePoint2<R, V>,
    polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        seg_start.wf_spec(),
        seg_end.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == segment_overlaps_convex_polygon::<V>(
            seg_start.model@, seg_end.model@, polygon.model(),
        ),
{
    let start_in = point_in_convex_polygon_boundary_inclusive_exec(seg_start, polygon);
    if start_in { return true; }
    let end_in = point_in_convex_polygon_boundary_inclusive_exec(seg_end, polygon);
    if end_in { return true; }

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
            has_hit == segment_prefix_hits_polygon_edge::<V>(
                seg_start.model@, seg_end.model@, polygon.model(), i as int,
            ),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let kind = segment_intersection_kind_2d_exec(seg_start, seg_end, vi, vj);

        let not_disjoint = !is_disjoint(&kind);
        if not_disjoint { has_hit = true; }

        proof {
            if has_hit {
                if not_disjoint {
                    assert(segment_hits_polygon_edge::<V>(
                        seg_start.model@, seg_end.model@, polygon.model(), i as int,
                    ));
                }
                assert(segment_prefix_hits_polygon_edge::<V>(
                    seg_start.model@, seg_end.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_hit {
                assert(!segment_prefix_hits_polygon_edge::<V>(
                    seg_start.model@, seg_end.model@, polygon.model(), (i + 1) as int,
                ));
            }
        }

        i = i + 1;
    }

    has_hit
}

} //  verus!
