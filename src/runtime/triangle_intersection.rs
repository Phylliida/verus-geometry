#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use super::classification::{point_above_plane_exec, point_below_plane_exec};
#[cfg(verus_keep_ghost)]
use super::intersection3d::segment_triangle_intersects_strict_exec;
#[cfg(verus_keep_ghost)]
use crate::sidedness::*;
#[cfg(verus_keep_ghost)]
use crate::triangle_intersection::*;

#[cfg(verus_keep_ghost)]
verus! {

/// Test whether two triangles strictly intersect in 3D.
///
/// Uses half-space early exit: if all vertices of one triangle are on the
/// same strict side of the other triangle's plane, the triangles cannot
/// intersect and we return false without computing any intersection points.
///
/// Otherwise, tests all 6 edge-through-triangle combinations with
/// short-circuit evaluation.
pub fn triangles_intersect_strict_exec(
    a1: &RuntimePoint3, b1: &RuntimePoint3, c1: &RuntimePoint3,
    a2: &RuntimePoint3, b2: &RuntimePoint3, c2: &RuntimePoint3,
) -> (out: bool)
    requires
        a1.wf_spec(),
        b1.wf_spec(),
        c1.wf_spec(),
        a2.wf_spec(),
        b2.wf_spec(),
        c2.wf_spec(),
    ensures
        out == triangles_intersect_strict::<RationalModel>(
            a1@, b1@, c1@, a2@, b2@, c2@,
        ),
{
    // --- Early exit: classify T1 vertices against plane(T2) ---
    let a1_above_t2 = point_above_plane_exec(a1, a2, b2, c2);
    let a1_below_t2 = point_below_plane_exec(a1, a2, b2, c2);
    let b1_above_t2 = point_above_plane_exec(b1, a2, b2, c2);
    let b1_below_t2 = point_below_plane_exec(b1, a2, b2, c2);
    let c1_above_t2 = point_above_plane_exec(c1, a2, b2, c2);
    let c1_below_t2 = point_below_plane_exec(c1, a2, b2, c2);

    let t1_all_above = a1_above_t2 && b1_above_t2 && c1_above_t2;
    let t1_all_below = a1_below_t2 && b1_below_t2 && c1_below_t2;

    if t1_all_above || t1_all_below {
        proof {
            lemma_t1_separated_no_t1_edges::<RationalModel>(
                a1@, b1@, c1@, a2@, b2@, c2@,
            );
            // T1 edges can't cross plane(T2), so segment_triangle_intersects_strict
            // is false for all 3 T1 edges.
            // For T2 edges through T1: each requires segment_crosses_plane_strict
            // which needs endpoints on opposite sides of plane(T1). Even though
            // we haven't checked T2 vs plane(T1), we can't short-circuit those
            // from T1-separation alone. But wait — we CAN use the geometric
            // argument: if an edge of T2 (whose endpoints are on plane(T2))
            // crosses plane(T1) and hits inside T1, the intersection point is
            // both on plane(T2) and inside T1. All T1 vertices are strictly
            // above/below plane(T2), and the intersection point is a convex
            // combination of T1's vertices projected onto plane(T1)... this
            // requires the affine linearity of orient3d.
            //
            // For now we check T2 vs plane(T1) at runtime too, so the early
            // exit only fires when BOTH separations hold (the common case).
        }
        // Fall through to check T2 vs plane(T1)
    }

    // --- Early exit: classify T2 vertices against plane(T1) ---
    let a2_above_t1 = point_above_plane_exec(a2, a1, b1, c1);
    let a2_below_t1 = point_below_plane_exec(a2, a1, b1, c1);
    let b2_above_t1 = point_above_plane_exec(b2, a1, b1, c1);
    let b2_below_t1 = point_below_plane_exec(b2, a1, b1, c1);
    let c2_above_t1 = point_above_plane_exec(c2, a1, b1, c1);
    let c2_below_t1 = point_below_plane_exec(c2, a1, b1, c1);

    let t2_all_above = a2_above_t1 && b2_above_t1 && c2_above_t1;
    let t2_all_below = a2_below_t1 && b2_below_t1 && c2_below_t1;

    if (t1_all_above || t1_all_below) && (t2_all_above || t2_all_below) {
        proof {
            lemma_both_separated_no_intersection::<RationalModel>(
                a1@, b1@, c1@, a2@, b2@, c2@,
            );
        }
        return false;
    }

    // --- Full test: 6 edge-through-triangle checks ---
    // Edges of T1 through T2
    if segment_triangle_intersects_strict_exec(a1, b1, a2, b2, c2) {
        return true;
    }
    if segment_triangle_intersects_strict_exec(b1, c1, a2, b2, c2) {
        return true;
    }
    if segment_triangle_intersects_strict_exec(c1, a1, a2, b2, c2) {
        return true;
    }
    // Edges of T2 through T1
    if segment_triangle_intersects_strict_exec(a2, b2, a1, b1, c1) {
        return true;
    }
    if segment_triangle_intersects_strict_exec(b2, c2, a1, b1, c1) {
        return true;
    }
    if segment_triangle_intersects_strict_exec(c2, a2, a1, b1, c1) {
        return true;
    }
    false
}

} // verus!
