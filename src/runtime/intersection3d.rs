use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::{RuntimePoint3, RuntimeVec3, sub3_exec, add_vec3_exec};
#[cfg(verus_keep_ghost)]
use super::orient::{orient2d_exec, orient3d_exec};
#[cfg(verus_keep_ghost)]
use super::classification::{
    orient2d_sign_exec,
    point_above_plane_exec, point_below_plane_exec,
};
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use crate::point3::{Point3, sub3, add_vec3};
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::orient3d::orient3d;
#[cfg(verus_keep_ghost)]
use crate::orientation_sign::*;
#[cfg(verus_keep_ghost)]
use crate::intersection3d::*;
#[cfg(verus_keep_ghost)]
use crate::sidedness::*;
#[cfg(verus_keep_ghost)]
use crate::barycentric::*;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::scale;
#[cfg(verus_keep_ghost)]
use verus_linalg::runtime::copy_rational;
#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// OrientationSign helpers (avoid derived PartialEq in exec)
// ---------------------------------------------------------------------------

pub fn is_positive(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Positive),
{
    match s { OrientationSign::Positive => true, _ => false }
}

pub fn is_negative(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Negative),
{
    match s { OrientationSign::Negative => true, _ => false }
}

// ---------------------------------------------------------------------------
// Segment-plane intersection
// ---------------------------------------------------------------------------

/// Intersection parameter t = orient3d(a,b,c,d) / (orient3d(a,b,c,d) - orient3d(a,b,c,e))
pub fn segment_plane_intersection_parameter_exec(
    d: &RuntimePoint3, e: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        d.wf_spec(),
        e.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        segment_crosses_plane_strict::<RationalModel>(d@, e@, a@, b@, c@),
    ensures
        out.wf_spec(),
        out@ == segment_plane_intersection_parameter::<RationalModel>(d@, e@, a@, b@, c@),
{
    let od = orient3d_exec(a, b, c, d);
    let oe = orient3d_exec(a, b, c, e);
    let neg_oe = oe.neg();
    let denom = od.add(&neg_oe);
    proof {
        lemma_crossing_denominator_nonzero::<RationalModel>(d@, e@, a@, b@, c@);
    }
    od.div(&denom)
}

/// Intersection point: d + t * (e - d)
pub fn segment_plane_intersection_point_exec(
    d: &RuntimePoint3, e: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: RuntimePoint3)
    requires
        d.wf_spec(),
        e.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        segment_crosses_plane_strict::<RationalModel>(d@, e@, a@, b@, c@),
    ensures
        out.wf_spec(),
        out@ == segment_plane_intersection_point::<RationalModel>(d@, e@, a@, b@, c@),
{
    let t = segment_plane_intersection_parameter_exec(d, e, a, b, c);
    let dir = sub3_exec(e, d);
    let tv = RuntimeVec3::scale_exec(&t, &dir);
    add_vec3_exec(d, &tv)
}

// ---------------------------------------------------------------------------
// 2D projection helpers
// ---------------------------------------------------------------------------

/// Drop z: (x, y, z) -> (x, y)
pub fn project_drop_z_exec(p: &RuntimePoint3) -> (out: RuntimePoint2)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == project_drop_z::<RationalModel>(p@),
{
    RuntimePoint2::new(copy_rational(&p.x), copy_rational(&p.y))
}

/// Drop y: (x, y, z) -> (x, z)
pub fn project_drop_y_exec(p: &RuntimePoint3) -> (out: RuntimePoint2)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == project_drop_y::<RationalModel>(p@),
{
    RuntimePoint2::new(copy_rational(&p.x), copy_rational(&p.z))
}

/// Drop x: (x, y, z) -> (y, z)
pub fn project_drop_x_exec(p: &RuntimePoint3) -> (out: RuntimePoint2)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == project_drop_x::<RationalModel>(p@),
{
    RuntimePoint2::new(copy_rational(&p.y), copy_rational(&p.z))
}

/// Project by chosen axis.
pub fn project_by_axis_exec(p: &RuntimePoint3, axis: u8) -> (out: RuntimePoint2)
    requires
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == project_by_axis::<RationalModel>(p@, axis as int),
{
    if axis == 0u8 {
        project_drop_x_exec(p)
    } else if axis == 1u8 {
        project_drop_y_exec(p)
    } else {
        project_drop_z_exec(p)
    }
}

// ---------------------------------------------------------------------------
// Triangle projection axis
// ---------------------------------------------------------------------------

/// Compute projection axis (0=drop x, 1=drop y, 2=drop z).
pub fn triangle_projection_axis_exec(
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: u8)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out as int == triangle_projection_axis::<RationalModel>(a@, b@, c@),
{
    // Compute cross product of (b-a) x (c-a) = triangle normal
    let ba = sub3_exec(b, a);
    let ca = sub3_exec(c, a);
    let n = super::point3::cross_exec(&ba, &ca);
    if !n.x.is_zero() {
        0u8
    } else if !n.y.is_zero() {
        1u8
    } else {
        2u8
    }
}

// ---------------------------------------------------------------------------
// Point in triangle on plane
// ---------------------------------------------------------------------------

/// Point p (coplanar) is inside triangle (a, b, c), boundary inclusive.
pub fn point_in_triangle_on_plane_exec(
    p: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == point_in_triangle_on_plane::<RationalModel>(p@, a@, b@, c@),
{
    let axis = triangle_projection_axis_exec(a, b, c);
    let p2 = project_by_axis_exec(p, axis);
    let a2 = project_by_axis_exec(a, axis);
    let b2 = project_by_axis_exec(b, axis);
    let c2 = project_by_axis_exec(c, axis);

    let o1 = orient2d_sign_exec(&a2, &b2, &p2);
    let o2 = orient2d_sign_exec(&b2, &c2, &p2);
    let o3 = orient2d_sign_exec(&c2, &a2, &p2);

    let o1p = is_positive(&o1);
    let o1n = is_negative(&o1);
    let o2p = is_positive(&o2);
    let o2n = is_negative(&o2);
    let o3p = is_positive(&o3);
    let o3n = is_negative(&o3);

    !(
        (o1p && (o2n || o3n))
        || (o1n && (o2p || o3p))
        || (o2p && o3n)
        || (o2n && o3p)
    )
}

// ---------------------------------------------------------------------------
// Segment-triangle intersection
// ---------------------------------------------------------------------------

/// Segment (d, e) strictly intersects triangle (a, b, c).
pub fn segment_triangle_intersects_strict_exec(
    seg_start: &RuntimePoint3, seg_end: &RuntimePoint3,
    tri_a: &RuntimePoint3, tri_b: &RuntimePoint3, tri_c: &RuntimePoint3,
) -> (out: bool)
    requires
        seg_start.wf_spec(),
        seg_end.wf_spec(),
        tri_a.wf_spec(),
        tri_b.wf_spec(),
        tri_c.wf_spec(),
    ensures
        out == segment_triangle_intersects_strict::<RationalModel>(
            seg_start@, seg_end@, tri_a@, tri_b@, tri_c@,
        ),
{
    let crosses = {
        let above_d = point_above_plane_exec(seg_start, tri_a, tri_b, tri_c);
        let below_d = point_below_plane_exec(seg_start, tri_a, tri_b, tri_c);
        let above_e = point_above_plane_exec(seg_end, tri_a, tri_b, tri_c);
        let below_e = point_below_plane_exec(seg_end, tri_a, tri_b, tri_c);
        (above_d && below_e) || (below_d && above_e)
    };
    if !crosses {
        return false;
    }
    let p = segment_plane_intersection_point_exec(
        seg_start, seg_end, tri_a, tri_b, tri_c,
    );
    point_in_triangle_on_plane_exec(&p, tri_a, tri_b, tri_c)
}

// ---------------------------------------------------------------------------
// Barycentric coordinates exec
// ---------------------------------------------------------------------------

/// Unnormalized barycentric coordinates: (orient2d(b,c,p), orient2d(c,a,p), orient2d(a,b,p))
pub fn barycentric_unnorm_2d_exec(
    p: &RuntimePoint2,
    a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: (RuntimeRational, RuntimeRational, RuntimeRational))
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out.0.wf_spec(),
        out.1.wf_spec(),
        out.2.wf_spec(),
        out.0@ == barycentric_unnorm_2d::<RationalModel>(p@, a@, b@, c@).0,
        out.1@ == barycentric_unnorm_2d::<RationalModel>(p@, a@, b@, c@).1,
        out.2@ == barycentric_unnorm_2d::<RationalModel>(p@, a@, b@, c@).2,
{
    let u = orient2d_exec(b, c, p);
    let v = orient2d_exec(c, a, p);
    let w = orient2d_exec(a, b, p);
    (u, v, w)
}

/// Normalized barycentric coordinates: each component / orient2d(a, b, c).
pub fn barycentric_coords_2d_exec(
    p: &RuntimePoint2,
    a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: (RuntimeRational, RuntimeRational, RuntimeRational))
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        !orient2d::<RationalModel>(a@, b@, c@).eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.0.wf_spec(),
        out.1.wf_spec(),
        out.2.wf_spec(),
        out.0@ == barycentric_coords_2d::<RationalModel>(p@, a@, b@, c@).0,
        out.1@ == barycentric_coords_2d::<RationalModel>(p@, a@, b@, c@).1,
        out.2@ == barycentric_coords_2d::<RationalModel>(p@, a@, b@, c@).2,
{
    let area = orient2d_exec(a, b, c);
    let (u, v, w) = barycentric_unnorm_2d_exec(p, a, b, c);
    let nu = u.div(&area);
    let nv = v.div(&area);
    let nw = w.div(&area);
    (nu, nv, nw)
}

} // verus!
