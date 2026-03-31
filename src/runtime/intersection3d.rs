#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
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
use crate::point3::Point3;
#[cfg(verus_keep_ghost)]
use crate::orientation_sign::*;
#[cfg(verus_keep_ghost)]
use crate::intersection3d::*;
#[cfg(verus_keep_ghost)]
use crate::sidedness::*;
#[cfg(verus_keep_ghost)]
use crate::barycentric::*;
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;

#[cfg(verus_keep_ghost)]
verus! {

pub fn is_positive_i3d(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Positive),
{
    match s { OrientationSign::Positive => true, _ => false }
}

pub fn is_negative_i3d(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Negative),
{
    match s { OrientationSign::Negative => true, _ => false }
}

pub fn segment_plane_intersection_parameter_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    d: &RuntimePoint3<R, V>, e: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        d.wf_spec(), e.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        segment_crosses_plane_strict::<V>(d.model@, e.model@, a.model@, b.model@, c.model@),
    ensures
        out.wf_spec(),
        out@ == segment_plane_intersection_parameter::<V>(d.model@, e.model@, a.model@, b.model@, c.model@),
{
    let od = orient3d_exec(a, b, c, d);
    let oe = orient3d_exec(a, b, c, e);
    let neg_oe = oe.neg();
    let denom = od.add(&neg_oe);
    proof {
        lemma_crossing_denominator_nonzero::<V>(d.model@, e.model@, a.model@, b.model@, c.model@);
    }
    od.div(&denom)
}

pub fn segment_plane_intersection_point_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    d: &RuntimePoint3<R, V>, e: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: RuntimePoint3<R, V>)
    requires
        d.wf_spec(), e.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        segment_crosses_plane_strict::<V>(d.model@, e.model@, a.model@, b.model@, c.model@),
    ensures
        out.wf_spec(),
        out.model@ == segment_plane_intersection_point::<V>(d.model@, e.model@, a.model@, b.model@, c.model@),
{
    let t = segment_plane_intersection_parameter_exec(d, e, a, b, c);
    let dir = e.sub(d);
    d.add(&dir.scaled(&t))
}

pub fn project_drop_z_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires p.wf_spec(),
    ensures out.wf_spec(), out.model@ == project_drop_z::<V>(p.model@),
{
    RuntimePoint2::new(p.x.copy(), p.y.copy())
}

pub fn project_drop_y_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires p.wf_spec(),
    ensures out.wf_spec(), out.model@ == project_drop_y::<V>(p.model@),
{
    RuntimePoint2::new(p.x.copy(), p.z.copy())
}

pub fn project_drop_x_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires p.wf_spec(),
    ensures out.wf_spec(), out.model@ == project_drop_x::<V>(p.model@),
{
    RuntimePoint2::new(p.y.copy(), p.z.copy())
}

pub fn project_by_axis_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>, axis: u8,
) -> (out: RuntimePoint2<R, V>)
    requires p.wf_spec(),
    ensures out.wf_spec(), out.model@ == project_by_axis::<V>(p.model@, axis as int),
{
    if axis == 0u8 {
        project_drop_x_exec(p)
    } else if axis == 1u8 {
        project_drop_y_exec(p)
    } else {
        project_drop_z_exec(p)
    }
}

pub fn triangle_projection_axis_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: u8)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out as int == triangle_projection_axis::<V>(a.model@, b.model@, c.model@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let n = ba.cross(&ca);
    let zero = n.x.zero_like();
    if !n.x.eq(&zero) {
        0u8
    } else if !n.y.eq(&zero) {
        1u8
    } else {
        2u8
    }
}

pub fn point_in_triangle_on_plane_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == point_in_triangle_on_plane::<V>(p.model@, a.model@, b.model@, c.model@),
{
    let axis = triangle_projection_axis_exec(a, b, c);
    let p2 = project_by_axis_exec(p, axis);
    let a2 = project_by_axis_exec(a, axis);
    let b2 = project_by_axis_exec(b, axis);
    let c2 = project_by_axis_exec(c, axis);

    let o1 = orient2d_sign_exec(&a2, &b2, &p2);
    let o2 = orient2d_sign_exec(&b2, &c2, &p2);
    let o3 = orient2d_sign_exec(&c2, &a2, &p2);

    let o1p = is_positive_i3d(&o1);
    let o1n = is_negative_i3d(&o1);
    let o2p = is_positive_i3d(&o2);
    let o2n = is_negative_i3d(&o2);
    let o3p = is_positive_i3d(&o3);
    let o3n = is_negative_i3d(&o3);

    !(
        (o1p && (o2n || o3n))
        || (o1n && (o2p || o3p))
        || (o2p && o3n)
        || (o2n && o3p)
    )
}

pub fn segment_triangle_intersects_strict_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    seg_start: &RuntimePoint3<R, V>, seg_end: &RuntimePoint3<R, V>,
    tri_a: &RuntimePoint3<R, V>, tri_b: &RuntimePoint3<R, V>, tri_c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires
        seg_start.wf_spec(), seg_end.wf_spec(),
        tri_a.wf_spec(), tri_b.wf_spec(), tri_c.wf_spec(),
    ensures
        out == segment_triangle_intersects_strict::<V>(
            seg_start.model@, seg_end.model@, tri_a.model@, tri_b.model@, tri_c.model@,
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

pub fn barycentric_unnorm_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>, c: &RuntimePoint2<R, V>,
) -> (out: (R, R, R))
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures
        out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
        out.0@ == barycentric_unnorm_2d::<V>(p.model@, a.model@, b.model@, c.model@).0,
        out.1@ == barycentric_unnorm_2d::<V>(p.model@, a.model@, b.model@, c.model@).1,
        out.2@ == barycentric_unnorm_2d::<V>(p.model@, a.model@, b.model@, c.model@).2,
{
    let u = orient2d_exec(b, c, p);
    let v = orient2d_exec(c, a, p);
    let w = orient2d_exec(a, b, p);
    (u, v, w)
}

pub fn barycentric_coords_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>, c: &RuntimePoint2<R, V>,
) -> (out: (R, R, R))
    requires
        p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        !orient2d::<V>(a.model@, b.model@, c.model@).eqv(V::zero()),
    ensures
        out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
        out.0@ == barycentric_coords_2d::<V>(p.model@, a.model@, b.model@, c.model@).0,
        out.1@ == barycentric_coords_2d::<V>(p.model@, a.model@, b.model@, c.model@).1,
        out.2@ == barycentric_coords_2d::<V>(p.model@, a.model@, b.model@, c.model@).2,
{
    let (u, v, w) = barycentric_unnorm_2d_exec(p, a, b, c);
    let area = orient2d_exec(a, b, c);
    (u.div(&area), v.div(&area), w.div(&area))
}

} //  verus!
