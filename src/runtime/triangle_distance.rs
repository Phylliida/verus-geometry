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
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::triangle_distance::*;
#[cfg(verus_keep_ghost)]
use crate::closest_point::*;
#[cfg(verus_keep_ghost)]
use crate::point2::sub2;
#[cfg(verus_keep_ghost)]
use crate::point3::sub3;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  2D: Point in triangle (exec)
//  ---------------------------------------------------------------------------

///  Test if point q is inside triangle (a, b, c), boundary inclusive.
pub fn point_in_triangle_2d_exec(
    q: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: bool)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures
        out == point_in_triangle_2d::<RationalModel>(q@, a@, b@, c@),
{
    let o1 = super::orient::orient2d_exec(a, b, q);
    let o2 = super::orient::orient2d_exec(b, c, q);
    let o3 = super::orient::orient2d_exec(c, a, q);
    let zero = RuntimeRational::from_int(0);

    let o1_ge = zero.le(&o1);
    let o2_ge = zero.le(&o2);
    let o3_ge = zero.le(&o3);

    let o1_le = o1.le(&zero);
    let o2_le = o2.le(&zero);
    let o3_le = o3.le(&zero);

    (o1_ge && o2_ge && o3_ge) || (o1_le && o2_le && o3_le)
}

//  ---------------------------------------------------------------------------
//  Min helper (exec)
//  ---------------------------------------------------------------------------

///  Minimum of two RuntimeRationals.
fn min_of_exec(a: RuntimeRational, b: RuntimeRational) -> (out: RuntimeRational)
    requires a.wf_spec(), b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == min_of::<RationalModel>(a@, b@),
{
    if a.le(&b) { a } else { b }
}

///  Minimum of three RuntimeRationals.
fn min_of_three_exec(a: RuntimeRational, b: RuntimeRational, c: RuntimeRational) -> (out: RuntimeRational)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == min_of_three::<RationalModel>(a@, b@, c@),
{
    min_of_exec(a, min_of_exec(b, c))
}

//  ---------------------------------------------------------------------------
//  2D: Point-triangle squared distance (exec)
//  ---------------------------------------------------------------------------

///  Squared distance from point q to triangle (a, b, c) in 2D.
pub fn squared_distance_point_triangle_2d_exec(
    q: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        !verus_linalg::vec2::ops::norm_sq(sub2::<RationalModel>(b@, a@)).eqv(RationalModel::from_int_spec(0)),
        !verus_linalg::vec2::ops::norm_sq(sub2::<RationalModel>(c@, b@)).eqv(RationalModel::from_int_spec(0)),
        !verus_linalg::vec2::ops::norm_sq(sub2::<RationalModel>(a@, c@)).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_triangle_2d::<RationalModel>(q@, a@, b@, c@),
{
    if point_in_triangle_2d_exec(q, a, b, c) {
        RuntimeRational::from_int(0)
    } else {
        let d_ab = super::closest_point::squared_distance_point_segment_2d_exec(q, a, b);
        let d_bc = super::closest_point::squared_distance_point_segment_2d_exec(q, b, c);
        let d_ca = super::closest_point::squared_distance_point_segment_2d_exec(q, c, a);
        min_of_three_exec(d_ab, d_bc, d_ca)
    }
}

//  ---------------------------------------------------------------------------
//  3D: Min edge squared distance (exec)
//  ---------------------------------------------------------------------------

///  Minimum squared distance from point q to the three edges of triangle
///  (a, b, c) in 3D.
pub fn min_edge_squared_distance_3d_exec(
    q: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        !verus_linalg::vec3::ops::norm_sq(sub3::<RationalModel>(b@, a@)).eqv(RationalModel::from_int_spec(0)),
        !verus_linalg::vec3::ops::norm_sq(sub3::<RationalModel>(c@, b@)).eqv(RationalModel::from_int_spec(0)),
        !verus_linalg::vec3::ops::norm_sq(sub3::<RationalModel>(a@, c@)).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == min_edge_squared_distance_3d::<RationalModel>(q@, a@, b@, c@),
{
    let d_ab = super::closest_point::squared_distance_point_segment_3d_exec(q, a, b);
    let d_bc = super::closest_point::squared_distance_point_segment_3d_exec(q, b, c);
    let d_ca = super::closest_point::squared_distance_point_segment_3d_exec(q, c, a);
    min_of_three_exec(d_ab, d_bc, d_ca)
}

} //  verus!
