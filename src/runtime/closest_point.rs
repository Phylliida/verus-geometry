use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec2::ops::{dot as dot2, norm_sq as norm_sq2, scale as scale2};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{dot as dot3, norm_sq as norm_sq3, scale as scale3};
#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::{RuntimePoint2, RuntimeVec2, sub2_exec, add_vec2_exec};
#[cfg(verus_keep_ghost)]
use super::point3::{RuntimePoint3, RuntimeVec3, sub3_exec, add_vec3_exec};
#[cfg(verus_keep_ghost)]
use crate::point2::{sub2, add_vec2};
#[cfg(verus_keep_ghost)]
use crate::point3::{sub3, add_vec3};
#[cfg(verus_keep_ghost)]
use crate::closest_point::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  Clamp helper
//  ---------------------------------------------------------------------------

///  Clamp a RuntimeRational to [0, 1], matching the spec clamp01.
fn clamp01_exec(t: &RuntimeRational) -> (out: RuntimeRational)
    requires
        t.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == clamp01::<RationalModel>(t@),
{
    let zero = RuntimeRational::from_int(0);
    let one = RuntimeRational::from_int(1);
    if t.le(&zero) {
        zero
    } else if one.le(t) {
        one
    } else {
        //  Need to copy t since we can't move out of a reference
        RuntimeRational::from_frac(1, 1).mul(t)
    }
}

//  ---------------------------------------------------------------------------
//  2D: Point-segment closest point exec
//  ---------------------------------------------------------------------------

///  Compute the clamped projection parameter at runtime.
pub fn closest_parameter_2d_exec(
    q: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq2::<RationalModel>(sub2::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_2d::<RationalModel>(q@, a@, b@),
{
    let d = sub2_exec(b, a);
    let w = sub2_exec(q, a);
    let dot_wd = w.dot_exec(&d);
    let nsd = d.norm_sq_exec();
    let t_raw = dot_wd.div(&nsd);
    clamp01_exec(&t_raw)
}

///  Compute the closest point on segment [a, b] to query point q.
pub fn closest_point_on_segment_2d_exec(
    q: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: RuntimePoint2)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq2::<RationalModel>(sub2::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_point_on_segment_2d::<RationalModel>(q@, a@, b@),
{
    let d = sub2_exec(b, a);
    let t = closest_parameter_2d_exec(q, a, b);
    let tv = RuntimeVec2::scale_exec(&t, &d);
    add_vec2_exec(a, &tv)
}

///  Compute the squared distance from point q to segment [a, b].
pub fn squared_distance_point_segment_2d_exec(
    q: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq2::<RationalModel>(sub2::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_segment_2d::<RationalModel>(q@, a@, b@),
{
    let cp = closest_point_on_segment_2d_exec(q, a, b);
    let diff = sub2_exec(&cp, q);
    diff.norm_sq_exec()
}

//  ---------------------------------------------------------------------------
//  3D: Point-segment closest point exec
//  ---------------------------------------------------------------------------

///  Compute the clamped projection parameter at runtime (3D).
pub fn closest_parameter_3d_exec(
    q: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq3::<RationalModel>(sub3::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_3d::<RationalModel>(q@, a@, b@),
{
    let d = sub3_exec(b, a);
    let w = sub3_exec(q, a);
    let dot_wd = w.dot_exec(&d);
    let nsd = d.norm_sq_exec();
    let t_raw = dot_wd.div(&nsd);
    clamp01_exec(&t_raw)
}

///  Compute the closest point on segment [a, b] to query point q (3D).
pub fn closest_point_on_segment_3d_exec(
    q: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3,
) -> (out: RuntimePoint3)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq3::<RationalModel>(sub3::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_point_on_segment_3d::<RationalModel>(q@, a@, b@),
{
    let d = sub3_exec(b, a);
    let t = closest_parameter_3d_exec(q, a, b);
    let tv = RuntimeVec3::scale_exec(&t, &d);
    add_vec3_exec(a, &tv)
}

///  Compute the squared distance from point q to segment [a, b] (3D).
pub fn squared_distance_point_segment_3d_exec(
    q: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        q.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        !norm_sq3::<RationalModel>(sub3::<RationalModel>(b@, a@))
            .eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_segment_3d::<RationalModel>(q@, a@, b@),
{
    let cp = closest_point_on_segment_3d_exec(q, a, b);
    let diff = sub3_exec(&cp, q);
    diff.norm_sq_exec()
}

} //  verus!
