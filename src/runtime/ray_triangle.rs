use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use super::point3::{sub3_exec, cross_exec, dot3_exec};
#[cfg(verus_keep_ghost)]
use verus_linalg::runtime::vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use crate::ray_triangle::*;

#[cfg(verus_keep_ghost)]
verus! {

/// Ray-triangle intersection test (Möller-Trumbore, division-free).
///
/// Tests whether ray (origin + t*dir, t ≥ 0) hits triangle (v0, v1, v2).
/// Uses sign comparisons to avoid division.
pub fn ray_hits_triangle_nodiv_exec(
    origin: &RuntimePoint3, dir: &RuntimeVec3,
    v0: &RuntimePoint3, v1: &RuntimePoint3, v2: &RuntimePoint3,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        v0.wf_spec(), v1.wf_spec(), v2.wf_spec(),
    ensures
        out == ray_hits_triangle_nodiv::<RationalModel>(
            origin@, dir@, v0@, v1@, v2@,
        ),
{
    // Edge vectors
    let e1 = sub3_exec(v1, v0);
    let e2 = sub3_exec(v2, v0);

    // P = dir × edge2
    let p = cross_exec(dir, &e2);

    // det = dot(edge1, P)
    let det = dot3_exec(&e1, &p);

    let zero = RuntimeRational::from_int(0);

    if det.eq(&zero) {
        return false;
    }

    // T = origin - v0
    let tvec = sub3_exec(origin, v0);

    // u_unnorm = dot(T, P)
    let u = dot3_exec(&tvec, &p);

    // Q = T × edge1
    let q = cross_exec(&tvec, &e1);

    // v_unnorm = dot(dir, Q)
    let v = dot3_exec(dir, &q);

    // t_unnorm = dot(edge2, Q)
    let t = dot3_exec(&e2, &q);

    // u + v
    let uv = u.add(&v);

    if zero.lt(&det) {
        // det > 0: u ≥ 0, v ≥ 0, u + v ≤ det, t ≥ 0
        zero.le(&u) && zero.le(&v) && uv.le(&det) && zero.le(&t)
    } else {
        // det < 0: u ≤ 0, v ≤ 0, u + v ≥ det, t ≤ 0
        u.le(&zero) && v.le(&zero) && det.le(&uv) && t.le(&zero)
    }
}

} // verus!
