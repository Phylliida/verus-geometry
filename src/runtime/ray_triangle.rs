#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::ray_triangle::*;

#[cfg(verus_keep_ghost)]
verus! {

///  Ray-triangle intersection test (Möller-Trumbore, division-free).
///
///  Tests whether ray (origin + t*dir, t >= 0) hits triangle (v0, v1, v2).
///  dir is represented as a RuntimePoint3 (same struct, used as a direction vector).
pub fn ray_hits_triangle_nodiv_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    v0: &RuntimePoint3<R, V>, v1: &RuntimePoint3<R, V>, v2: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        v0.wf_spec(), v1.wf_spec(), v2.wf_spec(),
    ensures
        out == ray_hits_triangle_nodiv::<V>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            v0.model@, v1.model@, v2.model@,
        ),
{
    let e1 = v1.sub(v0);
    let e2 = v2.sub(v0);

    //  P = dir × e2
    let p = dir.cross(&e2);

    //  det = e1 · P
    let det = e1.dot(&p);

    let zero = det.zero_like();

    if det.eq(&zero) {
        return false;
    }

    //  T = origin - v0
    let tvec = origin.sub(v0);

    //  u = T · P
    let u = tvec.dot(&p);

    //  Q = T × e1
    let q = tvec.cross(&e1);

    //  v = dir · Q
    let v = dir.dot(&q);

    //  t_param = e2 · Q
    let t_param = e2.dot(&q);

    //  u + v
    let uv = u.add(&v);

    if zero.lt(&det) {
        zero.le(&u) && zero.le(&v) && uv.le(&det) && zero.le(&t_param)
    } else {
        u.le(&zero) && v.le(&zero) && det.le(&uv) && t_param.le(&zero)
    }
}

} //  verus!
