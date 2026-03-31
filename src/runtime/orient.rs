#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::orient2d::{det2d, orient2d};
#[cfg(verus_keep_ghost)]
use crate::orient3d::orient3d;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;

#[cfg(verus_keep_ghost)]
verus! {

///  orient2d(a, b, c) = det2d(b - a, c - a)
pub fn orient2d_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == orient2d::<V>(a.model@, b.model@, c.model@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    //  det2d = ba.x * ca.y - ba.y * ca.x
    ba.x.mul(&ca.y).sub(&ba.y.mul(&ca.x))
}

///  orient3d(a, b, c, d) = dot(b-a, cross(c-a, d-a))
pub fn orient3d_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
    d: &RuntimePoint3<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == orient3d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let da = d.sub(a);
    ba.dot(&ca.cross(&da))
}

} //  verus!
