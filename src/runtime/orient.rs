use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::{RuntimePoint2, RuntimeVec2, sub2_exec};
#[cfg(verus_keep_ghost)]
use super::point3::{RuntimePoint3, RuntimeVec3, sub3_exec, cross_exec, dot3_exec};
#[cfg(verus_keep_ghost)]
use crate::orient2d::{det2d, orient2d};
#[cfg(verus_keep_ghost)]
use crate::orient3d::orient3d;

#[cfg(verus_keep_ghost)]
verus! {

///  det2d(u, v) = u.x * v.y - u.y * v.x
pub fn det2d_exec(u: &RuntimeVec2, v: &RuntimeVec2) -> (out: RuntimeRational)
    requires
        u.wf_spec(),
        v.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == det2d::<RationalModel>(u@, v@),
{
    let a = u.x.mul(&v.y);
    let b = u.y.mul(&v.x);
    a.sub(&b)
}

///  orient2d(a, b, c) = det2d(b - a, c - a)
pub fn orient2d_exec(
    a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == orient2d::<RationalModel>(a@, b@, c@),
{
    let ba = sub2_exec(b, a);
    let ca = sub2_exec(c, a);
    det2d_exec(&ba, &ca)
}

///  orient3d(a, b, c, d) = dot(b-a, cross(c-a, d-a))
pub fn orient3d_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == orient3d::<RationalModel>(a@, b@, c@, d@),
{
    let ba = sub3_exec(b, a);
    let ca = sub3_exec(c, a);
    let da = sub3_exec(d, a);
    let cr = cross_exec(&ca, &da);
    dot3_exec(&ba, &cr)
}

} //  verus!
