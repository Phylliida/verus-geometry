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

///  det2d(u, v) = ux * vy - uy * vx
pub fn det2d_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    ux: &R, uy: &R, vx: &R, vy: &R,
) -> (out: R)
    requires ux.wf_spec(), uy.wf_spec(), vx.wf_spec(), vy.wf_spec(),
    ensures
        out.wf_spec(),
        out.model() == det2d::<V>(
            verus_linalg::vec2::Vec2 { x: ux.model(), y: uy.model() },
            verus_linalg::vec2::Vec2 { x: vx.model(), y: vy.model() }),
{
    let a = ux.mul(vy);
    let b = uy.mul(vx);
    a.sub(&b)
}

///  orient2d(a, b, c) = det2d(b - a, c - a)
pub fn orient2d_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures
        out.wf_spec(),
        out.model() == orient2d::<V>(a.model@, b.model@, c.model@),
{
    let (bax, bay) = super::point2::sub2_exec(b, a);
    let (cax, cay) = super::point2::sub2_exec(c, a);
    det2d_exec(&bax, &bay, &cax, &cay)
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
        out.model() == orient3d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let (bax, bay, baz) = super::point3::sub3_exec(b, a);
    let (cax, cay, caz) = super::point3::sub3_exec(c, a);
    let (dax, day, daz) = super::point3::sub3_exec(d, a);
    let (crx, cry, crz) = super::point3::cross_exec(&cax, &cay, &caz, &dax, &day, &daz);
    super::point3::dot3_exec(&bax, &bay, &baz, &crx, &cry, &crz)
}

} //  verus!
