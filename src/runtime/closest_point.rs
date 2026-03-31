#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec2::ops::{norm_sq as norm_sq2};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{norm_sq as norm_sq3};
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::point2::sub2;
#[cfg(verus_keep_ghost)]
use crate::point3::sub3;
#[cfg(verus_keep_ghost)]
use crate::closest_point::*;

#[cfg(verus_keep_ghost)]
verus! {

fn clamp01_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    t: &R,
) -> (out: R)
    requires t.wf_spec(),
    ensures out.wf_spec(), out@ == clamp01::<V>(t@),
{
    let zero = t.zero_like();
    let one = t.one_like();
    if t.le(&zero) { zero }
    else if one.le(t) { one }
    else { t.copy() }
}

//  2D

pub fn closest_parameter_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq2::<V>(sub2::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_2d::<V>(q.model@, a.model@, b.model@),
{
    let d = b.sub(a);
    let w = q.sub(a);
    let dot_wd = w.dot(&d);
    let nsd = d.norm_sq();
    clamp01_exec(&dot_wd.div(&nsd))
}

pub fn closest_point_on_segment_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq2::<V>(sub2::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model@ == closest_point_on_segment_2d::<V>(q.model@, a.model@, b.model@),
{
    let d = b.sub(a);
    let t = closest_parameter_2d_exec(q, a, b);
    a.add(&d.scaled(&t))
}

pub fn squared_distance_point_segment_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq2::<V>(sub2::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_segment_2d::<V>(q.model@, a.model@, b.model@),
{
    let cp = closest_point_on_segment_2d_exec(q, a, b);
    cp.sub(q).norm_sq()
}

//  3D

pub fn closest_parameter_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint3<R, V>, a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq3::<V>(sub3::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_3d::<V>(q.model@, a.model@, b.model@),
{
    let d = b.sub(a);
    let w = q.sub(a);
    let dot_wd = w.dot(&d);
    let nsd = d.norm_sq();
    clamp01_exec(&dot_wd.div(&nsd))
}

pub fn closest_point_on_segment_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint3<R, V>, a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
) -> (out: RuntimePoint3<R, V>)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq3::<V>(sub3::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model@ == closest_point_on_segment_3d::<V>(q.model@, a.model@, b.model@),
{
    let d = b.sub(a);
    let t = closest_parameter_3d_exec(q, a, b);
    a.add(&d.scaled(&t))
}

pub fn squared_distance_point_segment_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint3<R, V>, a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq3::<V>(sub3::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_segment_3d::<V>(q.model@, a.model@, b.model@),
{
    let cp = closest_point_on_segment_3d_exec(q, a, b);
    cp.sub(q).norm_sq()
}

} //  verus!
