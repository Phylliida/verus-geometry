#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec2::ops::{dot as dot2, norm_sq as norm_sq2};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{dot as dot3, norm_sq as norm_sq3};
#[cfg(verus_keep_ghost)]
use super::point2::{RuntimePoint2, sub2_exec, add_vec2_exec};
#[cfg(verus_keep_ghost)]
use super::point3::{RuntimePoint3, sub3_exec, add_vec3_exec};
#[cfg(verus_keep_ghost)]
use crate::point2::{sub2, add_vec2};
#[cfg(verus_keep_ghost)]
use crate::point3::{sub3, add_vec3};
#[cfg(verus_keep_ghost)]
use crate::closest_point::*;

#[cfg(verus_keep_ghost)]
verus! {

//  Scalar helpers: dot, norm_sq, clamp01 — all inline via trait methods

fn dot2_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    ax: &R, ay: &R, bx: &R, by: &R,
) -> (out: R)
    requires ax.wf_spec(), ay.wf_spec(), bx.wf_spec(), by.wf_spec(),
    ensures out.wf_spec(),
        out.model() == ax.model().mul(bx.model()).add(ay.model().mul(by.model())),
{
    ax.mul(bx).add(&ay.mul(by))
}

fn norm_sq2_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    x: &R, y: &R,
) -> (out: R)
    requires x.wf_spec(), y.wf_spec(),
    ensures out.wf_spec(),
        out.model() == x.model().mul(x.model()).add(y.model().mul(y.model())),
{
    x.mul(x).add(&y.mul(y))
}

fn dot3_scalar_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    ax: &R, ay: &R, az: &R, bx: &R, by: &R, bz: &R,
) -> (out: R)
    requires ax.wf_spec(), ay.wf_spec(), az.wf_spec(), bx.wf_spec(), by.wf_spec(), bz.wf_spec(),
    ensures out.wf_spec(),
        out.model() == ax.model().mul(bx.model())
            .add(ay.model().mul(by.model()))
            .add(az.model().mul(bz.model())),
{
    ax.mul(bx).add(&ay.mul(by)).add(&az.mul(bz))
}

fn norm_sq3_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    x: &R, y: &R, z: &R,
) -> (out: R)
    requires x.wf_spec(), y.wf_spec(), z.wf_spec(),
    ensures out.wf_spec(),
        out.model() == x.model().mul(x.model())
            .add(y.model().mul(y.model()))
            .add(z.model().mul(z.model())),
{
    x.mul(x).add(&y.mul(y)).add(&z.mul(z))
}

fn clamp01_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    t: &R,
) -> (out: R)
    requires t.wf_spec(),
    ensures out.wf_spec(), out.model() == clamp01::<V>(t.model()),
{
    let zero = t.zero_like();
    let one = t.one_like();
    if t.le(&zero) {
        zero
    } else if one.le(t) {
        one
    } else {
        t.copy()
    }
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
        out.model() == closest_parameter_2d::<V>(q.model@, a.model@, b.model@),
{
    let (dx, dy) = b.sub(a);
    let (wx, wy) = q.sub(a);
    let dot_wd = dot2_exec(&wx, &wy, &dx, &dy);
    let nsd = norm_sq2_exec(&dx, &dy);
    let t_raw = dot_wd.div(&nsd);
    clamp01_exec(&t_raw)
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
    let (dx, dy) = b.sub(a);
    let t = closest_parameter_2d_exec(q, a, b);
    let tx = t.mul(&dx);
    let ty = t.mul(&dy);
    add_vec2_exec(a, &tx, &ty)
}

pub fn squared_distance_point_segment_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq2::<V>(sub2::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model() == squared_distance_point_segment_2d::<V>(q.model@, a.model@, b.model@),
{
    let cp = closest_point_on_segment_2d_exec(q, a, b);
    let (dx, dy) = &cp.sub(q);
    norm_sq2_exec(&dx, &dy)
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
        out.model() == closest_parameter_3d::<V>(q.model@, a.model@, b.model@),
{
    let (dx, dy, dz) = b.sub(a);
    let (wx, wy, wz) = q.sub(a);
    let dot_wd = dot3_scalar_exec(&wx, &wy, &wz, &dx, &dy, &dz);
    let nsd = norm_sq3_exec(&dx, &dy, &dz);
    let t_raw = dot_wd.div(&nsd);
    clamp01_exec(&t_raw)
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
    let (dx, dy, dz) = b.sub(a);
    let t = closest_parameter_3d_exec(q, a, b);
    let tx = t.mul(&dx);
    let ty = t.mul(&dy);
    let tz = t.mul(&dz);
    a.add(&RuntimePoint3::new(&tx, &ty, &tz))
}

pub fn squared_distance_point_segment_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint3<R, V>, a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(),
        !norm_sq3::<V>(sub3::<V>(b.model@, a.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model() == squared_distance_point_segment_3d::<V>(q.model@, a.model@, b.model@),
{
    let cp = closest_point_on_segment_3d_exec(q, a, b);
    let (dx, dy, dz) = &cp.sub(q);
    norm_sq3_exec(&dx, &dy, &dz)
}

} //  verus!
