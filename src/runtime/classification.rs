
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use super::orient::{orient2d_exec, orient3d_exec};
#[cfg(verus_keep_ghost)]
use crate::orientation_sign::*;
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::orient3d::orient3d;
#[cfg(verus_keep_ghost)]
use crate::collinearity::{collinear2d, collinear3d, coplanar};
#[cfg(verus_keep_ghost)]
use crate::sidedness::*;
#[cfg(verus_keep_ghost)]
use crate::incircle::*;
#[cfg(verus_keep_ghost)]
use crate::insphere::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  Generic sign detection: classifies a value as Positive, Negative, or Zero
//  using only the RuntimeOrderedFieldOps trait.
//  ---------------------------------------------------------------------------

///  Classify a scalar's sign, matching the spec `scalar_sign` definition:
///  zero.lt(val) → Positive, val.lt(zero) → Negative, else → Zero.
pub fn sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    val: &R,
) -> (out: OrientationSign)
    requires val.wf_spec(),
    ensures
        out == scalar_sign::<V>(val@),
{
    let zero = val.zero_like();
    if zero.lt(val) {
        OrientationSign::Positive
    } else if val.lt(&zero) {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

//  ---------------------------------------------------------------------------
//  orient2d_sign_exec (generic)
//  ---------------------------------------------------------------------------

pub fn orient2d_sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>,
) -> (out: OrientationSign)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == orient2d_sign::<V>(a.model@, b.model@, c.model@),
{
    let val = orient2d_exec(a, b, c);
    sign_exec(&val)
}

//  ---------------------------------------------------------------------------
//  orient3d_sign_exec (generic)
//  ---------------------------------------------------------------------------

pub fn orient3d_sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
    d: &RuntimePoint3<R, V>,
) -> (out: OrientationSign)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == orient3d_sign::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let val = orient3d_exec(a, b, c, d);
    sign_exec(&val)
}

//  ---------------------------------------------------------------------------
//  Boolean predicates: 2D (generic)
//  ---------------------------------------------------------------------------

pub fn collinear2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == collinear2d::<V>(a.model@, b.model@, c.model@),
{
    let val = orient2d_exec(a, b, c);
    let zero = val.zero_like();
    val.eq(&zero)
}

pub fn point_left_of_line_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(),
    ensures out == point_left_of_line::<V>(p.model@, a.model@, b.model@),
{
    let val = orient2d_exec(a, b, p);
    let zero = val.zero_like();
    zero.lt(&val)
}

pub fn point_right_of_line_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(),
    ensures out == point_right_of_line::<V>(p.model@, a.model@, b.model@),
{
    let val = orient2d_exec(a, b, p);
    let zero = val.zero_like();
    val.lt(&zero)
}

pub fn point_on_line_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(),
    ensures out == point_on_line::<V>(p.model@, a.model@, b.model@),
{
    let val = orient2d_exec(a, b, p);
    let zero = val.zero_like();
    val.eq(&zero)
}

//  ---------------------------------------------------------------------------
//  Boolean predicates: 3D (generic)
//  ---------------------------------------------------------------------------

pub fn collinear3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == collinear3d::<V>(a.model@, b.model@, c.model@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let cr = ba.cross(&ca);
    let zero = cr.x.zero_like();
    cr.x.eq(&zero) && cr.y.eq(&zero) && cr.z.eq(&zero)
}

pub fn coplanar_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
    d: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == coplanar::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let val = orient3d_exec(a, b, c, d);
    let zero = val.zero_like();
    val.eq(&zero)
}

pub fn point_above_plane_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == point_above_plane::<V>(p.model@, a.model@, b.model@, c.model@),
{
    let val = orient3d_exec(a, b, c, p);
    let zero = val.zero_like();
    zero.lt(&val)
}

pub fn point_below_plane_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == point_below_plane::<V>(p.model@, a.model@, b.model@, c.model@),
{
    let val = orient3d_exec(a, b, c, p);
    let zero = val.zero_like();
    val.lt(&zero)
}

pub fn point_on_plane_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == point_on_plane::<V>(p.model@, a.model@, b.model@, c.model@),
{
    let val = orient3d_exec(a, b, c, p);
    let zero = val.zero_like();
    val.eq(&zero)
}

pub fn segment_crosses_plane_strict_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    d: &RuntimePoint3<R, V>, e: &RuntimePoint3<R, V>,
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires d.wf_spec(), e.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == segment_crosses_plane_strict::<V>(d.model@, e.model@, a.model@, b.model@, c.model@),
{
    let above_d = point_above_plane_exec(d, a, b, c);
    let below_d = point_below_plane_exec(d, a, b, c);
    let above_e = point_above_plane_exec(e, a, b, c);
    let below_e = point_below_plane_exec(e, a, b, c);
    (above_d && below_e) || (below_d && above_e)
}

pub fn faces_consistently_oriented_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == crate::face_normal::faces_consistently_oriented::<V>(a.model@, b.model@, c.model@, d.model@),
{
    point_above_plane_exec(d, a, b, c)
}

//  ---------------------------------------------------------------------------
//  Incircle / Insphere (generic)
//  ---------------------------------------------------------------------------

fn incircle2d_compute<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out.wf_spec(), out@ == incircle2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let px = a.x.sub(&d.x);
    let py = a.y.sub(&d.y);
    let qx = b.x.sub(&d.x);
    let qy = b.y.sub(&d.y);
    let rx = c.x.sub(&d.x);
    let ry = c.y.sub(&d.y);

    let pw = px.mul(&px).add(&py.mul(&py));
    let qw = qx.mul(&qx).add(&qy.mul(&qy));
    let rw = rx.mul(&rx).add(&ry.mul(&ry));

    let det_qr = qx.mul(&ry).sub(&qy.mul(&rx));
    let det_pr = px.mul(&ry).sub(&py.mul(&rx));
    let det_pq = px.mul(&qy).sub(&py.mul(&qx));

    pw.mul(&det_qr).sub(&qw.mul(&det_pr)).add(&rw.mul(&det_pq))
}

pub fn incircle2d_sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: OrientationSign)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == incircle2d_sign::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let val = incircle2d_compute(a, b, c, d);
    sign_exec(&val)
}

fn insphere3d_compute<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>, e: &RuntimePoint3<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(), e.wf_spec(),
    ensures out.wf_spec(), out@ == insphere3d::<V>(a.model@, b.model@, c.model@, d.model@, e.model@),
{
    let p = a.sub(e);
    let q = b.sub(e);
    let r = c.sub(e);
    let s = d.sub(e);

    let pw = p.norm_sq();
    let qw = q.norm_sq();
    let rw = r.norm_sq();
    let sw = s.norm_sq();

    let t_qrs = q.dot(&r.cross(&s));
    let t_prs = p.dot(&r.cross(&s));
    let t_pqs = p.dot(&q.cross(&s));
    let t_pqr = p.dot(&q.cross(&r));

    pw.mul(&t_qrs).sub(&qw.mul(&t_prs)).add(&rw.mul(&t_pqs)).sub(&sw.mul(&t_pqr))
}

pub fn insphere3d_sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>, e: &RuntimePoint3<R, V>,
) -> (out: OrientationSign)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(), e.wf_spec(),
    ensures out == insphere3d_sign::<V>(a.model@, b.model@, c.model@, d.model@, e.model@),
{
    let val = insphere3d_compute(a, b, c, d, e);
    sign_exec(&val)
}

} //  verus!
