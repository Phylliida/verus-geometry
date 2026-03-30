use verus_rational::RuntimeRational;

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

pub fn sign_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    val: &R,
) -> (out: OrientationSign)
    requires val.wf_spec(),
    ensures
        out == (if val.rf_view().eqv(V::zero()) { OrientationSign::Zero }
                else if V::zero().lt(val.rf_view()) { OrientationSign::Positive }
                else { OrientationSign::Negative }),
{
    let zero = val.rf_zero_like();
    if val.rf_eq(&zero) {
        OrientationSign::Zero
    } else if zero.rf_lt(val) {
        OrientationSign::Positive
    } else {
        OrientationSign::Negative
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
    let zero = val.rf_zero_like();
    val.rf_eq(&zero)
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
    let zero = val.rf_zero_like();
    zero.rf_lt(&val)
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
    let zero = val.rf_zero_like();
    val.rf_lt(&zero)
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
    let zero = val.rf_zero_like();
    val.rf_eq(&zero)
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
    let (bax, bay, baz) = super::point3::sub3_exec(b, a);
    let (cax, cay, caz) = super::point3::sub3_exec(c, a);
    let (crx, cry, crz) = super::point3::cross_exec(&bax, &bay, &baz, &cax, &cay, &caz);
    let zero = crx.rf_zero_like();
    crx.rf_eq(&zero) && cry.rf_eq(&zero) && crz.rf_eq(&zero)
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
    let zero = val.rf_zero_like();
    val.rf_eq(&zero)
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
    let zero = val.rf_zero_like();
    zero.rf_lt(&val)
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
    let zero = val.rf_zero_like();
    val.rf_lt(&zero)
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
    let zero = val.rf_zero_like();
    val.rf_eq(&zero)
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
    ensures out.wf_spec(), out.rf_view() == incircle2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let px = a.x.rf_sub(&d.x);
    let py = a.y.rf_sub(&d.y);
    let qx = b.x.rf_sub(&d.x);
    let qy = b.y.rf_sub(&d.y);
    let rx = c.x.rf_sub(&d.x);
    let ry = c.y.rf_sub(&d.y);

    let pw = px.rf_mul(&px).rf_add(&py.rf_mul(&py));
    let qw = qx.rf_mul(&qx).rf_add(&qy.rf_mul(&qy));
    let rw = rx.rf_mul(&rx).rf_add(&ry.rf_mul(&ry));

    let det_qr = qx.rf_mul(&ry).rf_sub(&qy.rf_mul(&rx));
    let det_pr = px.rf_mul(&ry).rf_sub(&py.rf_mul(&rx));
    let det_pq = px.rf_mul(&qy).rf_sub(&py.rf_mul(&qx));

    pw.rf_mul(&det_qr).rf_sub(&qw.rf_mul(&det_pr)).rf_add(&rw.rf_mul(&det_pq))
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
    ensures out.wf_spec(), out.rf_view() == insphere3d::<V>(a.model@, b.model@, c.model@, d.model@, e.model@),
{
    use super::point3::{sub3_exec, cross_exec, dot3_exec};

    let (px, py, pz) = sub3_exec(a, e);
    let (qx, qy, qz) = sub3_exec(b, e);
    let (rx, ry, rz) = sub3_exec(c, e);
    let (sx, sy, sz) = sub3_exec(d, e);

    //  lift: w = x² + y² + z²
    let pw = px.rf_mul(&px).rf_add(&py.rf_mul(&py)).rf_add(&pz.rf_mul(&pz));
    let qw = qx.rf_mul(&qx).rf_add(&qy.rf_mul(&qy)).rf_add(&qz.rf_mul(&qz));
    let rw = rx.rf_mul(&rx).rf_add(&ry.rf_mul(&ry)).rf_add(&rz.rf_mul(&rz));
    let sw = sx.rf_mul(&sx).rf_add(&sy.rf_mul(&sy)).rf_add(&sz.rf_mul(&sz));

    //  triple products: dot(a, cross(b, c))
    let (cr_rs_x, cr_rs_y, cr_rs_z) = cross_exec(&rx, &ry, &rz, &sx, &sy, &sz);
    let t_qrs = dot3_exec(&qx, &qy, &qz, &cr_rs_x, &cr_rs_y, &cr_rs_z);

    let (cr_rs2_x, cr_rs2_y, cr_rs2_z) = cross_exec(&rx, &ry, &rz, &sx, &sy, &sz);
    let t_prs = dot3_exec(&px, &py, &pz, &cr_rs2_x, &cr_rs2_y, &cr_rs2_z);

    let (cr_qs_x, cr_qs_y, cr_qs_z) = cross_exec(&qx, &qy, &qz, &sx, &sy, &sz);
    let t_pqs = dot3_exec(&px, &py, &pz, &cr_qs_x, &cr_qs_y, &cr_qs_z);

    let (cr_qr_x, cr_qr_y, cr_qr_z) = cross_exec(&qx, &qy, &qz, &rx, &ry, &rz);
    let t_pqr = dot3_exec(&px, &py, &pz, &cr_qr_x, &cr_qr_y, &cr_qr_z);

    pw.rf_mul(&t_qrs).rf_sub(&qw.rf_mul(&t_prs)).rf_add(&rw.rf_mul(&t_pqs)).rf_sub(&sw.rf_mul(&t_pqr))
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
