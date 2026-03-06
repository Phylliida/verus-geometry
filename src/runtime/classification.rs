#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::RationalModel;
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
use verus_rational::rational::Rational;
#[cfg(verus_keep_ghost)]
use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// Helper: bridge signum ↔ OrderedRing lt/eqv
// ---------------------------------------------------------------------------

/// Connect RuntimeRational signum to the Rational OrderedRing trait lt/eqv.
///
/// Since all specs are open:
/// - `Rational::zero() = from_int_spec(0) = Rational { num: 0, den: 0 }`
/// - `Rational::zero().lt(v) = from_int_spec(0).lt_spec(v) = 0 * v.denom() < v.num * 1 = 0 < v.num`
/// - `v.signum() == 1` iff `v.num > 0`
/// So `Rational::zero().lt(v)` iff `v.signum() == 1`.
pub proof fn lemma_signum_bridge(val: RationalModel)
    ensures
        (val.signum() == 1) == Rational::from_int_spec(0).lt_spec(val),
        (val.signum() == -1) == val.lt_spec(Rational::from_int_spec(0)),
        (val.signum() == 0) == val.eqv_spec(Rational::from_int_spec(0)),
{
    Rational::lemma_signum_positive_iff(val);
    Rational::lemma_signum_negative_iff(val);
    Rational::lemma_signum_zero_iff(val);
    Rational::lemma_denom_positive(val);
    let zero = Rational::from_int_spec(0);
    assert(zero.num == 0);
    assert(zero.den == 0nat);
    assert(zero.denom_nat() == 1nat);
    assert(zero.denom() == 1);
    assert(zero.lt_spec(val) == (0 * val.denom() < val.num * 1));
    assert(val.lt_spec(zero) == (val.num * 1 < 0 * val.denom()));
    assert(val.eqv_spec(zero) == (val.num * 1 == 0 * val.denom()));
}

// ---------------------------------------------------------------------------
// orient2d_sign_exec
// ---------------------------------------------------------------------------

pub fn orient2d_sign_exec(
    a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: OrientationSign)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == orient2d_sign::<RationalModel>(a@, b@, c@),
{
    let val = orient2d_exec(a, b, c);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    if s == 1i8 {
        OrientationSign::Positive
    } else if s == -1i8 {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

// ---------------------------------------------------------------------------
// orient3d_sign_exec
// ---------------------------------------------------------------------------

pub fn orient3d_sign_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: OrientationSign)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == orient3d_sign::<RationalModel>(a@, b@, c@, d@),
{
    let val = orient3d_exec(a, b, c, d);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    if s == 1i8 {
        OrientationSign::Positive
    } else if s == -1i8 {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

// ---------------------------------------------------------------------------
// Boolean predicates: 2D line sidedness
// ---------------------------------------------------------------------------

/// Test collinearity: orient2d(a, b, c) ≡ 0
pub fn collinear2d_exec(
    a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == collinear2d::<RationalModel>(a@, b@, c@),
{
    let val = orient2d_exec(a, b, c);
    let z = val.is_zero();
    proof {
        // collinear2d(a@,b@,c@) = orient2d(a@,b@,c@).eqv(zero())
        // is_zero ensures: z == val@.eqv_spec(from_int_spec(0))
        // Since Rational::eqv = eqv_spec and Rational::zero() = from_int_spec(0),
        // orient2d(a@,b@,c@).eqv(RationalModel::zero()) = val@.eqv_spec(from_int_spec(0)) = z
    }
    z
}

/// Test 3D collinearity: cross(b-a, c-a) ≡ Vec3::zero()
pub fn collinear3d_exec(
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == collinear3d::<RationalModel>(a@, b@, c@),
{
    use super::point3::{sub3_exec, cross_exec};
    let ba = sub3_exec(b, a);
    let ca = sub3_exec(c, a);
    let cr = cross_exec(&ba, &ca);
    cr.x.is_zero() && cr.y.is_zero() && cr.z.is_zero()
}

/// Test coplanarity: orient3d(a,b,c,d) ≡ 0
pub fn coplanar_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == coplanar::<RationalModel>(a@, b@, c@, d@),
{
    let val = orient3d_exec(a, b, c, d);
    val.is_zero()
}

/// Point is strictly left of line a→b
pub fn point_left_of_line_exec(
    p: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out == point_left_of_line::<RationalModel>(p@, a@, b@),
{
    let val = orient2d_exec(a, b, p);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    s == 1i8
}

/// Point is strictly right of line a→b
pub fn point_right_of_line_exec(
    p: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out == point_right_of_line::<RationalModel>(p@, a@, b@),
{
    let val = orient2d_exec(a, b, p);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    s == -1i8
}

/// Point lies on line through a and b
pub fn point_on_line_exec(
    p: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out == point_on_line::<RationalModel>(p@, a@, b@),
{
    let val = orient2d_exec(a, b, p);
    let z = val.is_zero();
    proof {
        // point_on_line = orient2d_zero(a, b, p) = orient2d(a,b,p).eqv(zero())
    }
    z
}

// ---------------------------------------------------------------------------
// Boolean predicates: 3D plane sidedness
// ---------------------------------------------------------------------------

/// Point is strictly above oriented plane (a, b, c)
pub fn point_above_plane_exec(
    p: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == point_above_plane::<RationalModel>(p@, a@, b@, c@),
{
    let val = orient3d_exec(a, b, c, p);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    s == 1i8
}

/// Point is strictly below oriented plane (a, b, c)
pub fn point_below_plane_exec(
    p: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == point_below_plane::<RationalModel>(p@, a@, b@, c@),
{
    let val = orient3d_exec(a, b, c, p);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    s == -1i8
}

/// Point lies on the plane through a, b, c
pub fn point_on_plane_exec(
    p: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == point_on_plane::<RationalModel>(p@, a@, b@, c@),
{
    let val = orient3d_exec(a, b, c, p);
    val.is_zero()
}

/// Segment (d, e) strictly crosses the oriented plane (a, b, c)
pub fn segment_crosses_plane_strict_exec(
    d: &RuntimePoint3, e: &RuntimePoint3,
    a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3,
) -> (out: bool)
    requires
        d.wf_spec(),
        e.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
    ensures
        out == segment_crosses_plane_strict::<RationalModel>(d@, e@, a@, b@, c@),
{
    let above_d = point_above_plane_exec(d, a, b, c);
    let below_d = point_below_plane_exec(d, a, b, c);
    let above_e = point_above_plane_exec(e, a, b, c);
    let below_e = point_below_plane_exec(e, a, b, c);
    (above_d && below_e) || (below_d && above_e)
}

// ---------------------------------------------------------------------------
// Consistent face orientation
// ---------------------------------------------------------------------------

/// Two adjacent triangles have consistent orientation.
pub fn faces_consistently_oriented_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == crate::face_normal::faces_consistently_oriented::<RationalModel>(a@, b@, c@, d@),
{
    point_above_plane_exec(d, a, b, c)
}

// ---------------------------------------------------------------------------
// Incircle sign
// ---------------------------------------------------------------------------

/// Compute the incircle determinant at runtime.
fn incircle2d_compute(
    a: &RuntimePoint2, b: &RuntimePoint2,
    c: &RuntimePoint2, d: &RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == incircle2d::<RationalModel>(a@, b@, c@, d@),
{
    // p = a - d, q = b - d, r = c - d
    let px = a.x.sub(&d.x);
    let py = a.y.sub(&d.y);
    let qx = b.x.sub(&d.x);
    let qy = b.y.sub(&d.y);
    let rx = c.x.sub(&d.x);
    let ry = c.y.sub(&d.y);

    // lift coords: pw = px² + py², qw = qx² + qy², rw = rx² + ry²
    let pw = px.mul(&px).add(&py.mul(&py));
    let qw = qx.mul(&qx).add(&qy.mul(&qy));
    let rw = rx.mul(&rx).add(&ry.mul(&ry));

    // det2d(q, r) = qx*ry - qy*rx
    let det_qr = qx.mul(&ry).sub(&qy.mul(&rx));
    // det2d(p, r) = px*ry - py*rx
    let det_pr = px.mul(&ry).sub(&py.mul(&rx));
    // det2d(p, q) = px*qy - py*qx
    let det_pq = px.mul(&qy).sub(&py.mul(&qx));

    // pw * det_qr - qw * det_pr + rw * det_pq
    pw.mul(&det_qr).sub(&qw.mul(&det_pr)).add(&rw.mul(&det_pq))
}

/// Classify the incircle sign: Positive (inside), Negative (outside), Zero (cocircular).
pub fn incircle2d_sign_exec(
    a: &RuntimePoint2, b: &RuntimePoint2,
    c: &RuntimePoint2, d: &RuntimePoint2,
) -> (out: OrientationSign)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == incircle2d_sign::<RationalModel>(a@, b@, c@, d@),
{
    let val = incircle2d_compute(a, b, c, d);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    if s == 1i8 {
        OrientationSign::Positive
    } else if s == -1i8 {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

// ---------------------------------------------------------------------------
// Insphere sign
// ---------------------------------------------------------------------------

/// Compute the insphere determinant at runtime.
fn insphere3d_compute(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3, e: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
        e.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == insphere3d::<RationalModel>(a@, b@, c@, d@, e@),
{
    use super::point3::sub3_exec;
    use verus_linalg::runtime::vec3::RuntimeVec3;

    // p = a - e, q = b - e, r = c - e, s = d - e
    let p = sub3_exec(a, e);
    let q = sub3_exec(b, e);
    let r = sub3_exec(c, e);
    let s = sub3_exec(d, e);

    // lift coords
    let pw = p.norm_sq_exec();
    let qw = q.norm_sq_exec();
    let rw = r.norm_sq_exec();
    let sw = s.norm_sq_exec();

    // triple products
    let t_qrs = q.triple_exec(&r, &s);
    let t_prs = p.triple_exec(&r, &s);
    let t_pqs = p.triple_exec(&q, &s);
    let t_pqr = p.triple_exec(&q, &r);

    // pw * t_qrs - qw * t_prs + rw * t_pqs - sw * t_pqr
    pw.mul(&t_qrs).sub(&qw.mul(&t_prs)).add(&rw.mul(&t_pqs)).sub(&sw.mul(&t_pqr))
}

/// Classify the insphere sign: Positive (inside), Negative (outside), Zero (cospherical).
pub fn insphere3d_sign_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3, e: &RuntimePoint3,
) -> (out: OrientationSign)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
        e.wf_spec(),
    ensures
        out == insphere3d_sign::<RationalModel>(a@, b@, c@, d@, e@),
{
    let val = insphere3d_compute(a, b, c, d, e);
    let s = val.signum();
    proof {
        lemma_signum_bridge(val@);
    }
    if s == 1i8 {
        OrientationSign::Positive
    } else if s == -1i8 {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

} // verus!
