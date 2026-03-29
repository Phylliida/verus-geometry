use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq as vec2_norm_sq;
use verus_linalg::vec2::ops::{dot as vec2_dot, norm_sq};
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;

verus! {

//  =========================================================================
//  Spec functions
//  =========================================================================

///  The "lift" coordinate for incircle: norm_sq(v) = v.x² + v.y²
pub open spec fn lift<T: Ring>(v: Vec2<T>) -> T {
    vec2_norm_sq(v)
}

///  Incircle determinant: tests if d is inside the circumcircle of (a, b, c).
///
///  Defined as the 3×3 determinant with rows:
///    (ax-dx, ay-dy, (ax-dx)²+(ay-dy)²)
///    (bx-dx, by-dy, (bx-dx)²+(by-dy)²)
///    (cx-dx, cy-dy, (cx-dx)²+(cy-dy)²)
///
///  Convention: positive when d is inside the circumcircle of a CCW-oriented
///  triangle (a, b, c).
pub open spec fn incircle2d<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> T {
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);
    //  Cofactor expansion along the third column:
    //  pw * det2d(q, r) - qw * det2d(p, r) + rw * det2d(p, q)
    pw.mul(det2d(q, r))
        .sub(qw.mul(det2d(p, r)))
        .add(rw.mul(det2d(p, q)))
}

///  Sign classification of the incircle predicate.
pub open spec fn incircle2d_sign<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> OrientationSign {
    scalar_sign(incircle2d(a, b, c, d))
}

///  d is strictly inside the circumcircle of (a, b, c), assuming CCW orientation.
pub open spec fn incircle2d_positive<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    T::zero().lt(incircle2d(a, b, c, d))
}

///  d is strictly outside the circumcircle of (a, b, c), assuming CCW orientation.
pub open spec fn incircle2d_negative<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d(a, b, c, d).lt(T::zero())
}

///  d is on the circumcircle of (a, b, c).
pub open spec fn incircle2d_cocircular<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d(a, b, c, d).eqv(T::zero())
}

//  =========================================================================
//  Helper: zero-row proof pattern
//  =========================================================================

///  If v is the zero vector at the eqv level, then lift(v) ≡ 0.
proof fn lemma_lift_zero_eqv<T: Ring>(v: Vec2<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
    ensures
        lift(v).eqv(T::zero()),
{
    //  v.x * v.x ≡ 0 * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.x, T::zero(), v.x, T::zero());
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(v.x.mul(v.x), T::zero().mul(T::zero()), T::zero());

    //  v.y * v.y ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.y, T::zero(), v.y, T::zero());
    T::axiom_eqv_transitive(v.y.mul(v.y), T::zero().mul(T::zero()), T::zero());

    //  lift(v) = v.x*v.x + v.y*v.y ≡ 0 + 0 ≡ 0
    T::axiom_add_congruence_left(v.x.mul(v.x), T::zero(), v.y.mul(v.y));
    additive_group_lemmas::lemma_add_congruence_right::<T>(T::zero(), v.y.mul(v.y), T::zero());
    T::axiom_eqv_transitive(
        v.x.mul(v.x).add(v.y.mul(v.y)),
        T::zero().add(v.y.mul(v.y)),
        T::zero().add(T::zero()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        v.x.mul(v.x).add(v.y.mul(v.y)),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

///  If u has zero components, then det2d(u, w) ≡ 0.
proof fn lemma_det2d_zero_left<T: Ring>(u: Vec2<T>, w: Vec2<T>)
    requires
        u.x.eqv(T::zero()),
        u.y.eqv(T::zero()),
    ensures
        det2d(u, w).eqv(T::zero()),
{
    //  u.x * w.y ≡ 0 * w.y ≡ 0
    T::axiom_mul_congruence_left(u.x, T::zero(), w.y);
    ring_lemmas::lemma_mul_zero_left::<T>(w.y);
    T::axiom_eqv_transitive(u.x.mul(w.y), T::zero().mul(w.y), T::zero());

    //  u.y * w.x ≡ 0 * w.x ≡ 0
    T::axiom_mul_congruence_left(u.y, T::zero(), w.x);
    ring_lemmas::lemma_mul_zero_left::<T>(w.x);
    T::axiom_eqv_transitive(u.y.mul(w.x), T::zero().mul(w.x), T::zero());

    //  det2d(u, w) = u.x*w.y - u.y*w.x ≡ 0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(w.y), T::zero(), u.y.mul(w.x), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(det2d(u, w), T::zero().sub(T::zero()), T::zero());
}

///  If w has zero components, then det2d(u, w) ≡ 0.
proof fn lemma_det2d_zero_right<T: Ring>(u: Vec2<T>, w: Vec2<T>)
    requires
        w.x.eqv(T::zero()),
        w.y.eqv(T::zero()),
    ensures
        det2d(u, w).eqv(T::zero()),
{
    //  u.x * w.y ≡ u.x * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(u.x, w.y, T::zero());
    T::axiom_mul_zero_right(u.x);
    T::axiom_eqv_transitive(u.x.mul(w.y), u.x.mul(T::zero()), T::zero());

    //  u.y * w.x ≡ u.y * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(u.y, w.x, T::zero());
    T::axiom_mul_zero_right(u.y);
    T::axiom_eqv_transitive(u.y.mul(w.x), u.y.mul(T::zero()), T::zero());

    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(w.y), T::zero(), u.y.mul(w.x), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(det2d(u, w), T::zero().sub(T::zero()), T::zero());
}

///  Combine: when one vector in the incircle triple has zero components,
///  the full 3×3 determinant is zero.
///
///  If p is the zero-row: pw=0, det2d(p,r)=0, det2d(p,q)=0, so
///  incircle = 0*det2d(q,r) - qw*0 + rw*0 = 0.
proof fn lemma_incircle_zero_first_row<T: Ring>(
    p: Vec2<T>, q: Vec2<T>, r: Vec2<T>,
)
    requires
        p.x.eqv(T::zero()),
        p.y.eqv(T::zero()),
    ensures ({
        let pw = lift(p);
        let qw = lift(q);
        let rw = lift(r);
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))).eqv(T::zero())
    }),
{
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  pw ≡ 0
    lemma_lift_zero_eqv::<T>(p);

    //  pw * det2d(q, r) ≡ 0 * det2d(q, r) ≡ 0
    T::axiom_mul_congruence_left(pw, T::zero(), det2d(q, r));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(q, r));
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), T::zero().mul(det2d(q, r)), T::zero());

    //  det2d(p, r) ≡ 0
    lemma_det2d_zero_left::<T>(p, r);
    //  qw * det2d(p, r) ≡ qw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(qw, det2d(p, r), T::zero());
    T::axiom_mul_zero_right(qw);
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), qw.mul(T::zero()), T::zero());

    //  det2d(p, q) ≡ 0
    lemma_det2d_zero_left::<T>(p, q);
    //  rw * det2d(p, q) ≡ rw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(p, q), T::zero());
    T::axiom_mul_zero_right(rw);
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), rw.mul(T::zero()), T::zero());

    //  0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw.mul(det2d(q, r)), T::zero(),
        qw.mul(det2d(p, r)), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero().sub(T::zero()),
        T::zero(),
    );

    //  0 + 0 ≡ 0
    T::axiom_add_congruence_left(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero(),
        rw.mul(det2d(p, q)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), rw.mul(det2d(p, q)), T::zero(),
    );
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

///  Same pattern for zero second row.
proof fn lemma_incircle_zero_second_row<T: Ring>(
    p: Vec2<T>, q: Vec2<T>, r: Vec2<T>,
)
    requires
        q.x.eqv(T::zero()),
        q.y.eqv(T::zero()),
    ensures ({
        let pw = lift(p);
        let qw = lift(q);
        let rw = lift(r);
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))).eqv(T::zero())
    }),
{
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  qw ≡ 0
    lemma_lift_zero_eqv::<T>(q);

    //  det2d(q, r) ≡ 0
    lemma_det2d_zero_left::<T>(q, r);
    //  pw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(q, r), T::zero());
    T::axiom_mul_zero_right(pw);
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), pw.mul(T::zero()), T::zero());

    //  qw * det2d(p, r) ≡ 0 * det2d(p, r) ≡ 0
    T::axiom_mul_congruence_left(qw, T::zero(), det2d(p, r));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(p, r));
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), T::zero().mul(det2d(p, r)), T::zero());

    //  det2d(p, q) = det2d(p, q) where q has zero components → det2d zero right
    lemma_det2d_zero_right::<T>(p, q);
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(p, q), T::zero());
    T::axiom_mul_zero_right(rw);
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), rw.mul(T::zero()), T::zero());

    //  0 - 0 + 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw.mul(det2d(q, r)), T::zero(),
        qw.mul(det2d(p, r)), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero().sub(T::zero()),
        T::zero(),
    );

    T::axiom_add_congruence_left(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero(),
        rw.mul(det2d(p, q)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), rw.mul(det2d(p, q)), T::zero(),
    );
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

///  Same pattern for zero third row.
proof fn lemma_incircle_zero_third_row<T: Ring>(
    p: Vec2<T>, q: Vec2<T>, r: Vec2<T>,
)
    requires
        r.x.eqv(T::zero()),
        r.y.eqv(T::zero()),
    ensures ({
        let pw = lift(p);
        let qw = lift(q);
        let rw = lift(r);
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))).eqv(T::zero())
    }),
{
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  rw ≡ 0
    lemma_lift_zero_eqv::<T>(r);

    //  det2d(q, r) ≡ 0 (r is zero)
    lemma_det2d_zero_right::<T>(q, r);
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(q, r), T::zero());
    T::axiom_mul_zero_right(pw);
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), pw.mul(T::zero()), T::zero());

    //  det2d(p, r) ≡ 0 (r is zero)
    lemma_det2d_zero_right::<T>(p, r);
    ring_lemmas::lemma_mul_congruence_right::<T>(qw, det2d(p, r), T::zero());
    T::axiom_mul_zero_right(qw);
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), qw.mul(T::zero()), T::zero());

    //  rw * det2d(p, q) ≡ 0 * det2d(p, q) ≡ 0
    T::axiom_mul_congruence_left(rw, T::zero(), det2d(p, q));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(p, q));
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), T::zero().mul(det2d(p, q)), T::zero());

    //  0 - 0 + 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw.mul(det2d(q, r)), T::zero(),
        qw.mul(det2d(p, r)), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero().sub(T::zero()),
        T::zero(),
    );

    T::axiom_add_congruence_left(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        T::zero(),
        rw.mul(det2d(p, q)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), rw.mul(det2d(p, q)), T::zero(),
    );
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

//  =========================================================================
//  Degenerate lemmas
//  =========================================================================

///  When d coincides with a, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_da<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, a).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(a);
    lemma_incircle_zero_first_row::<T>(sub2(a, a), sub2(b, a), sub2(c, a));
}

///  When d coincides with b, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_db<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, b).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(b);
    lemma_incircle_zero_second_row::<T>(sub2(a, b), sub2(b, b), sub2(c, b));
}

///  When d coincides with c, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_dc<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, c).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(c);
    lemma_incircle_zero_third_row::<T>(sub2(a, c), sub2(b, c), sub2(c, c));
}

//  =========================================================================
//  Trichotomy and sign classification
//  =========================================================================

///  Exactly one of {positive, negative, cocircular} holds.
pub proof fn lemma_incircle2d_trichotomy<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_positive(a, b, c, d) || incircle2d_negative(a, b, c, d) || incircle2d_cocircular(a, b, c, d),
        !(incircle2d_positive(a, b, c, d) && incircle2d_negative(a, b, c, d)),
        !(incircle2d_positive(a, b, c, d) && incircle2d_cocircular(a, b, c, d)),
        !(incircle2d_negative(a, b, c, d) && incircle2d_cocircular(a, b, c, d)),
{
    let val = incircle2d(a, b, c, d);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());
}

///  The sign classification matches the scalar value.
pub proof fn lemma_incircle2d_sign_matches<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        (incircle2d_sign(a, b, c, d) == OrientationSign::Positive) == incircle2d_positive(a, b, c, d),
        (incircle2d_sign(a, b, c, d) == OrientationSign::Negative) == incircle2d_negative(a, b, c, d),
        (incircle2d_sign(a, b, c, d) == OrientationSign::Zero) == incircle2d_cocircular(a, b, c, d),
{
    let val = incircle2d(a, b, c, d);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());

    if T::zero().eqv(val) {
        T::axiom_eqv_symmetric(T::zero(), val);
    }
    if val.eqv(T::zero()) {
        T::axiom_eqv_symmetric(val, T::zero());
    }
}

//  =========================================================================
//  Lift congruence helper
//  =========================================================================

///  If p and q are component-wise equivalent, lift(p) ≡ lift(q).
proof fn lemma_lift_congruence<T: Ring>(p: Vec2<T>, q: Vec2<T>)
    requires
        p.x.eqv(q.x),
        p.y.eqv(q.y),
    ensures
        lift(p).eqv(lift(q)),
{
    //  p.x*p.x ≡ q.x*q.x
    ring_lemmas::lemma_mul_congruence::<T>(p.x, q.x, p.x, q.x);
    //  p.y*p.y ≡ q.y*q.y
    ring_lemmas::lemma_mul_congruence::<T>(p.y, q.y, p.y, q.y);
    //  sum ≡ sum
    T::axiom_add_congruence_left(p.x.mul(p.x), q.x.mul(q.x), p.y.mul(p.y));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        q.x.mul(q.x), p.y.mul(p.y), q.y.mul(q.y),
    );
    T::axiom_eqv_transitive(
        p.x.mul(p.x).add(p.y.mul(p.y)),
        q.x.mul(q.x).add(p.y.mul(p.y)),
        q.x.mul(q.x).add(q.y.mul(q.y)),
    );
}

//  =========================================================================
//  Translation invariance
//  =========================================================================

///  Incircle2d is invariant under uniform translation of all four points.
///
///  This follows because incircle2d only depends on pairwise differences
///  sub2(a, d), sub2(b, d), sub2(c, d), and translation cancels in differences.
pub proof fn lemma_incircle2d_translation<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
    v: Vec2<T>,
)
    ensures
        incircle2d(add_vec2(a, v), add_vec2(b, v), add_vec2(c, v), add_vec2(d, v))
            .eqv(incircle2d(a, b, c, d)),
{
    let a2 = add_vec2(a, v);
    let b2 = add_vec2(b, v);
    let c2 = add_vec2(c, v);
    let d2 = add_vec2(d, v);

    //  Difference vectors are equivalent after translation
    lemma_sub2_translation::<T>(d, a, v); //  sub2(a+v, d+v) .eqv. sub2(a, d)
    lemma_sub2_translation::<T>(d, b, v); //  sub2(b+v, d+v) .eqv. sub2(b, d)
    lemma_sub2_translation::<T>(d, c, v); //  sub2(c+v, d+v) .eqv. sub2(c, d)

    let p2 = sub2(a2, d2);
    let q2 = sub2(b2, d2);
    let r2 = sub2(c2, d2);
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);

    //  Component-wise equivalences (from Vec2::eqv being component-wise)
    //  p2.eqv(p) means p2.x.eqv(p.x) && p2.y.eqv(p.y)

    //  Lift congruence
    lemma_lift_congruence::<T>(p2, p);
    lemma_lift_congruence::<T>(q2, q);
    lemma_lift_congruence::<T>(r2, r);

    let pw2 = lift(p2);
    let qw2 = lift(q2);
    let rw2 = lift(r2);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  Det2d congruence
    lemma_det2d_congruence::<T>(q2, q, r2, r);  //  det2d(q2,r2) ≡ det2d(q,r)
    lemma_det2d_congruence::<T>(p2, p, r2, r);  //  det2d(p2,r2) ≡ det2d(p,r)
    lemma_det2d_congruence::<T>(p2, p, q2, q);  //  det2d(p2,q2) ≡ det2d(p,q)

    //  Product congruence: pw2*det2d(q2,r2) ≡ pw*det2d(q,r)
    ring_lemmas::lemma_mul_congruence::<T>(pw2, pw, det2d(q2, r2), det2d(q, r));
    //  qw2*det2d(p2,r2) ≡ qw*det2d(p,r)
    ring_lemmas::lemma_mul_congruence::<T>(qw2, qw, det2d(p2, r2), det2d(p, r));
    //  rw2*det2d(p2,q2) ≡ rw*det2d(p,q)
    ring_lemmas::lemma_mul_congruence::<T>(rw2, rw, det2d(p2, q2), det2d(p, q));

    //  Combine: (pw2*D1 - qw2*D2) ≡ (pw*D1 - qw*D2)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw2.mul(det2d(q2, r2)), pw.mul(det2d(q, r)),
        qw2.mul(det2d(p2, r2)), qw.mul(det2d(p, r)),
    );

    //  Final: (...) + rw2*D3 ≡ (...) + rw*D3
    T::axiom_add_congruence_left(
        pw2.mul(det2d(q2, r2)).sub(qw2.mul(det2d(p2, r2))),
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        rw2.mul(det2d(p2, q2)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))),
        rw2.mul(det2d(p2, q2)),
        rw.mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        pw2.mul(det2d(q2, r2)).sub(qw2.mul(det2d(p2, r2))).add(rw2.mul(det2d(p2, q2))),
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw2.mul(det2d(p2, q2))),
        pw.mul(det2d(q, r)).sub(qw.mul(det2d(p, r))).add(rw.mul(det2d(p, q))),
    );
}

//  =========================================================================
//  Swap antisymmetry
//  =========================================================================

///  Swapping a and b negates the incircle determinant.
///
///  incircle2d(b, a, c, d) ≡ -(incircle2d(a, b, c, d))
pub proof fn lemma_incircle2d_swap_ab<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(b, a, c, d).eqv(incircle2d(a, b, c, d).neg()),
{
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  Original = A - B + C  where A=pw*det(q,r), B=qw*det(p,r), C=rw*det(p,q)
    //  Swapped  = B - A + rw*det(q,p)
    let a_term = pw.mul(det2d(q, r));
    let b_term = qw.mul(det2d(p, r));
    let c_term = rw.mul(det2d(p, q));

    //  Step 1: det2d(q, p) ≡ -det2d(p, q)
    lemma_det2d_antisymmetric::<T>(p, q);
    //  gives det2d(p, q) ≡ det2d(q, p).neg()
    //  We need det2d(q, p) ≡ det2d(p, q).neg()
    lemma_det2d_antisymmetric::<T>(q, p);
    //  gives det2d(q, p) ≡ det2d(p, q).neg()

    //  Step 2: rw * det2d(q,p) ≡ rw * (-det2d(p,q))
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(q, p), det2d(p, q).neg());

    //  Step 3: rw * (-det2d(p,q)) ≡ -(rw * det2d(p,q)) = -C
    ring_lemmas::lemma_mul_neg_right::<T>(rw, det2d(p, q));

    //  Step 4: rw * det2d(q,p) ≡ -C
    T::axiom_eqv_transitive(
        rw.mul(det2d(q, p)),
        rw.mul(det2d(p, q).neg()),
        rw.mul(det2d(p, q)).neg(),
    );

    //  Step 5: Swapped = B - A + rw*det(q,p) ≡ B - A + (-C)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b_term.sub(a_term),
        rw.mul(det2d(q, p)),
        c_term.neg(),
    );

    //  Now show: -(A - B + C) ≡ B - A + (-C)

    //  Step 6: -(A - B + C) ≡ -(A-B) + (-C) by neg_add
    additive_group_lemmas::lemma_neg_add::<T>(a_term.sub(b_term), c_term);

    //  Step 7: A.sub(B) ≡ B.sub(A).neg() by sub_antisymmetric
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a_term, b_term);
    //  gives a_term.sub(b_term).eqv(b_term.sub(a_term).neg())

    //  Step 8: -(A-B) = -(B-A).neg().neg() but easier:
    //  A-B ≡ -(B-A), so -(A-B) ≡ -(-(B-A)) ≡ B-A by neg_involution
    additive_group_lemmas::lemma_neg_congruence::<T>(
        a_term.sub(b_term), b_term.sub(a_term).neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(b_term.sub(a_term));
    T::axiom_eqv_transitive(
        a_term.sub(b_term).neg(),
        b_term.sub(a_term).neg().neg(),
        b_term.sub(a_term),
    );

    //  Step 9: -(A-B) + (-C) ≡ (B-A) + (-C)
    T::axiom_add_congruence_left(
        a_term.sub(b_term).neg(),
        b_term.sub(a_term),
        c_term.neg(),
    );

    //  Step 10: Chain: -(A-B+C) ≡ -(A-B)+(-C) ≡ (B-A)+(-C)
    T::axiom_eqv_transitive(
        a_term.sub(b_term).add(c_term).neg(),
        a_term.sub(b_term).neg().add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    //  Step 11: Swapped ≡ (B-A)+(-C) [from Step 5]
    //           -(original) ≡ (B-A)+(-C) [from Step 10]
    //  So: Swapped ≡ -(original) by transitivity

    //  Need symmetry on the neg side:
    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).neg(),
        b_term.sub(a_term).add(c_term.neg()),
    );

    T::axiom_eqv_transitive(
        b_term.sub(a_term).add(rw.mul(det2d(q, p))),
        b_term.sub(a_term).add(c_term.neg()),
        a_term.sub(b_term).add(c_term).neg(),
    );
}

///  Swapping b and c negates the incircle determinant.
pub proof fn lemma_incircle2d_swap_bc<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(a, c, b, d).eqv(incircle2d(a, b, c, d).neg()),
{
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    //  incircle2d(a, c, b, d) uses: p'=sub2(a,d)=p, q'=sub2(c,d)=r, r'=sub2(b,d)=q
    //  = lift(p)*det2d(r, q) - lift(r)*det2d(p, q) + lift(q)*det2d(p, r)

    let a_term = pw.mul(det2d(q, r));  //  A in original
    let b_term = qw.mul(det2d(p, r));  //  B in original
    let c_term = rw.mul(det2d(p, q));  //  C in original

    //  Swapped first term: pw*det2d(r, q) ≡ pw*(-det2d(q, r)) ≡ -A
    lemma_det2d_antisymmetric::<T>(r, q);
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(r, q), det2d(q, r).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(pw, det2d(q, r));
    T::axiom_eqv_transitive(
        pw.mul(det2d(r, q)), pw.mul(det2d(q, r).neg()), a_term.neg(),
    );

    //  Swapped = -A - C + B  (the second/third terms are just rearranged)
    //  Original = A - B + C
    //  Need: -A - C + B ≡ -(A - B + C)

    //  -A - C ≡ -(A + C)  by neg_add reversed
    //  -A - C + B = -(A+C) + B
    //  -(A - B + C) = -A + B - C = B - A - C = B + (-A - C)

    //  Step: swapped first term + second:
    //  pw*det2d(r,q) - rw*det2d(p,q)  ≡ -A - C

    //  sub congruence: pw*det2d(r,q).sub(rw*det2d(p,q)) ≡ (-A).sub(C)
    T::axiom_eqv_reflexive(c_term);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw.mul(det2d(r, q)), a_term.neg(),
        rw.mul(det2d(p, q)), c_term,
    );

    //  -A - C + B is the swapped expression
    //  add congruence:
    T::axiom_eqv_reflexive(b_term);
    additive_group_lemmas::lemma_add_congruence::<T>(
        pw.mul(det2d(r, q)).sub(rw.mul(det2d(p, q))),
        a_term.neg().sub(c_term),
        qw.mul(det2d(p, r)),
        b_term,
    );

    //  So swapped ≡ (-A).sub(C).add(B)

    //  Now show -(A - B + C) ≡ (-A).sub(C).add(B)
    //  -(A - B + C) ≡ -(A-B) + (-C) ≡ (B-A) + (-C)
    additive_group_lemmas::lemma_neg_add::<T>(a_term.sub(b_term), c_term);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a_term, b_term);
    additive_group_lemmas::lemma_neg_congruence::<T>(
        a_term.sub(b_term), b_term.sub(a_term).neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(b_term.sub(a_term));
    T::axiom_eqv_transitive(
        a_term.sub(b_term).neg(),
        b_term.sub(a_term).neg().neg(),
        b_term.sub(a_term),
    );
    T::axiom_add_congruence_left(
        a_term.sub(b_term).neg(), b_term.sub(a_term), c_term.neg(),
    );
    T::axiom_eqv_transitive(
        a_term.sub(b_term).add(c_term).neg(),
        a_term.sub(b_term).neg().add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    //  Need: (-A).sub(C).add(B) ≡ B.sub(A).add(C.neg())
    //  (-A).sub(C) ≡ (-A) + (-C) ≡ -(A) + -(C) which is (-A)+(-C)
    //  B.sub(A) + (-C) ≡ (B + (-A)) + (-C)
    //  (-A).sub(C).add(B) ≡ ((-A)+(-C)) + B
    //  We need: ((-A)+(-C))+B ≡ (B+(-A))+(-C)
    //  This is commutativity+associativity: x+y+z ≡ z+x+y where x=-A, y=-C, z=B

    //  Actually, let me use a simpler approach. Note that sub is add_neg:
    //  (-A).sub(C) = (-A) + (-C) [axiom_sub_is_add_neg]
    T::axiom_sub_is_add_neg(a_term.neg(), c_term);
    //  (-A).sub(C).add(B) = ((-A)+(-C))+B

    //  B.sub(A) = B + (-A) [axiom_sub_is_add_neg]
    T::axiom_sub_is_add_neg(b_term, a_term);
    //  B.sub(A) + (-C) = (B+(-A))+(-C)

    //  Need: ((-A)+(-C))+B ≡ (B+(-A))+(-C)
    //  = (-A + -C + B) ≡ (B + -A + -C)
    //  By commutativity of addition this should hold
    //  (-A)+(-C)+B = (-A)+((-C)+B) [assoc] = (-A)+(B+(-C)) [comm] = ((-A)+B)+(-C) [assoc]
    //  = (B+(-A))+(-C) [comm on first pair]

    //  Assoc: ((-A)+(-C))+B ≡ (-A)+((-C)+B)
    T::axiom_add_associative(a_term.neg(), c_term.neg(), b_term);

    //  Comm: (-C)+B ≡ B+(-C)
    T::axiom_add_commutative(c_term.neg(), b_term);

    //  Congr: (-A)+((-C)+B) ≡ (-A)+(B+(-C))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a_term.neg(), c_term.neg().add(b_term), b_term.add(c_term.neg()),
    );

    //  Chain: ((-A)+(-C))+B ≡ (-A)+((-C)+B) ≡ (-A)+(B+(-C))
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(c_term.neg().add(b_term)),
        a_term.neg().add(b_term.add(c_term.neg())),
    );

    //  Assoc back: (-A)+(B+(-C)) ≡ ((-A)+B)+(-C)
    T::axiom_add_associative(a_term.neg(), b_term, c_term.neg());
    T::axiom_eqv_symmetric(
        a_term.neg().add(b_term).add(c_term.neg()),
        a_term.neg().add(b_term.add(c_term.neg())),
    );

    //  Chain: (...)+B ≡ (-A)+(B+(-C)) ≡ ((-A)+B)+(-C)
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term.add(c_term.neg())),
        a_term.neg().add(b_term).add(c_term.neg()),
    );

    //  Comm: (-A)+B ≡ B+(-A)
    T::axiom_add_commutative(a_term.neg(), b_term);
    T::axiom_add_congruence_left(
        a_term.neg().add(b_term), b_term.add(a_term.neg()), c_term.neg(),
    );

    //  Chain: ((-A)+(-C))+B ≡ ((-A)+B)+(-C) ≡ (B+(-A))+(-C)
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term).add(c_term.neg()),
        b_term.add(a_term.neg()).add(c_term.neg()),
    );

    //  Now fold back using sub_is_add_neg: B+(-A) ≡ B.sub(A), and +(-C) stays
    T::axiom_eqv_symmetric(b_term.sub(a_term), b_term.add(a_term.neg()));
    T::axiom_add_congruence_left(
        b_term.add(a_term.neg()), b_term.sub(a_term), c_term.neg(),
    );
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        b_term.add(a_term.neg()).add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    //  Similarly fold (-A).sub(C) ≡ (-A)+(-C) [already established]
    T::axiom_eqv_symmetric(a_term.neg().sub(c_term), a_term.neg().add(c_term.neg()));
    T::axiom_add_congruence_left(
        a_term.neg().add(c_term.neg()), a_term.neg().sub(c_term), b_term,
    );
    T::axiom_eqv_symmetric(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().sub(c_term).add(b_term),
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(c_term).add(b_term),
        a_term.neg().add(c_term.neg()).add(b_term),
        b_term.sub(a_term).add(c_term.neg()),
    );

    //  Now: swapped ≡ (-A).sub(C).add(B) ≡ B.sub(A).add(C.neg()) ≡ -(original)
    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).neg(),
        b_term.sub(a_term).add(c_term.neg()),
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(c_term).add(b_term),
        b_term.sub(a_term).add(c_term.neg()),
        a_term.sub(b_term).add(c_term).neg(),
    );

    //  Final: swapped ≡ (-A).sub(C).add(B) ≡ -(original)
    T::axiom_eqv_transitive(
        pw.mul(det2d(r, q)).sub(rw.mul(det2d(p, q))).add(qw.mul(det2d(p, r))),
        a_term.neg().sub(c_term).add(b_term),
        a_term.sub(b_term).add(c_term).neg(),
    );
}

///  Swapping a and c negates the incircle determinant.
///  Derived from swap_ab ∘ swap_bc ∘ swap_ab = swap_ac and
///  three negations = one negation.
pub proof fn lemma_incircle2d_swap_ac<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(c, b, a, d).eqv(incircle2d(a, b, c, d).neg()),
{
    //  swap(b,c) on (a,b,c,d) gives -(a,b,c,d)
    lemma_incircle2d_swap_bc::<T>(a, b, c, d);
    //  incircle2d(a, c, b, d) ≡ -incircle2d(a, b, c, d)

    //  swap(a,b) on (a,c,b,d) gives -(a,c,b,d)
    lemma_incircle2d_swap_ab::<T>(a, c, b, d);
    //  incircle2d(c, a, b, d) ≡ -incircle2d(a, c, b, d)

    //  Chain: incircle2d(c,a,b,d) ≡ -(-incircle2d(a,b,c,d)) ≡ incircle2d(a,b,c,d)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        incircle2d(a, c, b, d), incircle2d(a, b, c, d).neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(incircle2d(a, b, c, d));
    T::axiom_eqv_transitive(
        incircle2d(c, a, b, d),
        incircle2d(a, c, b, d).neg(),
        incircle2d(a, b, c, d).neg().neg(),
    );
    T::axiom_eqv_transitive(
        incircle2d(c, a, b, d),
        incircle2d(a, b, c, d).neg().neg(),
        incircle2d(a, b, c, d),
    );
    //  So incircle2d(c, a, b, d) ≡ incircle2d(a, b, c, d) [double swap = identity]

    //  Now swap(a,b) on (c,a,b,d) gives -(c,a,b,d) = -(a,b,c,d)
    lemma_incircle2d_swap_ab::<T>(c, a, b, d);
    //  incircle2d(a, c, b, d)... wait, that gives us swap_ab on (c,a,b,d) → (a,c,b,d)
    //  That's not right. Let me redo this.

    //  Actually: swap(b,c) on (c,a,b,d) gives (c,b,a,d)
    lemma_incircle2d_swap_bc::<T>(c, a, b, d);
    //  incircle2d(c, b, a, d) ≡ -incircle2d(c, a, b, d)

    //  incircle2d(c, a, b, d) ≡ incircle2d(a, b, c, d) [proved above]
    //  So: incircle2d(c, b, a, d) ≡ -incircle2d(c, a, b, d) ≡ -incircle2d(a, b, c, d)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        incircle2d(c, a, b, d), incircle2d(a, b, c, d),
    );
    T::axiom_eqv_transitive(
        incircle2d(c, b, a, d),
        incircle2d(c, a, b, d).neg(),
        incircle2d(a, b, c, d).neg(),
    );
}

///  Cyclic permutation (a,b,c) → (b,c,a) preserves the incircle determinant.
///  Derived from swap_ab then swap_bc (two transpositions = even permutation).
pub proof fn lemma_incircle2d_cyclic_abc<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(b, c, a, d).eqv(incircle2d(a, b, c, d)),
{
    //  swap_ab: incircle2d(b, a, c, d) ≡ -incircle2d(a, b, c, d)
    lemma_incircle2d_swap_ab::<T>(a, b, c, d);

    //  swap_bc on (b, a, c, d): incircle2d(b, c, a, d) ≡ -incircle2d(b, a, c, d)
    lemma_incircle2d_swap_bc::<T>(b, a, c, d);

    //  Chain: incircle2d(b, c, a, d) ≡ -incircle2d(b, a, c, d) ≡ -(-incircle2d(a, b, c, d))
    additive_group_lemmas::lemma_neg_congruence::<T>(
        incircle2d(b, a, c, d), incircle2d(a, b, c, d).neg(),
    );
    T::axiom_eqv_transitive(
        incircle2d(b, c, a, d),
        incircle2d(b, a, c, d).neg(),
        incircle2d(a, b, c, d).neg().neg(),
    );

    //  Double negation: -(-x) ≡ x
    additive_group_lemmas::lemma_neg_involution::<T>(incircle2d(a, b, c, d));
    T::axiom_eqv_transitive(
        incircle2d(b, c, a, d),
        incircle2d(a, b, c, d).neg().neg(),
        incircle2d(a, b, c, d),
    );
}

///  Cyclic permutation (a,b,c) → (c,a,b) preserves the incircle determinant.
///  This is the inverse cyclic permutation (two applications of the forward cycle).
pub proof fn lemma_incircle2d_cyclic_cab<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(c, a, b, d).eqv(incircle2d(a, b, c, d)),
{
    //  (a,b,c) → (b,c,a) → (c,a,b)
    lemma_incircle2d_cyclic_abc::<T>(a, b, c, d);
    //  incircle2d(b, c, a, d) ≡ incircle2d(a, b, c, d)

    lemma_incircle2d_cyclic_abc::<T>(b, c, a, d);
    //  incircle2d(c, a, b, d) ≡ incircle2d(b, c, a, d)

    T::axiom_eqv_transitive(
        incircle2d(c, a, b, d),
        incircle2d(b, c, a, d),
        incircle2d(a, b, c, d),
    );
}

///  Incircle sign classification is preserved under cyclic permutation (a,b,c) → (b,c,a).
pub proof fn lemma_incircle2d_sign_cyclic_abc<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_sign(b, c, a, d) == incircle2d_sign(a, b, c, d),
{
    lemma_incircle2d_cyclic_abc::<T>(a, b, c, d);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        incircle2d(b, c, a, d), incircle2d(a, b, c, d),
    );
}

///  Incircle sign classification is preserved under cyclic permutation (a,b,c) → (c,a,b).
pub proof fn lemma_incircle2d_sign_cyclic_cab<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_sign(c, a, b, d) == incircle2d_sign(a, b, c, d),
{
    lemma_incircle2d_cyclic_cab::<T>(a, b, c, d);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        incircle2d(c, a, b, d), incircle2d(a, b, c, d),
    );
}

///  Swapping a and b reverses the incircle sign classification.
pub proof fn lemma_incircle2d_sign_swap_ab<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_sign(b, a, c, d) == match incircle2d_sign(a, b, c, d) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_incircle2d_swap_ab::<T>(a, b, c, d);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        incircle2d(b, a, c, d), incircle2d(a, b, c, d),
    );
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(b, a, c, d);
}

///  Swapping b and c reverses the incircle sign classification.
pub proof fn lemma_incircle2d_sign_swap_bc<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_sign(a, c, b, d) == match incircle2d_sign(a, b, c, d) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_incircle2d_swap_bc::<T>(a, b, c, d);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        incircle2d(a, c, b, d), incircle2d(a, b, c, d),
    );
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(a, c, b, d);
}

///  Swapping a and c reverses the incircle sign classification.
pub proof fn lemma_incircle2d_sign_swap_ac<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d_sign(c, b, a, d) == match incircle2d_sign(a, b, c, d) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_incircle2d_swap_ac::<T>(a, b, c, d);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        incircle2d(c, b, a, d), incircle2d(a, b, c, d),
    );
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(c, b, a, d);
}

//  =========================================================================
//  Lagrange identity and reference-point swap
//  =========================================================================

///  Helper: a*(b*c) ≡ b*(a*c) for Ring elements (swap first two factors).
proof fn lemma_mul_swap_first_two<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b.mul(c)).eqv(b.mul(a.mul(c))),
{
    T::axiom_mul_associative(a, b, c); //  (a*b)*c ≡ a*(b*c)
    T::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c))); //  flip: a*(b*c) ≡ (a*b)*c
    T::axiom_mul_commutative(a, b);
    T::axiom_mul_congruence_left(a.mul(b), b.mul(a), c);
    T::axiom_eqv_transitive(
        a.mul(b.mul(c)), a.mul(b).mul(c), b.mul(a).mul(c),
    );
    T::axiom_mul_associative(b, a, c);
    T::axiom_eqv_transitive(
        a.mul(b.mul(c)), b.mul(a).mul(c), b.mul(a.mul(c)),
    );
}

///  Helper: a*(b*c) ≡ c*(b*a) for Ring elements (reverse all three factors).
proof fn lemma_mul_reverse_three<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b.mul(c)).eqv(c.mul(b.mul(a))),
{
    //  a*(b*c) ≡ b*(a*c) [swap first two]
    lemma_mul_swap_first_two::<T>(a, b, c);
    //  b*(a*c) ≡ b*(c*a) [comm on inner]
    T::axiom_mul_commutative(a, c);
    ring_lemmas::lemma_mul_congruence_right::<T>(b, a.mul(c), c.mul(a));
    T::axiom_eqv_transitive(
        a.mul(b.mul(c)), b.mul(a.mul(c)), b.mul(c.mul(a)),
    );
    //  b*(c*a) ≡ c*(b*a) [swap first two again]
    lemma_mul_swap_first_two::<T>(b, c, a);
    T::axiom_eqv_transitive(
        a.mul(b.mul(c)), b.mul(c.mul(a)), c.mul(b.mul(a)),
    );
}

///  Helper: (a - c) - (b - c) ≡ a - b (cancel common right subtrahend).
proof fn lemma_sub_cancel_common_right<T: Ring>(a: T, b: T, c: T)
    ensures
        a.sub(c).sub(b.sub(c)).eqv(a.sub(b)),
{
    //  neg(b - c) ≡ c - b
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(b, c);
    additive_group_lemmas::lemma_neg_congruence::<T>(b.sub(c), c.sub(b).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(c.sub(b));
    T::axiom_eqv_transitive(b.sub(c).neg(), c.sub(b).neg().neg(), c.sub(b));
    //  (a-c) - (b-c) ≡ (a-c) + neg(b-c) ≡ (a-c) + (c-b)
    T::axiom_sub_is_add_neg(a.sub(c), b.sub(c));
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.sub(c), b.sub(c).neg(), c.sub(b));
    T::axiom_eqv_transitive(
        a.sub(c).sub(b.sub(c)), a.sub(c).add(b.sub(c).neg()), a.sub(c).add(c.sub(b)),
    );
    //  (a-c) + (c-b) ≡ a-b [telescoping]
    additive_group_lemmas::lemma_sub_add_sub::<T>(a, c, b);
    T::axiom_eqv_transitive(a.sub(c).sub(b.sub(c)), a.sub(c).add(c.sub(b)), a.sub(b));
}

///  Helper: (c - a) - (c - b) ≡ b - a (cancel common left subtrahend).
proof fn lemma_sub_cancel_common_left<T: Ring>(a: T, b: T, c: T)
    ensures
        c.sub(a).sub(c.sub(b)).eqv(b.sub(a)),
{
    //  neg(c - b) ≡ b - c
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(c, b);
    additive_group_lemmas::lemma_neg_congruence::<T>(c.sub(b), b.sub(c).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(b.sub(c));
    T::axiom_eqv_transitive(c.sub(b).neg(), b.sub(c).neg().neg(), b.sub(c));
    //  (c-a) - (c-b) ≡ (c-a) + (b-c)
    T::axiom_sub_is_add_neg(c.sub(a), c.sub(b));
    additive_group_lemmas::lemma_add_congruence_right::<T>(c.sub(a), c.sub(b).neg(), b.sub(c));
    T::axiom_eqv_transitive(
        c.sub(a).sub(c.sub(b)), c.sub(a).add(c.sub(b).neg()), c.sub(a).add(b.sub(c)),
    );
    //  Commute: (c-a) + (b-c) ≡ (b-c) + (c-a)
    T::axiom_add_commutative(c.sub(a), b.sub(c));
    T::axiom_eqv_transitive(
        c.sub(a).sub(c.sub(b)), c.sub(a).add(b.sub(c)), b.sub(c).add(c.sub(a)),
    );
    //  (b-c) + (c-a) ≡ b-a [telescoping]
    additive_group_lemmas::lemma_sub_add_sub::<T>(b, c, a);
    T::axiom_eqv_transitive(c.sub(a).sub(c.sub(b)), b.sub(c).add(c.sub(a)), b.sub(a));
}

///  Sub-identity for Lagrange: v.x * det2d(p, w) - w.x * det2d(p, v) ≡ p.x * det2d(v, w)
proof fn lemma_cross_column_x<T: Ring>(p: Vec2<T>, v: Vec2<T>, w: Vec2<T>)
    ensures
        v.x.mul(det2d(p, w)).sub(w.x.mul(det2d(p, v)))
            .eqv(p.x.mul(det2d(v, w))),
{
    let (px, py, vx, vy, wx, wy) = (p.x, p.y, v.x, v.y, w.x, w.y);
    //  Expand: vx * det2d(p,w) ≡ t1a - t1b
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(vx, px.mul(wy), py.mul(wx));
    let (t1a, t1b) = (vx.mul(px.mul(wy)), vx.mul(py.mul(wx)));
    //  Expand: wx * det2d(p,v) ≡ t2a - t2b
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(wx, px.mul(vy), py.mul(vx));
    let (t2a, t2b) = (wx.mul(px.mul(vy)), wx.mul(py.mul(vx)));
    //  Cross: t1b ≡ t2b [both ≡ py*vx*wx by rearrangement]
    lemma_mul_reverse_three::<T>(vx, py, wx);
    //  LHS ≡ (t1a - t1b) - (t2a - t2b) [sub_congruence from expansion]
    additive_group_lemmas::lemma_sub_congruence::<T>(
        vx.mul(det2d(p, w)), t1a.sub(t1b), wx.mul(det2d(p, v)), t2a.sub(t2b),
    );
    //  Replace t1b with t2b: (t1a - t1b) ≡ (t1a - t2b)
    T::axiom_eqv_reflexive(t1a);
    additive_group_lemmas::lemma_sub_congruence::<T>(t1a, t1a, t1b, t2b);
    T::axiom_eqv_reflexive(t2a.sub(t2b));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t1a.sub(t1b), t1a.sub(t2b), t2a.sub(t2b), t2a.sub(t2b),
    );
    T::axiom_eqv_transitive(
        vx.mul(det2d(p, w)).sub(wx.mul(det2d(p, v))),
        t1a.sub(t1b).sub(t2a.sub(t2b)), t1a.sub(t2b).sub(t2a.sub(t2b)),
    );
    //  (t1a - t2b) - (t2a - t2b) ≡ t1a - t2a [cancel common right]
    lemma_sub_cancel_common_right::<T>(t1a, t2a, t2b);
    T::axiom_eqv_transitive(
        vx.mul(det2d(p, w)).sub(wx.mul(det2d(p, v))),
        t1a.sub(t2b).sub(t2a.sub(t2b)), t1a.sub(t2a),
    );
    //  t1a ≡ px*(vx*wy), t2a ≡ px*(vy*wx)
    lemma_mul_swap_first_two::<T>(vx, px, wy);
    lemma_mul_swap_first_two::<T>(wx, px, vy);
    T::axiom_mul_commutative(wx, vy);
    ring_lemmas::lemma_mul_congruence_right::<T>(px, wx.mul(vy), vy.mul(wx));
    T::axiom_eqv_transitive(t2a, px.mul(wx.mul(vy)), px.mul(vy.mul(wx)));
    //  t1a - t2a ≡ px*(vx*wy) - px*(vy*wx) ≡ px*det2d(v,w)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t1a, px.mul(vx.mul(wy)), t2a, px.mul(vy.mul(wx)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(px, vx.mul(wy), vy.mul(wx));
    T::axiom_eqv_symmetric(px.mul(det2d(v, w)), px.mul(vx.mul(wy)).sub(px.mul(vy.mul(wx))));
    T::axiom_eqv_transitive(
        t1a.sub(t2a), px.mul(vx.mul(wy)).sub(px.mul(vy.mul(wx))), px.mul(det2d(v, w)),
    );
    //  Final chain
    T::axiom_eqv_transitive(
        vx.mul(det2d(p, w)).sub(wx.mul(det2d(p, v))), t1a.sub(t2a), px.mul(det2d(v, w)),
    );
}

///  Sub-identity for Lagrange: v.y * det2d(p, w) - w.y * det2d(p, v) ≡ p.y * det2d(v, w)
proof fn lemma_cross_column_y<T: Ring>(p: Vec2<T>, v: Vec2<T>, w: Vec2<T>)
    ensures
        v.y.mul(det2d(p, w)).sub(w.y.mul(det2d(p, v)))
            .eqv(p.y.mul(det2d(v, w))),
{
    let (px, py, vx, vy, wx, wy) = (p.x, p.y, v.x, v.y, w.x, w.y);
    //  Expand: vy * det2d(p,w) ≡ t1a - t1b
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(vy, px.mul(wy), py.mul(wx));
    let (t1a, t1b) = (vy.mul(px.mul(wy)), vy.mul(py.mul(wx)));
    //  Expand: wy * det2d(p,v) ≡ t2a - t2b
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(wy, px.mul(vy), py.mul(vx));
    let (t2a, t2b) = (wy.mul(px.mul(vy)), wy.mul(py.mul(vx)));
    //  Cross: t1a ≡ t2a [vy*(px*wy) ≡ wy*(px*vy)]
    lemma_mul_reverse_three::<T>(vy, px, wy);
    //  LHS ≡ (t1a - t1b) - (t2a - t2b)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        vy.mul(det2d(p, w)), t1a.sub(t1b), wy.mul(det2d(p, v)), t2a.sub(t2b),
    );
    //  Since t1a ≡ t2a: (t1a - t1b) ≡ (t2a - t1b)
    T::axiom_eqv_reflexive(t1b);
    additive_group_lemmas::lemma_sub_congruence::<T>(t1a, t2a, t1b, t1b);
    T::axiom_eqv_reflexive(t2a.sub(t2b));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t1a.sub(t1b), t2a.sub(t1b), t2a.sub(t2b), t2a.sub(t2b),
    );
    T::axiom_eqv_transitive(
        vy.mul(det2d(p, w)).sub(wy.mul(det2d(p, v))),
        t1a.sub(t1b).sub(t2a.sub(t2b)), t2a.sub(t1b).sub(t2a.sub(t2b)),
    );
    //  (t2a - t1b) - (t2a - t2b) ≡ t2b - t1b [cancel common left]
    lemma_sub_cancel_common_left::<T>(t1b, t2b, t2a);
    T::axiom_eqv_transitive(
        vy.mul(det2d(p, w)).sub(wy.mul(det2d(p, v))),
        t2a.sub(t1b).sub(t2a.sub(t2b)), t2b.sub(t1b),
    );
    //  t1b ≡ py*(vy*wx), t2b ≡ py*(vx*wy)
    lemma_mul_swap_first_two::<T>(vy, py, wx);
    lemma_mul_swap_first_two::<T>(wy, py, vx);
    T::axiom_mul_commutative(wy, vx);
    ring_lemmas::lemma_mul_congruence_right::<T>(py, wy.mul(vx), vx.mul(wy));
    T::axiom_eqv_transitive(t2b, py.mul(wy.mul(vx)), py.mul(vx.mul(wy)));
    //  t2b - t1b ≡ py*(vx*wy) - py*(vy*wx) ≡ py*det2d(v,w)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t2b, py.mul(vx.mul(wy)), t1b, py.mul(vy.mul(wx)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(py, vx.mul(wy), vy.mul(wx));
    T::axiom_eqv_symmetric(py.mul(det2d(v, w)), py.mul(vx.mul(wy)).sub(py.mul(vy.mul(wx))));
    T::axiom_eqv_transitive(
        t2b.sub(t1b), py.mul(vx.mul(wy)).sub(py.mul(vy.mul(wx))), py.mul(det2d(v, w)),
    );
    //  Final chain
    T::axiom_eqv_transitive(
        vy.mul(det2d(p, w)).sub(wy.mul(det2d(p, v))), t2b.sub(t1b), py.mul(det2d(v, w)),
    );
}

//  =========================================================================
//  Helper lemmas for reference-point swap (incircle2d_swap_ad)
//  =========================================================================

///  a - 0 ≡ a
pub proof fn lemma_sub_zero_right<T: Ring>(a: T)
    ensures a.sub(T::zero()).eqv(a)
{
    T::axiom_sub_is_add_neg(a, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero().neg()), a.add(T::zero()));
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero()), a);
}

///  lift(-v) ≡ lift(v): norm_sq is even
pub proof fn lemma_lift_neg_vec2<T: Ring>(v: Vec2<T>)
    ensures lift(v.neg()).eqv(lift(v))
{
    ring_lemmas::lemma_neg_mul_neg::<T>(v.x, v.x);
    ring_lemmas::lemma_neg_mul_neg::<T>(v.y, v.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        v.x.neg().mul(v.x.neg()), v.x.mul(v.x),
        v.y.neg().mul(v.y.neg()), v.y.mul(v.y),
    );
}

///  det2d(-p, v-p) ≡ -det2d(p, v)
pub proof fn lemma_det2d_neg_sub<T: Ring>(p: Vec2<T>, v: Vec2<T>)
    ensures det2d(p.neg(), v.sub(p)).eqv(det2d(p, v).neg())
{
    //  det2d(-p, v-p) ≡ -det2d(p, v-p)
    lemma_det2d_neg_left::<T>(p, v.sub(p));
    //  det2d(p, v-p) ≡ det2d(p,v) - det2d(p,p)
    lemma_det2d_sub_right::<T>(p, v, p);
    //  det2d(p,p) ≡ 0
    lemma_det2d_self_zero::<T>(p);
    //  det2d(p,v) - det2d(p,p) ≡ det2d(p,v) - 0
    T::axiom_eqv_reflexive(det2d(p, v));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(p, v), det2d(p, v), det2d(p, p), T::zero(),
    );
    //  det2d(p,v) - 0 ≡ det2d(p,v)
    lemma_sub_zero_right::<T>(det2d(p, v));
    //  Chain: det2d(p, v-p) ≡ det2d(p,v)
    T::axiom_eqv_transitive(
        det2d(p, v.sub(p)), det2d(p, v).sub(det2d(p, p)), det2d(p, v).sub(T::zero()),
    );
    T::axiom_eqv_transitive(det2d(p, v.sub(p)), det2d(p, v).sub(T::zero()), det2d(p, v));
    //  -det2d(p, v-p) ≡ -det2d(p, v)
    additive_group_lemmas::lemma_neg_congruence::<T>(det2d(p, v.sub(p)), det2d(p, v));
    //  Chain: det2d(-p, v-p) ≡ -det2d(p, v-p) ≡ -det2d(p, v)
    T::axiom_eqv_transitive(
        det2d(p.neg(), v.sub(p)), det2d(p, v.sub(p)).neg(), det2d(p, v).neg(),
    );
}

///  det2d(q-p, r-p) ≡ (det2d(q,r) - det2d(q,p)) - det2d(p,r)
pub proof fn lemma_det2d_sub_sub<T: Ring>(p: Vec2<T>, q: Vec2<T>, r: Vec2<T>)
    ensures det2d(q.sub(p), r.sub(p)).eqv(
        det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r))
    )
{
    //  det2d(q-p, r-p) ≡ det2d(q, r-p) - det2d(p, r-p)
    lemma_det2d_sub_left::<T>(q, p, r.sub(p));
    //  det2d(q, r-p) ≡ det2d(q,r) - det2d(q,p)
    lemma_det2d_sub_right::<T>(q, r, p);
    //  det2d(p, r-p) ≡ det2d(p,r)
    lemma_det2d_sub_right::<T>(p, r, p);
    lemma_det2d_self_zero::<T>(p);
    T::axiom_eqv_reflexive(det2d(p, r));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(p, r), det2d(p, r), det2d(p, p), T::zero(),
    );
    lemma_sub_zero_right::<T>(det2d(p, r));
    T::axiom_eqv_transitive(
        det2d(p, r.sub(p)), det2d(p, r).sub(det2d(p, p)), det2d(p, r).sub(T::zero()),
    );
    T::axiom_eqv_transitive(det2d(p, r.sub(p)), det2d(p, r).sub(T::zero()), det2d(p, r));
    //  Outer: det2d(q,r-p) - det2d(p,r-p) ≡ (det2d(q,r)-det2d(q,p)) - det2d(p,r)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(q, r.sub(p)), det2d(q, r).sub(det2d(q, p)),
        det2d(p, r.sub(p)), det2d(p, r),
    );
    T::axiom_eqv_transitive(
        det2d(q.sub(p), r.sub(p)),
        det2d(q, r.sub(p)).sub(det2d(p, r.sub(p))),
        det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r)),
    );
}

///  Lagrange 2D identity: lift(p)*det2d(q,r) ≡ dot(p,q)*det2d(p,r) - dot(p,r)*det2d(p,q)
pub proof fn lemma_lagrange_2d<T: Ring>(p: Vec2<T>, q: Vec2<T>, r: Vec2<T>)
    ensures lift(p).mul(det2d(q, r)).eqv(
        vec2_dot(p, q).mul(det2d(p, r)).sub(vec2_dot(p, r).mul(det2d(p, q)))
    )
{
    let px = p.x;
    let py = p.y;

    //  LHS = (px*px + py*py) * det2d(q,r) ≡ (px*px)*det2d(q,r) + (py*py)*det2d(q,r)
    ring_lemmas::lemma_mul_distributes_right::<T>(px.mul(px), py.mul(py), det2d(q, r));

    //  === X-part: (px*px)*det2d(q,r) ≡ (px*qx)*det2d(p,r) - (px*rx)*det2d(p,q) ===
    //  (px*px)*det2d(q,r) ≡ px*(px*det2d(q,r))
    T::axiom_mul_associative(px, px, det2d(q, r));
    //  column_x: qx*det2d(p,r) - rx*det2d(p,q) ≡ px*det2d(q,r) → reversed
    lemma_cross_column_x::<T>(p, q, r);
    T::axiom_eqv_symmetric(
        q.x.mul(det2d(p, r)).sub(r.x.mul(det2d(p, q))),
        p.x.mul(det2d(q, r)),
    );
    //  px*(px*det2d(q,r)) ≡ px*(qx*det2d(p,r) - rx*det2d(p,q))
    ring_lemmas::lemma_mul_congruence_right::<T>(
        px, px.mul(det2d(q, r)),
        q.x.mul(det2d(p, r)).sub(r.x.mul(det2d(p, q))),
    );
    T::axiom_eqv_transitive(
        px.mul(px).mul(det2d(q, r)),
        px.mul(px.mul(det2d(q, r))),
        px.mul(q.x.mul(det2d(p, r)).sub(r.x.mul(det2d(p, q)))),
    );
    //  px*(qx*det2d(p,r) - rx*det2d(p,q)) ≡ px*(qx*det2d(p,r)) - px*(rx*det2d(p,q))
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(
        px, q.x.mul(det2d(p, r)), r.x.mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        px.mul(px).mul(det2d(q, r)),
        px.mul(q.x.mul(det2d(p, r)).sub(r.x.mul(det2d(p, q)))),
        px.mul(q.x.mul(det2d(p, r))).sub(px.mul(r.x.mul(det2d(p, q)))),
    );
    //  Reassociate: px*(qx*det2d(p,r)) ≡ (px*qx)*det2d(p,r) etc.
    T::axiom_mul_associative(px, q.x, det2d(p, r));
    T::axiom_eqv_symmetric(
        px.mul(q.x).mul(det2d(p, r)), px.mul(q.x.mul(det2d(p, r))),
    );
    T::axiom_mul_associative(px, r.x, det2d(p, q));
    T::axiom_eqv_symmetric(
        px.mul(r.x).mul(det2d(p, q)), px.mul(r.x.mul(det2d(p, q))),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        px.mul(q.x.mul(det2d(p, r))), px.mul(q.x).mul(det2d(p, r)),
        px.mul(r.x.mul(det2d(p, q))), px.mul(r.x).mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        px.mul(px).mul(det2d(q, r)),
        px.mul(q.x.mul(det2d(p, r))).sub(px.mul(r.x.mul(det2d(p, q)))),
        px.mul(q.x).mul(det2d(p, r)).sub(px.mul(r.x).mul(det2d(p, q))),
    );

    //  === Y-part: (py*py)*det2d(q,r) ≡ (py*qy)*det2d(p,r) - (py*ry)*det2d(p,q) ===
    T::axiom_mul_associative(py, py, det2d(q, r));
    lemma_cross_column_y::<T>(p, q, r);
    T::axiom_eqv_symmetric(
        q.y.mul(det2d(p, r)).sub(r.y.mul(det2d(p, q))),
        p.y.mul(det2d(q, r)),
    );
    ring_lemmas::lemma_mul_congruence_right::<T>(
        py, py.mul(det2d(q, r)),
        q.y.mul(det2d(p, r)).sub(r.y.mul(det2d(p, q))),
    );
    T::axiom_eqv_transitive(
        py.mul(py).mul(det2d(q, r)),
        py.mul(py.mul(det2d(q, r))),
        py.mul(q.y.mul(det2d(p, r)).sub(r.y.mul(det2d(p, q)))),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(
        py, q.y.mul(det2d(p, r)), r.y.mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        py.mul(py).mul(det2d(q, r)),
        py.mul(q.y.mul(det2d(p, r)).sub(r.y.mul(det2d(p, q)))),
        py.mul(q.y.mul(det2d(p, r))).sub(py.mul(r.y.mul(det2d(p, q)))),
    );
    T::axiom_mul_associative(py, q.y, det2d(p, r));
    T::axiom_eqv_symmetric(
        py.mul(q.y).mul(det2d(p, r)), py.mul(q.y.mul(det2d(p, r))),
    );
    T::axiom_mul_associative(py, r.y, det2d(p, q));
    T::axiom_eqv_symmetric(
        py.mul(r.y).mul(det2d(p, q)), py.mul(r.y.mul(det2d(p, q))),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        py.mul(q.y.mul(det2d(p, r))), py.mul(q.y).mul(det2d(p, r)),
        py.mul(r.y.mul(det2d(p, q))), py.mul(r.y).mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        py.mul(py).mul(det2d(q, r)),
        py.mul(q.y.mul(det2d(p, r))).sub(py.mul(r.y.mul(det2d(p, q)))),
        py.mul(q.y).mul(det2d(p, r)).sub(py.mul(r.y).mul(det2d(p, q))),
    );

    //  === Combine x+y parts ===
    additive_group_lemmas::lemma_add_congruence::<T>(
        px.mul(px).mul(det2d(q, r)),
        px.mul(q.x).mul(det2d(p, r)).sub(px.mul(r.x).mul(det2d(p, q))),
        py.mul(py).mul(det2d(q, r)),
        py.mul(q.y).mul(det2d(p, r)).sub(py.mul(r.y).mul(det2d(p, q))),
    );
    T::axiom_eqv_transitive(
        lift(p).mul(det2d(q, r)),
        px.mul(px).mul(det2d(q, r)).add(py.mul(py).mul(det2d(q, r))),
        px.mul(q.x).mul(det2d(p, r)).sub(px.mul(r.x).mul(det2d(p, q))).add(
            py.mul(q.y).mul(det2d(p, r)).sub(py.mul(r.y).mul(det2d(p, q)))
        ),
    );

    //  === Rearrange: (A-B) + (C-D) ≡ (A+C) - (B+D) ===
    //  sub_add_rearrange(A,C,B,D) gives (A+C)-(B+D) ≡ (A-B)+(C-D), then symmetric
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(
        px.mul(q.x).mul(det2d(p, r)),
        py.mul(q.y).mul(det2d(p, r)),
        px.mul(r.x).mul(det2d(p, q)),
        py.mul(r.y).mul(det2d(p, q)),
    );
    T::axiom_eqv_symmetric(
        px.mul(q.x).mul(det2d(p, r)).add(py.mul(q.y).mul(det2d(p, r))).sub(
            px.mul(r.x).mul(det2d(p, q)).add(py.mul(r.y).mul(det2d(p, q)))
        ),
        px.mul(q.x).mul(det2d(p, r)).sub(px.mul(r.x).mul(det2d(p, q))).add(
            py.mul(q.y).mul(det2d(p, r)).sub(py.mul(r.y).mul(det2d(p, q)))
        ),
    );
    T::axiom_eqv_transitive(
        lift(p).mul(det2d(q, r)),
        px.mul(q.x).mul(det2d(p, r)).sub(px.mul(r.x).mul(det2d(p, q))).add(
            py.mul(q.y).mul(det2d(p, r)).sub(py.mul(r.y).mul(det2d(p, q)))
        ),
        px.mul(q.x).mul(det2d(p, r)).add(py.mul(q.y).mul(det2d(p, r))).sub(
            px.mul(r.x).mul(det2d(p, q)).add(py.mul(r.y).mul(det2d(p, q)))
        ),
    );

    //  === Factor back: (px*qx)*det2d(p,r) + (py*qy)*det2d(p,r) ≡ dot(p,q)*det2d(p,r) ===
    ring_lemmas::lemma_mul_distributes_right::<T>(
        px.mul(q.x), py.mul(q.y), det2d(p, r),
    );
    T::axiom_eqv_symmetric(
        px.mul(q.x).add(py.mul(q.y)).mul(det2d(p, r)),
        px.mul(q.x).mul(det2d(p, r)).add(py.mul(q.y).mul(det2d(p, r))),
    );
    //  === Factor back: (px*rx)*det2d(p,q) + (py*ry)*det2d(p,q) ≡ dot(p,r)*det2d(p,q) ===
    ring_lemmas::lemma_mul_distributes_right::<T>(
        px.mul(r.x), py.mul(r.y), det2d(p, q),
    );
    T::axiom_eqv_symmetric(
        px.mul(r.x).add(py.mul(r.y)).mul(det2d(p, q)),
        px.mul(r.x).mul(det2d(p, q)).add(py.mul(r.y).mul(det2d(p, q))),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        px.mul(q.x).mul(det2d(p, r)).add(py.mul(q.y).mul(det2d(p, r))),
        vec2_dot(p, q).mul(det2d(p, r)),
        px.mul(r.x).mul(det2d(p, q)).add(py.mul(r.y).mul(det2d(p, q))),
        vec2_dot(p, r).mul(det2d(p, q)),
    );
    T::axiom_eqv_transitive(
        lift(p).mul(det2d(q, r)),
        px.mul(q.x).mul(det2d(p, r)).add(py.mul(q.y).mul(det2d(p, r))).sub(
            px.mul(r.x).mul(det2d(p, q)).add(py.mul(r.y).mul(det2d(p, q)))
        ),
        vec2_dot(p, q).mul(det2d(p, r)).sub(vec2_dot(p, r).mul(det2d(p, q))),
    );
}

///  Helper: a.sub(b.neg()) ≡ a.add(b)
pub proof fn lemma_sub_neg_is_add<T: Ring>(a: T, b: T)
    ensures a.sub(b.neg()).eqv(a.add(b))
{
    T::axiom_sub_is_add_neg(a, b.neg());
    additive_group_lemmas::lemma_neg_involution::<T>(b);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.neg().neg(), b);
    T::axiom_eqv_transitive(a.sub(b.neg()), a.add(b.neg().neg()), a.add(b));
}

///  Helper: a.add(b.neg()) ≡ a.sub(b)
proof fn lemma_add_neg_is_sub<T: Ring>(a: T, b: T)
    ensures a.add(b.neg()).eqv(a.sub(b))
{
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
}

///  Swap reference point: incircle2d(d,b,c,a) ≡ -incircle2d(a,b,c,d)
pub proof fn lemma_incircle2d_swap_ad<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(d, b, c, a).eqv(incircle2d(a, b, c, d).neg()),
{
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);

    //  === Phase 1: Rebase sub2 vectors ===
    lemma_sub2_antisymmetric::<T>(d, a);
    //  sub2(d,a) ≡ sub2(a,d).neg() = p.neg()
    lemma_sub2_rebase::<T>(b, a, d);
    //  sub2(b,a) ≡ sub2(b,d).sub(sub2(a,d)) = q.sub(p)
    lemma_sub2_rebase::<T>(c, a, d);
    //  sub2(c,a) ≡ sub2(c,d).sub(sub2(a,d)) = r.sub(p)

    //  === Phase 2: Simplify lift and det2d of rebased vectors ===
    //  lift(sub2(d,a)) ≡ lift(p)
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(d, a), p.neg());
    lemma_lift_neg_vec2::<T>(p);
    T::axiom_eqv_transitive(lift(sub2(d, a)), lift(p.neg()), lift(p));

    //  det2d(sub2(b,a), sub2(c,a)) ≡ det2d(q,r) - det2d(q,p) - det2d(p,r)
    lemma_det2d_congruence::<T>(sub2(b, a), q.sub(p), sub2(c, a), r.sub(p));
    lemma_det2d_sub_sub::<T>(p, q, r);
    T::axiom_eqv_transitive(
        det2d(sub2(b, a), sub2(c, a)),
        det2d(q.sub(p), r.sub(p)),
        det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r)),
    );

    //  det2d(sub2(d,a), sub2(c,a)) ≡ -det2d(p,r)
    lemma_det2d_congruence::<T>(sub2(d, a), p.neg(), sub2(c, a), r.sub(p));
    lemma_det2d_neg_sub::<T>(p, r);
    T::axiom_eqv_transitive(
        det2d(sub2(d, a), sub2(c, a)),
        det2d(p.neg(), r.sub(p)),
        det2d(p, r).neg(),
    );

    //  det2d(sub2(d,a), sub2(b,a)) ≡ -det2d(p,q)
    lemma_det2d_congruence::<T>(sub2(d, a), p.neg(), sub2(b, a), q.sub(p));
    lemma_det2d_neg_sub::<T>(p, q);
    T::axiom_eqv_transitive(
        det2d(sub2(d, a), sub2(b, a)),
        det2d(p.neg(), q.sub(p)),
        det2d(p, q).neg(),
    );

    //  lift(sub2(b,a)) ≡ lift(q.sub(p)) = norm_sq(q-p)
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(b, a), q.sub(p));

    //  lift(sub2(c,a)) ≡ lift(r.sub(p)) = norm_sq(r-p)
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(c, a), r.sub(p));

    //  === Phase 3: Build the three terms ===
    //  Let D = det2d(q,r) - det2d(q,p) - det2d(p,r)
    let big_d = det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r));

    //  Term1: lift(sub2(d,a)) * det2d(sub2(b,a), sub2(c,a)) ≡ lift(p) * D
    ring_lemmas::lemma_mul_congruence_right::<T>(
        lift(sub2(d, a)), det2d(sub2(b, a), sub2(c, a)), big_d,
    );
    T::axiom_mul_congruence_left(lift(sub2(d, a)), lift(p), big_d);
    T::axiom_eqv_transitive(
        lift(sub2(d, a)).mul(det2d(sub2(b, a), sub2(c, a))),
        lift(sub2(d, a)).mul(big_d),
        lift(p).mul(big_d),
    );

    //  Term2: lift(sub2(b,a)) * det2d(sub2(d,a), sub2(c,a)) ≡ lift(q-p) * (-det2d(p,r))
    ring_lemmas::lemma_mul_congruence_right::<T>(
        lift(sub2(b, a)), det2d(sub2(d, a), sub2(c, a)), det2d(p, r).neg(),
    );
    T::axiom_mul_congruence_left(
        lift(sub2(b, a)), lift(q.sub(p)), det2d(p, r).neg(),
    );
    T::axiom_eqv_transitive(
        lift(sub2(b, a)).mul(det2d(sub2(d, a), sub2(c, a))),
        lift(sub2(b, a)).mul(det2d(p, r).neg()),
        lift(q.sub(p)).mul(det2d(p, r).neg()),
    );
    //  lift(q-p) * (-det2d(p,r)) ≡ -(lift(q-p) * det2d(p,r))
    ring_lemmas::lemma_mul_neg_right::<T>(lift(q.sub(p)), det2d(p, r));
    T::axiom_eqv_transitive(
        lift(sub2(b, a)).mul(det2d(sub2(d, a), sub2(c, a))),
        lift(q.sub(p)).mul(det2d(p, r).neg()),
        lift(q.sub(p)).mul(det2d(p, r)).neg(),
    );

    //  Term3: lift(sub2(c,a)) * det2d(sub2(d,a), sub2(b,a)) ≡ -(lift(r-p) * det2d(p,q))
    ring_lemmas::lemma_mul_congruence_right::<T>(
        lift(sub2(c, a)), det2d(sub2(d, a), sub2(b, a)), det2d(p, q).neg(),
    );
    T::axiom_mul_congruence_left(
        lift(sub2(c, a)), lift(r.sub(p)), det2d(p, q).neg(),
    );
    T::axiom_eqv_transitive(
        lift(sub2(c, a)).mul(det2d(sub2(d, a), sub2(b, a))),
        lift(sub2(c, a)).mul(det2d(p, q).neg()),
        lift(r.sub(p)).mul(det2d(p, q).neg()),
    );
    ring_lemmas::lemma_mul_neg_right::<T>(lift(r.sub(p)), det2d(p, q));
    T::axiom_eqv_transitive(
        lift(sub2(c, a)).mul(det2d(sub2(d, a), sub2(b, a))),
        lift(r.sub(p)).mul(det2d(p, q).neg()),
        lift(r.sub(p)).mul(det2d(p, q)).neg(),
    );

    //  === Phase 4: Assemble incircle2d(d,b,c,a) ≡ lift(p)*D + lift(q-p)*dpr - lift(r-p)*dpq ===
    //  incircle2d(d,b,c,a) = Term1.sub(Term2).add(Term3)
    //  ≡ (lift(p)*D).sub(-(lift(q-p)*dpr)).add(-(lift(r-p)*dpq))
    //  First: sub congruence on (Term1, Term2)
    let t1_orig = lift(sub2(d, a)).mul(det2d(sub2(b, a), sub2(c, a)));
    let t2_orig = lift(sub2(b, a)).mul(det2d(sub2(d, a), sub2(c, a)));
    let t3_orig = lift(sub2(c, a)).mul(det2d(sub2(d, a), sub2(b, a)));
    let t1_simp = lift(p).mul(big_d);
    let t2_simp = lift(q.sub(p)).mul(det2d(p, r)).neg();
    let t3_simp = lift(r.sub(p)).mul(det2d(p, q)).neg();

    additive_group_lemmas::lemma_sub_congruence::<T>(t1_orig, t1_simp, t2_orig, t2_simp);
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1_orig.sub(t2_orig), t1_simp.sub(t2_simp), t3_orig, t3_simp,
    );
    //  incircle2d(d,b,c,a) ≡ t1_simp.sub(t2_simp).add(t3_simp)

    //  sub(-x) ≡ add(x): t1_simp.sub(t2_simp) ≡ t1_simp + lift(q-p)*dpr
    lemma_sub_neg_is_add::<T>(t1_simp, lift(q.sub(p)).mul(det2d(p, r)));
    //  add(-x) ≡ sub(x): (...).add(t3_simp) ≡ (...) - lift(r-p)*dpq
    let mid = t1_simp.add(lift(q.sub(p)).mul(det2d(p, r)));
    lemma_add_neg_is_sub::<T>(mid, lift(r.sub(p)).mul(det2d(p, q)));

    //  Chain: incircle2d(d,b,c,a)
    //  ≡ t1_simp.sub(t2_simp).add(t3_simp)
    //  ≡ (t1_simp + lift(q-p)*dpr).add(t3_simp)
    T::axiom_eqv_reflexive(t3_simp);
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1_simp.sub(t2_simp), t1_simp.add(lift(q.sub(p)).mul(det2d(p, r))),
        t3_simp, t3_simp,
    );
    T::axiom_eqv_transitive(
        t1_simp.sub(t2_simp).add(t3_simp),
        t1_simp.add(lift(q.sub(p)).mul(det2d(p, r))).add(t3_simp),
        mid.sub(lift(r.sub(p)).mul(det2d(p, q))),
    );

    //  Now: incircle2d(d,b,c,a) ≡ lift(p)*D + lift(q-p)*dpr - lift(r-p)*dpq

    //  === Phase 5: Show this equals -incircle2d(a,b,c,d) ===
    //  incircle2d(a,b,c,d) = lift(p)*det2d(q,r) - lift(q)*det2d(p,r) + lift(r)*det2d(p,q)
    //  -incircle2d(a,b,c,d) = -lift(p)*det2d(q,r) + lift(q)*det2d(p,r) - lift(r)*det2d(p,q)
    //
    //  We need: lift(p)*D + lift(q-p)*dpr - lift(r-p)*dpq ≡ -incircle2d(a,b,c,d)
    //
    //  Strategy: Use Lagrange to replace lift(p)*det2d(q,r) in the expansion of lift(p)*D,
    //  then use norm_sq_sub_expand to simplify coefficients.
    //  This is done in a separate helper.
    lemma_incircle2d_swap_ad_algebra::<T>(p, q, r);

    //  Chain everything
    T::axiom_eqv_transitive(
        incircle2d(d, b, c, a),
        t1_simp.sub(t2_simp).add(t3_simp),
        mid.sub(lift(r.sub(p)).mul(det2d(p, q))),
    );
    T::axiom_eqv_transitive(
        incircle2d(d, b, c, a),
        mid.sub(lift(r.sub(p)).mul(det2d(p, q))),
        incircle2d(a, b, c, d).neg(),
    );
}

///  Helper: -(a - b) ≡ b - a
proof fn lemma_neg_sub<T: Ring>(a: T, b: T)
    ensures a.sub(b).neg().eqv(b.sub(a))
{
    T::axiom_sub_is_add_neg(a, b);
    additive_group_lemmas::lemma_neg_add::<T>(a, b.neg());
    //  -(a+(-b)) ≡ (-a)+(-(-b))
    additive_group_lemmas::lemma_neg_involution::<T>(b);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    //  (-a)+(-(-b)) ≡ (-a)+b
    T::axiom_eqv_transitive(a.add(b.neg()).neg(), a.neg().add(b.neg().neg()), a.neg().add(b));
    //  neg congruence from sub to add
    additive_group_lemmas::lemma_neg_congruence::<T>(a.sub(b), a.add(b.neg()));
    T::axiom_eqv_transitive(a.sub(b).neg(), a.add(b.neg()).neg(), a.neg().add(b));
    //  (-a)+b ≡ b+(-a) ≡ b-a
    T::axiom_add_commutative(a.neg(), b);
    T::axiom_sub_is_add_neg(b, a);
    T::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
    T::axiom_eqv_transitive(a.neg().add(b), b.add(a.neg()), b.sub(a));
    T::axiom_eqv_transitive(a.sub(b).neg(), a.neg().add(b), b.sub(a));
}

///  Helper: two() * a ≡ a + a
proof fn lemma_two_is_add<T: Ring>(a: T)
    ensures verus_algebra::convex::two::<T>().mul(a).eqv(a.add(a))
{
    ring_lemmas::lemma_mul_distributes_right::<T>(T::one(), T::one(), a);
    ring_lemmas::lemma_mul_one_left::<T>(a);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(a), a, T::one().mul(a), a,
    );
    T::axiom_eqv_transitive(
        verus_algebra::convex::two::<T>().mul(a),
        T::one().mul(a).add(T::one().mul(a)),
        a.add(a),
    );
}

///  dpr coefficient cancel: (dp_q - lp) + ((lq - d) + lp) ≡ lq - dp_q
///  when d ≡ dp_q + dp_q
proof fn lemma_dpr_coeff_cancel<T: Ring>(dp_q: T, lp: T, lq: T, d: T)
    requires d.eqv(dp_q.add(dp_q))
    ensures dp_q.sub(lp).add(lq.sub(d).add(lp)).eqv(lq.sub(dp_q))
{
    //  Commute inner: (lq-d)+lp ≡ lp+(lq-d)
    T::axiom_add_commutative(lq.sub(d), lp);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dp_q.sub(lp), lq.sub(d).add(lp), lp.add(lq.sub(d)),
    );
    //  Assoc reverse: (dp_q-lp)+(lp+(lq-d)) → ((dp_q-lp)+lp)+(lq-d)
    T::axiom_add_associative(dp_q.sub(lp), lp, lq.sub(d));
    T::axiom_eqv_symmetric(
        dp_q.sub(lp).add(lp).add(lq.sub(d)),
        dp_q.sub(lp).add(lp.add(lq.sub(d))),
    );
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.sub(lp).add(lp.add(lq.sub(d))),
        dp_q.sub(lp).add(lp).add(lq.sub(d)),
    );
    //  Cancel: (dp_q-lp)+lp ≡ dp_q
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(dp_q, lp);
    T::axiom_eqv_reflexive(lq.sub(d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        dp_q.sub(lp).add(lp), dp_q, lq.sub(d), lq.sub(d),
    );
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.sub(lp).add(lp).add(lq.sub(d)),
        dp_q.add(lq.sub(d)),
    );
    //  Substitute d ≡ dp_q+dp_q
    T::axiom_eqv_reflexive(lq);
    additive_group_lemmas::lemma_sub_congruence::<T>(lq, lq, d, dp_q.add(dp_q));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dp_q, lq.sub(d), lq.sub(dp_q.add(dp_q)),
    );
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.add(lq.sub(d)),
        dp_q.add(lq.sub(dp_q.add(dp_q))),
    );
    //  Convert dp_q+(lq-(dp_q+dp_q)) to (dp_q+lq)-(dp_q+dp_q)
    crate::triangle_intersection::lemma_add_sub_rearrange::<T>(
        dp_q, lq, dp_q.add(dp_q),
    );
    crate::segment_distance::lemma_add_sub_rearrange::<T>(
        dp_q, lq, dp_q.add(dp_q),
    );
    T::axiom_eqv_symmetric(
        dp_q.add(lq).sub(dp_q.add(dp_q)),
        dp_q.sub(dp_q.add(dp_q)).add(lq),
    );
    T::axiom_eqv_transitive(
        dp_q.add(lq.sub(dp_q.add(dp_q))),
        dp_q.sub(dp_q.add(dp_q)).add(lq),
        dp_q.add(lq).sub(dp_q.add(dp_q)),
    );
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.add(lq.sub(dp_q.add(dp_q))),
        dp_q.add(lq).sub(dp_q.add(dp_q)),
    );
    //  sub_add_rearrange: (dp_q+lq)-(dp_q+dp_q) ≡ (dp_q-dp_q)+(lq-dp_q)
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(dp_q, lq, dp_q, dp_q);
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.add(lq).sub(dp_q.add(dp_q)),
        dp_q.sub(dp_q).add(lq.sub(dp_q)),
    );
    //  sub_self + add_zero_left
    additive_group_lemmas::lemma_sub_self::<T>(dp_q);
    T::axiom_eqv_reflexive(lq.sub(dp_q));
    additive_group_lemmas::lemma_add_congruence::<T>(
        dp_q.sub(dp_q), T::zero(), lq.sub(dp_q), lq.sub(dp_q),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(lq.sub(dp_q));
    T::axiom_eqv_transitive(
        dp_q.sub(dp_q).add(lq.sub(dp_q)),
        T::zero().add(lq.sub(dp_q)),
        lq.sub(dp_q),
    );
    T::axiom_eqv_transitive(
        dp_q.sub(lp).add(lq.sub(d).add(lp)),
        dp_q.sub(dp_q).add(lq.sub(dp_q)),
        lq.sub(dp_q),
    );
}

///  dpq coefficient cancel: (lp - dp_r) - ((lr - d) + lp) ≡ dp_r - lr
///  when d ≡ dp_r + dp_r
proof fn lemma_dpq_coeff_cancel<T: Ring>(lp: T, dp_r: T, lr: T, d: T)
    requires d.eqv(dp_r.add(dp_r))
    ensures lp.sub(dp_r).sub(lr.sub(d).add(lp)).eqv(dp_r.sub(lr))
{
    //  Step A: Commute subtrahend + convert to add forms
    T::axiom_add_commutative(lr.sub(d), lp);
    T::axiom_sub_is_add_neg(lp, dp_r);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        lp.sub(dp_r), lp.add(dp_r.neg()),
        lr.sub(d).add(lp), lp.add(lr.sub(d)),
    );
    //  (lp-dp_r)-((lr-d)+lp) ≡ (lp+(-dp_r))-(lp+(lr-d))

    //  Step B: sub_add_rearrange: (a+b)-(c+d) ≡ (a-c)+(b-d)
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(
        lp, dp_r.neg(), lp, lr.sub(d),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        lp.add(dp_r.neg()).sub(lp.add(lr.sub(d))),
        lp.sub(lp).add(dp_r.neg().sub(lr.sub(d))),
    );

    //  Step C: lp-lp ≡ 0, simplify to (-dp_r)-(lr-d)
    additive_group_lemmas::lemma_sub_self::<T>(lp);
    T::axiom_eqv_reflexive(dp_r.neg().sub(lr.sub(d)));
    additive_group_lemmas::lemma_add_congruence::<T>(
        lp.sub(lp), T::zero(),
        dp_r.neg().sub(lr.sub(d)), dp_r.neg().sub(lr.sub(d)),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(dp_r.neg().sub(lr.sub(d)));
    T::axiom_eqv_transitive(
        lp.sub(lp).add(dp_r.neg().sub(lr.sub(d))),
        T::zero().add(dp_r.neg().sub(lr.sub(d))),
        dp_r.neg().sub(lr.sub(d)),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        lp.sub(lp).add(dp_r.neg().sub(lr.sub(d))),
        dp_r.neg().sub(lr.sub(d)),
    );
    //  original ≡ (-dp_r)-(lr-d)

    //  Step D: (-dp_r)-(lr-d) ≡ (-dp_r)+(d-lr)
    T::axiom_sub_is_add_neg(dp_r.neg(), lr.sub(d));
    lemma_neg_sub::<T>(lr, d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dp_r.neg(), lr.sub(d).neg(), d.sub(lr),
    );
    T::axiom_eqv_transitive(
        dp_r.neg().sub(lr.sub(d)),
        dp_r.neg().add(lr.sub(d).neg()),
        dp_r.neg().add(d.sub(lr)),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        dp_r.neg().sub(lr.sub(d)),
        dp_r.neg().add(d.sub(lr)),
    );
    //  original ≡ (-dp_r)+(d-lr)

    //  Step E: Substitute d ≡ dp_r+dp_r
    T::axiom_eqv_reflexive(lr);
    additive_group_lemmas::lemma_sub_congruence::<T>(d, dp_r.add(dp_r), lr, lr);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dp_r.neg(), d.sub(lr), dp_r.add(dp_r).sub(lr),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        dp_r.neg().add(d.sub(lr)),
        dp_r.neg().add(dp_r.add(dp_r).sub(lr)),
    );
    //  original ≡ (-dp_r)+((dp_r+dp_r)-lr)

    //  Step F: Convert to add form and use assoc
    T::axiom_sub_is_add_neg(dp_r.add(dp_r), lr);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dp_r.neg(),
        dp_r.add(dp_r).sub(lr),
        dp_r.add(dp_r).add(lr.neg()),
    );
    T::axiom_add_associative(dp_r.neg(), dp_r.add(dp_r), lr.neg());
    T::axiom_eqv_symmetric(
        dp_r.neg().add(dp_r.add(dp_r)).add(lr.neg()),
        dp_r.neg().add(dp_r.add(dp_r).add(lr.neg())),
    );
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r.add(dp_r).sub(lr)),
        dp_r.neg().add(dp_r.add(dp_r).add(lr.neg())),
        dp_r.neg().add(dp_r.add(dp_r)).add(lr.neg()),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        dp_r.neg().add(dp_r.add(dp_r).sub(lr)),
        dp_r.neg().add(dp_r.add(dp_r)).add(lr.neg()),
    );
    //  original ≡ ((-dp_r)+(dp_r+dp_r))+(-lr)

    //  Step G: (-dp_r)+(dp_r+dp_r) ≡ dp_r
    T::axiom_add_associative(dp_r.neg(), dp_r, dp_r);
    T::axiom_eqv_symmetric(
        dp_r.neg().add(dp_r).add(dp_r),
        dp_r.neg().add(dp_r.add(dp_r)),
    );
    //  (-dp_r)+(dp_r+dp_r) ≡ ((-dp_r)+dp_r)+dp_r
    T::axiom_add_commutative(dp_r.neg(), dp_r);
    lemma_add_neg_is_sub::<T>(dp_r, dp_r);
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r), dp_r.add(dp_r.neg()), dp_r.sub(dp_r),
    );
    additive_group_lemmas::lemma_sub_self::<T>(dp_r);
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r), dp_r.sub(dp_r), T::zero(),
    );
    //  (-dp_r)+dp_r ≡ 0
    T::axiom_eqv_reflexive(dp_r);
    additive_group_lemmas::lemma_add_congruence::<T>(
        dp_r.neg().add(dp_r), T::zero(), dp_r, dp_r,
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(dp_r);
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r).add(dp_r), T::zero().add(dp_r), dp_r,
    );
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r.add(dp_r)),
        dp_r.neg().add(dp_r).add(dp_r),
        dp_r,
    );
    //  (-dp_r)+(dp_r+dp_r) ≡ dp_r

    //  Step H: dp_r+(-lr) ≡ dp_r-lr
    T::axiom_eqv_reflexive(lr.neg());
    additive_group_lemmas::lemma_add_congruence::<T>(
        dp_r.neg().add(dp_r.add(dp_r)), dp_r, lr.neg(), lr.neg(),
    );
    //  ((-dp_r)+(dp_r+dp_r))+(-lr) ≡ dp_r+(-lr)
    lemma_add_neg_is_sub::<T>(dp_r, lr);
    T::axiom_eqv_transitive(
        dp_r.neg().add(dp_r.add(dp_r)).add(lr.neg()),
        dp_r.add(lr.neg()),
        dp_r.sub(lr),
    );
    T::axiom_eqv_transitive(
        lp.sub(dp_r).sub(lr.sub(d).add(lp)),
        dp_r.neg().add(dp_r.add(dp_r)).add(lr.neg()),
        dp_r.sub(lr),
    );
}

///  RHS form: -(lift(p)*dqr - lift(q)*dpr + lift(r)*dpq) ≡ (lq - dot(p,q))*dpr + (dot(p,r) - lr)*dpq
///
///  Uses Lagrange to replace lift(p)*dqr, then negates.
proof fn lemma_swap_ad_rhs_form<T: Ring>(p: Vec2<T>, q: Vec2<T>, r: Vec2<T>)
    ensures
        lift(p).mul(det2d(q, r))
            .sub(lift(q).mul(det2d(p, r)))
            .add(lift(r).mul(det2d(p, q)))
            .neg()
            .eqv(
                lift(q).sub(vec2_dot(p, q)).mul(det2d(p, r))
                    .add(vec2_dot(p, r).sub(lift(r)).mul(det2d(p, q)))
            ),
{
    let lp = lift(p);
    let lq = lift(q);
    let lr = lift(r);
    let dqr = det2d(q, r);
    let dpr = det2d(p, r);
    let dpq = det2d(p, q);
    let dp_q = vec2_dot(p, q);
    let dp_r = vec2_dot(p, r);

    //  Step 1: Lagrange: lp*dqr ≡ dp_q*dpr - dp_r*dpq
    lemma_lagrange_2d::<T>(p, q, r);
    //  lift(p)*dqr ≡ dp_q*dpr - dp_r*dpq

    //  Step 2: Substitute into incircle: lp*dqr - lq*dpr + lr*dpq
    //  ≡ (dp_q*dpr - dp_r*dpq) - lq*dpr + lr*dpq
    T::axiom_eqv_reflexive(lq.mul(dpr));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        lp.mul(dqr), dp_q.mul(dpr).sub(dp_r.mul(dpq)),
        lq.mul(dpr), lq.mul(dpr),
    );
    T::axiom_eqv_reflexive(lr.mul(dpq));
    additive_group_lemmas::lemma_add_congruence::<T>(
        lp.mul(dqr).sub(lq.mul(dpr)),
        dp_q.mul(dpr).sub(dp_r.mul(dpq)).sub(lq.mul(dpr)),
        lr.mul(dpq), lr.mul(dpq),
    );
    //  incircle ≡ (dp_q*dpr - dp_r*dpq) - lq*dpr + lr*dpq

    //  Step 3: Rearrange: (A - B) - C + D where A=dp_q*dpr, B=dp_r*dpq, C=lq*dpr, D=lr*dpq
    //  Goal: ≡ (A - C) + (D - B) = (dp_q - lq)*dpr + (lr - dp_r)*dpq
    //  Use sub_add_rearrange(A, D, B, C): (A+D)-(B+C) ≡ (A-B)+(D-C)
    //  But we have (A-B)-C+D. Let's go through: (A-B)-C+D = (A-B)+(D-C) by sub_add on the outer.
    //  Actually: ((A-B)-C)+D. sub_is_add_neg: (A-B)-C ≡ (A-B)+(-C).
    //  Then ((A-B)+(-C))+D ≡ (A-B)+((-C)+D) by assoc ≡ (A-B)+(D-C) by comm+sub.
    //  Alternatively: use sub_add_rearrange on (A,D,C,B): (A+D)-(C+B) ≡ (A-C)+(D-B)
    //  and show (A-B)-C+D ≡ (A+D)-(C+B).

    //  Path: (A-B)-C+D
    //  sub_add_rearrange(A,D,B,C): (A+D)-(B+C) ≡ (A-B)+(D-C)
    //  Also: sub_add_rearrange(A,D,C,B): (A+D)-(C+B) ≡ (A-C)+(D-B)
    //  And (B+C) ≡ (C+B) by commutativity.
    //  So (A-B)+(D-C) ≡ (A+D)-(B+C) ≡ (A+D)-(C+B) ≡ (A-C)+(D-B)
    let a = dp_q.mul(dpr);
    let b = dp_r.mul(dpq);
    let c = lq.mul(dpr);
    let d = lr.mul(dpq);

    //  (A-B)+(D-C) ≡ (A+D)-(B+C) [sub_add_rearrange reverse]
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(a, d, b, c);
    T::axiom_eqv_symmetric(a.add(d).sub(b.add(c)), a.sub(b).add(d.sub(c)));

    //  (B+C) ≡ (C+B) [commutativity]
    T::axiom_add_commutative(b, c);
    T::axiom_eqv_reflexive(a.add(d));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(d), a.add(d), b.add(c), c.add(b),
    );
    //  (A+D)-(B+C) ≡ (A+D)-(C+B)

    //  (A+D)-(C+B) ≡ (A-C)+(D-B) [sub_add_rearrange]
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(a, d, c, b);

    //  Chain: (A-B)+(D-C) ≡ (A+D)-(B+C) ≡ (A+D)-(C+B) ≡ (A-C)+(D-B)
    T::axiom_eqv_transitive(
        a.sub(b).add(d.sub(c)),
        a.add(d).sub(b.add(c)),
        a.add(d).sub(c.add(b)),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(d.sub(c)),
        a.add(d).sub(c.add(b)),
        a.sub(c).add(d.sub(b)),
    );
    //  So: (dp_q*dpr - dp_r*dpq) + (lr*dpq - lq*dpr) ≡ (dp_q*dpr - lq*dpr) + (lr*dpq - dp_r*dpq)

    //  Now show (A-B)-C+D ≡ (A-B)+(D-C)
    //  (A-B)-C = (A-B)+(-C) [sub_is_add_neg]
    //  (A-B)+(-C)+D = (A-B)+((-C)+D) [add_assoc]
    //  (-C)+D = D+(-C) = D-C [comm + sub]
    T::axiom_sub_is_add_neg(a.sub(b), c);
    T::axiom_add_associative(a.sub(b), c.neg(), d);
    T::axiom_add_commutative(c.neg(), d);
    lemma_add_neg_is_sub::<T>(d, c);
    T::axiom_eqv_transitive(c.neg().add(d), d.add(c.neg()), d.sub(c));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.sub(b), c.neg().add(d), d.sub(c),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.neg().add(d)),
        a.sub(b).add(d.sub(c)),
        a.sub(c).add(d.sub(b)),
    );
    //  sub to add+neg:
    T::axiom_eqv_symmetric(a.sub(b).sub(c), a.sub(b).add(c.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b).sub(c), a.sub(b).add(c.neg()),
        d, d,
    );
    T::axiom_eqv_reflexive(d);
    T::axiom_eqv_transitive(
        a.sub(b).sub(c).add(d),
        a.sub(b).add(c.neg()).add(d),
        a.sub(b).add(c.neg().add(d)),
    );
    T::axiom_eqv_transitive(
        a.sub(b).sub(c).add(d),
        a.sub(b).add(c.neg().add(d)),
        a.sub(c).add(d.sub(b)),
    );
    //  incircle ≡ (A-B)-C+D ≡ (A-C)+(D-B)

    //  Chain from the Lagrange substitution
    T::axiom_eqv_transitive(
        lp.mul(dqr).sub(lq.mul(dpr)).add(lr.mul(dpq)),
        a.sub(b).sub(c).add(d),
        a.sub(c).add(d.sub(b)),
    );

    //  Step 4: Factor: A-C = (dp_q - lq)*dpr, D-B = (lr - dp_r)*dpq
    //  A-C = dp_q*dpr - lq*dpr ≡ (dp_q - lq)*dpr [right_distributes_over_sub reverse]
    crate::triangle_intersection::lemma_right_distributes_over_sub::<T>(dp_q, lq, dpr);
    T::axiom_eqv_symmetric(dp_q.mul(dpr).sub(lq.mul(dpr)), dp_q.sub(lq).mul(dpr));
    //  D-B = lr*dpq - dp_r*dpq ≡ (lr - dp_r)*dpq
    crate::triangle_intersection::lemma_right_distributes_over_sub::<T>(lr, dp_r, dpq);
    T::axiom_eqv_symmetric(lr.mul(dpq).sub(dp_r.mul(dpq)), lr.sub(dp_r).mul(dpq));

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(c), dp_q.sub(lq).mul(dpr),
        d.sub(b), lr.sub(dp_r).mul(dpq),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr).sub(lq.mul(dpr)).add(lr.mul(dpq)),
        a.sub(c).add(d.sub(b)),
        dp_q.sub(lq).mul(dpr).add(lr.sub(dp_r).mul(dpq)),
    );
    //  incircle ≡ (dp_q - lq)*dpr + (lr - dp_r)*dpq

    //  Step 5: Negate: -incircle ≡ -[(dp_q - lq)*dpr + (lr - dp_r)*dpq]
    //  = -(dp_q - lq)*dpr + -(lr - dp_r)*dpq [neg_add]
    //  = (lq - dp_q)*dpr + (dp_r - lr)*dpq [neg_sub on each factor]
    additive_group_lemmas::lemma_neg_congruence::<T>(
        lp.mul(dqr).sub(lq.mul(dpr)).add(lr.mul(dpq)),
        dp_q.sub(lq).mul(dpr).add(lr.sub(dp_r).mul(dpq)),
    );
    additive_group_lemmas::lemma_neg_add::<T>(
        dp_q.sub(lq).mul(dpr), lr.sub(dp_r).mul(dpq),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr).sub(lq.mul(dpr)).add(lr.mul(dpq)).neg(),
        dp_q.sub(lq).mul(dpr).add(lr.sub(dp_r).mul(dpq)).neg(),
        dp_q.sub(lq).mul(dpr).neg().add(lr.sub(dp_r).mul(dpq).neg()),
    );

    //  -(X*dpr) ≡ (-X)*dpr ≡ (lq - dp_q)*dpr
    ring_lemmas::lemma_mul_neg_left::<T>(dp_q.sub(lq), dpr);
    T::axiom_eqv_symmetric(dp_q.sub(lq).neg().mul(dpr), dp_q.sub(lq).mul(dpr).neg());
    lemma_neg_sub::<T>(dp_q, lq);
    T::axiom_mul_congruence_left(dp_q.sub(lq).neg(), lq.sub(dp_q), dpr);
    T::axiom_eqv_transitive(
        dp_q.sub(lq).mul(dpr).neg(),
        dp_q.sub(lq).neg().mul(dpr),
        lq.sub(dp_q).mul(dpr),
    );

    //  -(Y*dpq) ≡ (-Y)*dpq ≡ (dp_r - lr)*dpq
    ring_lemmas::lemma_mul_neg_left::<T>(lr.sub(dp_r), dpq);
    T::axiom_eqv_symmetric(lr.sub(dp_r).neg().mul(dpq), lr.sub(dp_r).mul(dpq).neg());
    lemma_neg_sub::<T>(lr, dp_r);
    T::axiom_mul_congruence_left(lr.sub(dp_r).neg(), dp_r.sub(lr), dpq);
    T::axiom_eqv_transitive(
        lr.sub(dp_r).mul(dpq).neg(),
        lr.sub(dp_r).neg().mul(dpq),
        dp_r.sub(lr).mul(dpq),
    );

    additive_group_lemmas::lemma_add_congruence::<T>(
        dp_q.sub(lq).mul(dpr).neg(), lq.sub(dp_q).mul(dpr),
        lr.sub(dp_r).mul(dpq).neg(), dp_r.sub(lr).mul(dpq),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr).sub(lq.mul(dpr)).add(lr.mul(dpq)).neg(),
        dp_q.sub(lq).mul(dpr).neg().add(lr.sub(dp_r).mul(dpq).neg()),
        lq.sub(dp_q).mul(dpr).add(dp_r.sub(lr).mul(dpq)),
    );
    //  -incircle ≡ (lq - dp_q)*dpr + (dp_r - lr)*dpq ✓
}

///  LHS form: lift(p)*D + lift(q-p)*dpr - lift(r-p)*dpq ≡ (lq - dot(p,q))*dpr + (dot(p,r) - lr)*dpq
///
///  Uses Lagrange, norm_sq_sub_expand, and dot commutativity.
proof fn lemma_swap_ad_lhs_form<T: Ring>(p: Vec2<T>, q: Vec2<T>, r: Vec2<T>)
    ensures
        lift(p).mul(det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r)))
            .add(lift(q.sub(p)).mul(det2d(p, r)))
            .sub(lift(r.sub(p)).mul(det2d(p, q)))
            .eqv(
                lift(q).sub(vec2_dot(p, q)).mul(det2d(p, r))
                    .add(vec2_dot(p, r).sub(lift(r)).mul(det2d(p, q)))
            ),
{
    let lp = lift(p);
    let lq = lift(q);
    let lr = lift(r);
    let dqr = det2d(q, r);
    let dpr = det2d(p, r);
    let dpq = det2d(p, q);
    let dqp = det2d(q, p);
    let dp_q = vec2_dot(p, q);
    let dp_r = vec2_dot(p, r);
    let lqp = lift(q.sub(p));
    let lrp = lift(r.sub(p));

    //  === Phase A: Simplify D = dqr - dqp - dpr ===
    //  dqp ≡ -dpq (antisymmetry)
    lemma_det2d_antisymmetric::<T>(q, p);
    //  dqr - dqp ≡ dqr - (-dpq) ≡ dqr + dpq (sub_neg_is_add)
    T::axiom_eqv_reflexive(dqr);
    additive_group_lemmas::lemma_sub_congruence::<T>(dqr, dqr, dqp, dpq.neg());
    lemma_sub_neg_is_add::<T>(dqr, dpq);
    T::axiom_eqv_transitive(dqr.sub(dqp), dqr.sub(dpq.neg()), dqr.add(dpq));
    //  D = (dqr - dqp) - dpr ≡ (dqr + dpq) - dpr
    T::axiom_eqv_reflexive(dpr);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        dqr.sub(dqp), dqr.add(dpq), dpr, dpr,
    );
    //  D ≡ (dqr + dpq) - dpr
    //  lp*D ≡ lp*((dqr + dpq) - dpr)
    ring_lemmas::lemma_mul_congruence_right::<T>(
        lp, dqr.sub(dqp).sub(dpr), dqr.add(dpq).sub(dpr),
    );

    //  === Phase B: Distribute lp*((dqr+dpq) - dpr) ===
    //  lp*(X - Y) ≡ lp*X - lp*Y [mul_distributes_over_sub]
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(lp, dqr.add(dpq), dpr);
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)),
        lp.mul(dqr.add(dpq).sub(dpr)),
        lp.mul(dqr.add(dpq)).sub(lp.mul(dpr)),
    );
    //  lp*(dqr+dpq) ≡ lp*dqr + lp*dpq [axiom_mul_distributes_left]
    T::axiom_mul_distributes_left(lp, dqr, dpq);
    T::axiom_eqv_reflexive(lp.mul(dpr));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        lp.mul(dqr.add(dpq)), lp.mul(dqr).add(lp.mul(dpq)),
        lp.mul(dpr), lp.mul(dpr),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)),
        lp.mul(dqr.add(dpq)).sub(lp.mul(dpr)),
        lp.mul(dqr).add(lp.mul(dpq)).sub(lp.mul(dpr)),
    );
    //  lp*D ≡ lp*dqr + lp*dpq - lp*dpr

    //  === Phase C: Apply Lagrange to lp*dqr ===
    lemma_lagrange_2d::<T>(p, q, r);
    //  lp*dqr ≡ dp_q*dpr - dp_r*dpq
    T::axiom_eqv_reflexive(lp.mul(dpq));
    additive_group_lemmas::lemma_add_congruence::<T>(
        lp.mul(dqr), dp_q.mul(dpr).sub(dp_r.mul(dpq)),
        lp.mul(dpq), lp.mul(dpq),
    );
    T::axiom_eqv_reflexive(lp.mul(dpr));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        lp.mul(dqr).add(lp.mul(dpq)),
        dp_q.mul(dpr).sub(dp_r.mul(dpq)).add(lp.mul(dpq)),
        lp.mul(dpr), lp.mul(dpr),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)),
        lp.mul(dqr).add(lp.mul(dpq)).sub(lp.mul(dpr)),
        dp_q.mul(dpr).sub(dp_r.mul(dpq)).add(lp.mul(dpq)).sub(lp.mul(dpr)),
    );
    //  lp*D ≡ (dp_q*dpr - dp_r*dpq) + lp*dpq - lp*dpr

    //  === Phase D: Rearrange lp*D into dpr and dpq coefficient form ===
    //  We have: (dp_q*dpr - dp_r*dpq) + lp*dpq - lp*dpr
    //  Goal: (dp_q*dpr - lp*dpr) + (lp*dpq - dp_r*dpq)
    //  = (dp_q - lp)*dpr + (lp - dp_r)*dpq
    //
    //  Use sub_add_rearrange on (dp_q*dpr, lp*dpq, dp_r*dpq, lp*dpr):
    //  (A+C)-(B+D) ≡ (A-B)+(C-D) where A=dp_q*dpr, C=lp*dpq, B=dp_r*dpq, D=lp*dpr
    //  Gives: (dp_q*dpr + lp*dpq) - (dp_r*dpq + lp*dpr) ≡ (dp_q*dpr - dp_r*dpq) + (lp*dpq - lp*dpr)

    //  But we have ((dp_q*dpr - dp_r*dpq) + lp*dpq) - lp*dpr
    //  which is (A - B + C) - D. We need (A - D) + (C - B).
    //  Same rearrangement as in rhs_form. Let me reuse the pattern.

    let a = dp_q.mul(dpr);
    let b = dp_r.mul(dpq);
    let c = lp.mul(dpq);
    let d = lp.mul(dpr);
    //  We have (a-b+c)-d and want (a-d)+(c-b)

    //  First: (a-b)+c-d. Use sub_add_rearrange(a,c,b,d): (a+c)-(b+d) ≡ (a-b)+(c-d)
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(a, c, b, d);
    T::axiom_eqv_symmetric(a.add(c).sub(b.add(d)), a.sub(b).add(c.sub(d)));
    //  (a-b)+(c-d) ≡ (a+c)-(b+d)

    //  Also: sub_add_rearrange(a,c,d,b): (a+c)-(d+b) ≡ (a-d)+(c-b)
    verus_linalg::quat::ops::lemma_sub_add_rearrange::<T>(a, c, d, b);

    //  (b+d) ≡ (d+b) by commutativity
    T::axiom_add_commutative(b, d);
    T::axiom_eqv_reflexive(a.add(c));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(c), a.add(c), b.add(d), d.add(b),
    );
    //  (a+c)-(b+d) ≡ (a+c)-(d+b)
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).sub(b.add(d)),
        a.add(c).sub(d.add(b)),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).sub(d.add(b)),
        a.sub(d).add(c.sub(b)),
    );
    //  (a-b)+(c-d) ≡ (a-d)+(c-b)

    //  Now connect (a-b+c)-d to (a-b)+(c-d) via associativity
    T::axiom_sub_is_add_neg(a.sub(b).add(c), d);
    T::axiom_add_associative(a.sub(b), c, d.neg());
    lemma_add_neg_is_sub::<T>(c, d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.sub(b), c.add(d.neg()), c.sub(d),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.add(d.neg())),
        a.sub(b).add(c.sub(d)),
        a.sub(d).add(c.sub(b)),
    );
    T::axiom_eqv_symmetric(
        a.sub(b).add(c).add(d.neg()),
        a.sub(b).add(c.add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c).add(d.neg()),
        a.sub(b).add(c.add(d.neg())),
        a.sub(d).add(c.sub(b)),
    );
    T::axiom_eqv_symmetric(a.sub(b).add(c).sub(d), a.sub(b).add(c).add(d.neg()));
    T::axiom_eqv_transitive(
        a.sub(b).add(c).sub(d),
        a.sub(b).add(c).add(d.neg()),
        a.sub(d).add(c.sub(b)),
    );
    //  (a-b+c)-d ≡ (a-d)+(c-b)

    //  Chain from Phase C: lp*D ≡ (a-b+c)-d ≡ (a-d)+(c-b)
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)),
        a.sub(b).add(c).sub(d),
        a.sub(d).add(c.sub(b)),
    );
    //  lp*D ≡ (dp_q*dpr - lp*dpr) + (lp*dpq - dp_r*dpq)

    //  Factor: (dp_q - lp)*dpr and (lp - dp_r)*dpq
    crate::triangle_intersection::lemma_right_distributes_over_sub::<T>(dp_q, lp, dpr);
    T::axiom_eqv_symmetric(a.sub(d), dp_q.sub(lp).mul(dpr));
    crate::triangle_intersection::lemma_right_distributes_over_sub::<T>(lp, dp_r, dpq);
    T::axiom_eqv_symmetric(c.sub(b), lp.sub(dp_r).mul(dpq));

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(d), dp_q.sub(lp).mul(dpr),
        c.sub(b), lp.sub(dp_r).mul(dpq),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)),
        a.sub(d).add(c.sub(b)),
        dp_q.sub(lp).mul(dpr).add(lp.sub(dp_r).mul(dpq)),
    );
    //  lp*D ≡ (dp_q - lp)*dpr + (lp - dp_r)*dpq

    //  === Phase E: Apply norm_sq_sub_expand for lqp and lrp ===
    //  lqp = lift(q-p) ≡ lq - 2*dot(q,p) + lp
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(q, p);
    let two_dqp = verus_algebra::convex::two::<T>().mul(vec2_dot(q, p));
    //  lqp ≡ lq - two_dqp + lp

    //  lqp*dpr ≡ (lq - two_dqp + lp)*dpr
    ring_lemmas::lemma_mul_congruence_right::<T>(
        dpr, lqp, lq.sub(two_dqp).add(lp),
    );
    T::axiom_mul_commutative(lqp, dpr);
    T::axiom_mul_commutative(dpr, lq.sub(two_dqp).add(lp));
    T::axiom_eqv_transitive(lqp.mul(dpr), dpr.mul(lqp), dpr.mul(lq.sub(two_dqp).add(lp)));
    T::axiom_eqv_transitive(
        lqp.mul(dpr), dpr.mul(lq.sub(two_dqp).add(lp)),
        lq.sub(two_dqp).add(lp).mul(dpr),
    );

    //  Distribute (lq - two_dqp + lp)*dpr = ((lq - two_dqp) + lp)*dpr
    //  = (lq - two_dqp)*dpr + lp*dpr
    ring_lemmas::lemma_mul_distributes_right::<T>(lq.sub(two_dqp), lp, dpr);
    T::axiom_eqv_transitive(
        lqp.mul(dpr),
        lq.sub(two_dqp).add(lp).mul(dpr),
        lq.sub(two_dqp).mul(dpr).add(lp.mul(dpr)),
    );
    //  lqp*dpr ≡ (lq - two_dqp)*dpr + lp*dpr

    //  Similarly for lrp*dpq
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(r, p);
    let two_drp = verus_algebra::convex::two::<T>().mul(vec2_dot(r, p));
    //  lrp ≡ lr - two_drp + lp

    ring_lemmas::lemma_mul_congruence_right::<T>(
        dpq, lrp, lr.sub(two_drp).add(lp),
    );
    T::axiom_mul_commutative(lrp, dpq);
    T::axiom_mul_commutative(dpq, lr.sub(two_drp).add(lp));
    T::axiom_eqv_transitive(lrp.mul(dpq), dpq.mul(lrp), dpq.mul(lr.sub(two_drp).add(lp)));
    T::axiom_eqv_transitive(
        lrp.mul(dpq), dpq.mul(lr.sub(two_drp).add(lp)),
        lr.sub(two_drp).add(lp).mul(dpq),
    );
    ring_lemmas::lemma_mul_distributes_right::<T>(lr.sub(two_drp), lp, dpq);
    T::axiom_eqv_transitive(
        lrp.mul(dpq),
        lr.sub(two_drp).add(lp).mul(dpq),
        lr.sub(two_drp).mul(dpq).add(lp.mul(dpq)),
    );
    //  lrp*dpq ≡ (lr - two_drp)*dpq + lp*dpq

    //  === Phase F: Factor Phase E results ===
    //  lqp*dpr ≡ ... ≡ ((lq-two_dqp)+lp)*dpr
    ring_lemmas::lemma_mul_distributes_right::<T>(lq.sub(two_dqp), lp, dpr);
    T::axiom_eqv_symmetric(
        lq.sub(two_dqp).add(lp).mul(dpr),
        lq.sub(two_dqp).mul(dpr).add(lp.mul(dpr)),
    );
    T::axiom_eqv_transitive(
        lqp.mul(dpr),
        lq.sub(two_dqp).mul(dpr).add(lp.mul(dpr)),
        lq.sub(two_dqp).add(lp).mul(dpr),
    );
    //  lrp*dpq ≡ ... ≡ ((lr-two_drp)+lp)*dpq
    ring_lemmas::lemma_mul_distributes_right::<T>(lr.sub(two_drp), lp, dpq);
    T::axiom_eqv_symmetric(
        lr.sub(two_drp).add(lp).mul(dpq),
        lr.sub(two_drp).mul(dpq).add(lp.mul(dpq)),
    );
    T::axiom_eqv_transitive(
        lrp.mul(dpq),
        lr.sub(two_drp).mul(dpq).add(lp.mul(dpq)),
        lr.sub(two_drp).add(lp).mul(dpq),
    );

    //  === Phase G: Build substituted LHS ===
    let u = dp_q.sub(lp).mul(dpr);
    let v = lp.sub(dp_r).mul(dpq);
    let w = lq.sub(two_dqp).add(lp).mul(dpr);
    let x = lr.sub(two_drp).add(lp).mul(dpq);
    additive_group_lemmas::lemma_add_congruence::<T>(
        lp.mul(dqr.sub(dqp).sub(dpr)), u.add(v),
        lqp.mul(dpr), w,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        lp.mul(dqr.sub(dqp).sub(dpr)).add(lqp.mul(dpr)), u.add(v).add(w),
        lrp.mul(dpq), x,
    );
    //  LHS ≡ (u+v)+w-x

    //  === Phase H: Rearrange (u+v)+w-x to (u+w)+(v-x) ===
    //  (u+v)+w ≡ u+(v+w) ≡ u+(w+v) ≡ (u+w)+v
    T::axiom_add_associative(u, v, w);
    T::axiom_add_commutative(v, w);
    additive_group_lemmas::lemma_add_congruence_right::<T>(u, v.add(w), w.add(v));
    T::axiom_eqv_transitive(
        u.add(v).add(w), u.add(v.add(w)), u.add(w.add(v)),
    );
    T::axiom_add_associative(u, w, v);
    T::axiom_eqv_symmetric(u.add(w).add(v), u.add(w.add(v)));
    T::axiom_eqv_transitive(
        u.add(v).add(w), u.add(w.add(v)), u.add(w).add(v),
    );
    //  (u+v)+w ≡ (u+w)+v
    T::axiom_eqv_reflexive(x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.add(v).add(w), u.add(w).add(v), x, x,
    );
    //  (u+v)+w-x ≡ (u+w)+v-x
    crate::segment_distance::lemma_add_sub_rearrange::<T>(u.add(w), v, x);
    crate::triangle_intersection::lemma_add_sub_rearrange::<T>(u.add(w), v, x);
    T::axiom_eqv_symmetric(
        u.add(w).add(v.sub(x)), u.add(w).sub(x).add(v),
    );
    T::axiom_eqv_transitive(
        u.add(w).add(v).sub(x),
        u.add(w).sub(x).add(v),
        u.add(w).add(v.sub(x)),
    );
    //  (u+w)+v-x ≡ (u+w)+(v-x)
    T::axiom_eqv_transitive(
        u.add(v).add(w).sub(x),
        u.add(w).add(v).sub(x),
        u.add(w).add(v.sub(x)),
    );
    //  (u+v)+w-x ≡ (u+w)+(v-x)

    //  Chain Phase G + H: LHS ≡ (u+w)+(v-x)
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)).add(lqp.mul(dpr)).sub(lrp.mul(dpq)),
        u.add(v).add(w).sub(x),
        u.add(w).add(v.sub(x)),
    );

    //  === Phase I: Factor dpr and dpq terms ===
    //  u+w ≡ ((dp_q-lp)+((lq-two_dqp)+lp))*dpr
    ring_lemmas::lemma_mul_distributes_right::<T>(
        dp_q.sub(lp), lq.sub(two_dqp).add(lp), dpr,
    );
    T::axiom_eqv_symmetric(
        dp_q.sub(lp).add(lq.sub(two_dqp).add(lp)).mul(dpr),
        dp_q.sub(lp).mul(dpr).add(lq.sub(two_dqp).add(lp).mul(dpr)),
    );
    //  v-x ≡ ((lp-dp_r)-((lr-two_drp)+lp))*dpq
    crate::triangle_intersection::lemma_right_distributes_over_sub::<T>(
        lp.sub(dp_r), lr.sub(two_drp).add(lp), dpq,
    );

    //  === Phase J: Simplify coefficients via dot commutativity + helpers ===
    //  two_dqp ≡ dp_q + dp_q
    verus_linalg::vec2::ops::lemma_dot_commutative::<T>(p, q);
    T::axiom_eqv_symmetric(dp_q, vec2_dot(q, p));
    ring_lemmas::lemma_mul_congruence_right::<T>(
        verus_algebra::convex::two::<T>(), vec2_dot(q, p), dp_q,
    );
    lemma_two_is_add::<T>(dp_q);
    T::axiom_eqv_transitive(
        two_dqp, verus_algebra::convex::two::<T>().mul(dp_q), dp_q.add(dp_q),
    );
    //  dpr coefficient cancel
    lemma_dpr_coeff_cancel::<T>(dp_q, lp, lq, two_dqp);
    T::axiom_mul_congruence_left(
        dp_q.sub(lp).add(lq.sub(two_dqp).add(lp)), lq.sub(dp_q), dpr,
    );
    T::axiom_eqv_transitive(
        u.add(w),
        dp_q.sub(lp).add(lq.sub(two_dqp).add(lp)).mul(dpr),
        lq.sub(dp_q).mul(dpr),
    );
    //  u+w ≡ (lq-dp_q)*dpr

    //  two_drp ≡ dp_r + dp_r
    verus_linalg::vec2::ops::lemma_dot_commutative::<T>(p, r);
    T::axiom_eqv_symmetric(dp_r, vec2_dot(r, p));
    ring_lemmas::lemma_mul_congruence_right::<T>(
        verus_algebra::convex::two::<T>(), vec2_dot(r, p), dp_r,
    );
    lemma_two_is_add::<T>(dp_r);
    T::axiom_eqv_transitive(
        two_drp, verus_algebra::convex::two::<T>().mul(dp_r), dp_r.add(dp_r),
    );
    //  dpq coefficient cancel
    lemma_dpq_coeff_cancel::<T>(lp, dp_r, lr, two_drp);
    T::axiom_mul_congruence_left(
        lp.sub(dp_r).sub(lr.sub(two_drp).add(lp)), dp_r.sub(lr), dpq,
    );
    T::axiom_eqv_transitive(
        v.sub(x),
        lp.sub(dp_r).sub(lr.sub(two_drp).add(lp)).mul(dpq),
        dp_r.sub(lr).mul(dpq),
    );
    //  v-x ≡ (dp_r-lr)*dpq

    //  === Phase K: Final assembly ===
    additive_group_lemmas::lemma_add_congruence::<T>(
        u.add(w), lq.sub(dp_q).mul(dpr),
        v.sub(x), dp_r.sub(lr).mul(dpq),
    );
    T::axiom_eqv_transitive(
        lp.mul(dqr.sub(dqp).sub(dpr)).add(lqp.mul(dpr)).sub(lrp.mul(dpq)),
        u.add(w).add(v.sub(x)),
        lq.sub(dp_q).mul(dpr).add(dp_r.sub(lr).mul(dpq)),
    );
    //  LHS ≡ CF ✓
}

///  Algebraic core: lift(p)*D + lift(q-p)*dpr - lift(r-p)*dpq ≡ -(lift(p)*dqr - lift(q)*dpr + lift(r)*dpq)
///  where D = det2d(q,r) - det2d(q,p) - det2d(p,r)
proof fn lemma_incircle2d_swap_ad_algebra<T: Ring>(
    p: Vec2<T>, q: Vec2<T>, r: Vec2<T>,
)
    ensures
        lift(p).mul(det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r)))
            .add(lift(q.sub(p)).mul(det2d(p, r)))
            .sub(lift(r.sub(p)).mul(det2d(p, q)))
            .eqv(
                lift(p).mul(det2d(q, r))
                    .sub(lift(q).mul(det2d(p, r)))
                    .add(lift(r).mul(det2d(p, q)))
                    .neg()
            ),
{
    let lhs = lift(p).mul(det2d(q, r).sub(det2d(q, p)).sub(det2d(p, r)))
        .add(lift(q.sub(p)).mul(det2d(p, r)))
        .sub(lift(r.sub(p)).mul(det2d(p, q)));
    let cf = lift(q).sub(vec2_dot(p, q)).mul(det2d(p, r))
        .add(vec2_dot(p, r).sub(lift(r)).mul(det2d(p, q)));
    let neg_inc = lift(p).mul(det2d(q, r))
        .sub(lift(q).mul(det2d(p, r)))
        .add(lift(r).mul(det2d(p, q)))
        .neg();

    lemma_swap_ad_lhs_form::<T>(p, q, r);
    //  lhs ≡ cf
    lemma_swap_ad_rhs_form::<T>(p, q, r);
    //  neg_inc ≡ cf
    T::axiom_eqv_symmetric(neg_inc, cf);
    T::axiom_eqv_transitive(lhs, cf, neg_inc);
}

///  incircle2d(c,d,b,a) ≡ -incircle2d(a,b,c,d)
pub proof fn lemma_incircle2d_four_point_swap<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(c, d, b, a).eqv(incircle2d(a, b, c, d).neg()),
{
    //  (a,b,c,d) → (d,b,c,a) [swap_ad: negate]
    //  (d,b,c,a) → (c,d,b,a) [cyclic_cab: preserve]
    lemma_incircle2d_swap_ad::<T>(a, b, c, d);
    //  incircle2d(d,b,c,a) ≡ -incircle2d(a,b,c,d)

    lemma_incircle2d_cyclic_cab::<T>(d, b, c, a);
    //  incircle2d(c,d,b,a) ≡ incircle2d(d,b,c,a)

    T::axiom_eqv_transitive(
        incircle2d(c, d, b, a),
        incircle2d(d, b, c, a),
        incircle2d(a, b, c, d).neg(),
    );
}

} //  verus!
