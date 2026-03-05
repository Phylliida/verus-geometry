use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq as vec2_norm_sq;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;

verus! {

// =========================================================================
// Spec functions
// =========================================================================

/// The "lift" coordinate for incircle: norm_sq(v) = v.x² + v.y²
pub open spec fn lift<T: Ring>(v: Vec2<T>) -> T {
    vec2_norm_sq(v)
}

/// Incircle determinant: tests if d is inside the circumcircle of (a, b, c).
///
/// Defined as the 3×3 determinant with rows:
///   (ax-dx, ay-dy, (ax-dx)²+(ay-dy)²)
///   (bx-dx, by-dy, (bx-dx)²+(by-dy)²)
///   (cx-dx, cy-dy, (cx-dx)²+(cy-dy)²)
///
/// Convention: positive when d is inside the circumcircle of a CCW-oriented
/// triangle (a, b, c).
pub open spec fn incircle2d<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> T {
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);
    // Cofactor expansion along the third column:
    // pw * det2d(q, r) - qw * det2d(p, r) + rw * det2d(p, q)
    pw.mul(det2d(q, r))
        .sub(qw.mul(det2d(p, r)))
        .add(rw.mul(det2d(p, q)))
}

/// Sign classification of the incircle predicate.
pub open spec fn incircle2d_sign<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> OrientationSign {
    scalar_sign(incircle2d(a, b, c, d))
}

/// d is strictly inside the circumcircle of (a, b, c), assuming CCW orientation.
pub open spec fn incircle2d_positive<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    T::zero().lt(incircle2d(a, b, c, d))
}

/// d is strictly outside the circumcircle of (a, b, c), assuming CCW orientation.
pub open spec fn incircle2d_negative<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d(a, b, c, d).lt(T::zero())
}

/// d is on the circumcircle of (a, b, c).
pub open spec fn incircle2d_cocircular<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d(a, b, c, d).eqv(T::zero())
}

// =========================================================================
// Helper: zero-row proof pattern
// =========================================================================

/// If v is the zero vector at the eqv level, then lift(v) ≡ 0.
proof fn lemma_lift_zero_eqv<T: Ring>(v: Vec2<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
    ensures
        lift(v).eqv(T::zero()),
{
    // v.x * v.x ≡ 0 * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.x, T::zero(), v.x, T::zero());
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(v.x.mul(v.x), T::zero().mul(T::zero()), T::zero());

    // v.y * v.y ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.y, T::zero(), v.y, T::zero());
    T::axiom_eqv_transitive(v.y.mul(v.y), T::zero().mul(T::zero()), T::zero());

    // lift(v) = v.x*v.x + v.y*v.y ≡ 0 + 0 ≡ 0
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

/// If u has zero components, then det2d(u, w) ≡ 0.
proof fn lemma_det2d_zero_left<T: Ring>(u: Vec2<T>, w: Vec2<T>)
    requires
        u.x.eqv(T::zero()),
        u.y.eqv(T::zero()),
    ensures
        det2d(u, w).eqv(T::zero()),
{
    // u.x * w.y ≡ 0 * w.y ≡ 0
    T::axiom_mul_congruence_left(u.x, T::zero(), w.y);
    ring_lemmas::lemma_mul_zero_left::<T>(w.y);
    T::axiom_eqv_transitive(u.x.mul(w.y), T::zero().mul(w.y), T::zero());

    // u.y * w.x ≡ 0 * w.x ≡ 0
    T::axiom_mul_congruence_left(u.y, T::zero(), w.x);
    ring_lemmas::lemma_mul_zero_left::<T>(w.x);
    T::axiom_eqv_transitive(u.y.mul(w.x), T::zero().mul(w.x), T::zero());

    // det2d(u, w) = u.x*w.y - u.y*w.x ≡ 0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(w.y), T::zero(), u.y.mul(w.x), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(det2d(u, w), T::zero().sub(T::zero()), T::zero());
}

/// If w has zero components, then det2d(u, w) ≡ 0.
proof fn lemma_det2d_zero_right<T: Ring>(u: Vec2<T>, w: Vec2<T>)
    requires
        w.x.eqv(T::zero()),
        w.y.eqv(T::zero()),
    ensures
        det2d(u, w).eqv(T::zero()),
{
    // u.x * w.y ≡ u.x * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(u.x, w.y, T::zero());
    T::axiom_mul_zero_right(u.x);
    T::axiom_eqv_transitive(u.x.mul(w.y), u.x.mul(T::zero()), T::zero());

    // u.y * w.x ≡ u.y * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(u.y, w.x, T::zero());
    T::axiom_mul_zero_right(u.y);
    T::axiom_eqv_transitive(u.y.mul(w.x), u.y.mul(T::zero()), T::zero());

    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(w.y), T::zero(), u.y.mul(w.x), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(det2d(u, w), T::zero().sub(T::zero()), T::zero());
}

/// Combine: when one vector in the incircle triple has zero components,
/// the full 3×3 determinant is zero.
///
/// If p is the zero-row: pw=0, det2d(p,r)=0, det2d(p,q)=0, so
/// incircle = 0*det2d(q,r) - qw*0 + rw*0 = 0.
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

    // pw ≡ 0
    lemma_lift_zero_eqv::<T>(p);

    // pw * det2d(q, r) ≡ 0 * det2d(q, r) ≡ 0
    T::axiom_mul_congruence_left(pw, T::zero(), det2d(q, r));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(q, r));
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), T::zero().mul(det2d(q, r)), T::zero());

    // det2d(p, r) ≡ 0
    lemma_det2d_zero_left::<T>(p, r);
    // qw * det2d(p, r) ≡ qw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(qw, det2d(p, r), T::zero());
    T::axiom_mul_zero_right(qw);
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), qw.mul(T::zero()), T::zero());

    // det2d(p, q) ≡ 0
    lemma_det2d_zero_left::<T>(p, q);
    // rw * det2d(p, q) ≡ rw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(p, q), T::zero());
    T::axiom_mul_zero_right(rw);
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), rw.mul(T::zero()), T::zero());

    // 0 - 0 ≡ 0
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

    // 0 + 0 ≡ 0
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

/// Same pattern for zero second row.
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

    // qw ≡ 0
    lemma_lift_zero_eqv::<T>(q);

    // det2d(q, r) ≡ 0
    lemma_det2d_zero_left::<T>(q, r);
    // pw * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(q, r), T::zero());
    T::axiom_mul_zero_right(pw);
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), pw.mul(T::zero()), T::zero());

    // qw * det2d(p, r) ≡ 0 * det2d(p, r) ≡ 0
    T::axiom_mul_congruence_left(qw, T::zero(), det2d(p, r));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(p, r));
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), T::zero().mul(det2d(p, r)), T::zero());

    // det2d(p, q) = det2d(p, q) where q has zero components → det2d zero right
    lemma_det2d_zero_right::<T>(p, q);
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(p, q), T::zero());
    T::axiom_mul_zero_right(rw);
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), rw.mul(T::zero()), T::zero());

    // 0 - 0 + 0 ≡ 0
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

/// Same pattern for zero third row.
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

    // rw ≡ 0
    lemma_lift_zero_eqv::<T>(r);

    // det2d(q, r) ≡ 0 (r is zero)
    lemma_det2d_zero_right::<T>(q, r);
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(q, r), T::zero());
    T::axiom_mul_zero_right(pw);
    T::axiom_eqv_transitive(pw.mul(det2d(q, r)), pw.mul(T::zero()), T::zero());

    // det2d(p, r) ≡ 0 (r is zero)
    lemma_det2d_zero_right::<T>(p, r);
    ring_lemmas::lemma_mul_congruence_right::<T>(qw, det2d(p, r), T::zero());
    T::axiom_mul_zero_right(qw);
    T::axiom_eqv_transitive(qw.mul(det2d(p, r)), qw.mul(T::zero()), T::zero());

    // rw * det2d(p, q) ≡ 0 * det2d(p, q) ≡ 0
    T::axiom_mul_congruence_left(rw, T::zero(), det2d(p, q));
    ring_lemmas::lemma_mul_zero_left::<T>(det2d(p, q));
    T::axiom_eqv_transitive(rw.mul(det2d(p, q)), T::zero().mul(det2d(p, q)), T::zero());

    // 0 - 0 + 0 ≡ 0
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

// =========================================================================
// Degenerate lemmas
// =========================================================================

/// When d coincides with a, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_da<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, a).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(a);
    lemma_incircle_zero_first_row::<T>(sub2(a, a), sub2(b, a), sub2(c, a));
}

/// When d coincides with b, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_db<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, b).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(b);
    lemma_incircle_zero_second_row::<T>(sub2(a, b), sub2(b, b), sub2(c, b));
}

/// When d coincides with c, the incircle determinant is zero.
pub proof fn lemma_incircle2d_degenerate_dc<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        incircle2d(a, b, c, c).eqv(T::zero()),
{
    lemma_sub2_self_zero::<T>(c);
    lemma_incircle_zero_third_row::<T>(sub2(a, c), sub2(b, c), sub2(c, c));
}

// =========================================================================
// Trichotomy and sign classification
// =========================================================================

/// Exactly one of {positive, negative, cocircular} holds.
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

/// The sign classification matches the scalar value.
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

} // verus!
