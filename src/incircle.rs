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

// =========================================================================
// Lift congruence helper
// =========================================================================

/// If p and q are component-wise equivalent, lift(p) ≡ lift(q).
proof fn lemma_lift_congruence<T: Ring>(p: Vec2<T>, q: Vec2<T>)
    requires
        p.x.eqv(q.x),
        p.y.eqv(q.y),
    ensures
        lift(p).eqv(lift(q)),
{
    // p.x*p.x ≡ q.x*q.x
    ring_lemmas::lemma_mul_congruence::<T>(p.x, q.x, p.x, q.x);
    // p.y*p.y ≡ q.y*q.y
    ring_lemmas::lemma_mul_congruence::<T>(p.y, q.y, p.y, q.y);
    // sum ≡ sum
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

// =========================================================================
// Translation invariance
// =========================================================================

/// Incircle2d is invariant under uniform translation of all four points.
///
/// This follows because incircle2d only depends on pairwise differences
/// sub2(a, d), sub2(b, d), sub2(c, d), and translation cancels in differences.
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

    // Difference vectors are equivalent after translation
    lemma_sub2_translation::<T>(d, a, v); // sub2(a+v, d+v) .eqv. sub2(a, d)
    lemma_sub2_translation::<T>(d, b, v); // sub2(b+v, d+v) .eqv. sub2(b, d)
    lemma_sub2_translation::<T>(d, c, v); // sub2(c+v, d+v) .eqv. sub2(c, d)

    let p2 = sub2(a2, d2);
    let q2 = sub2(b2, d2);
    let r2 = sub2(c2, d2);
    let p = sub2(a, d);
    let q = sub2(b, d);
    let r = sub2(c, d);

    // Component-wise equivalences (from Vec2::eqv being component-wise)
    // p2.eqv(p) means p2.x.eqv(p.x) && p2.y.eqv(p.y)

    // Lift congruence
    lemma_lift_congruence::<T>(p2, p);
    lemma_lift_congruence::<T>(q2, q);
    lemma_lift_congruence::<T>(r2, r);

    let pw2 = lift(p2);
    let qw2 = lift(q2);
    let rw2 = lift(r2);
    let pw = lift(p);
    let qw = lift(q);
    let rw = lift(r);

    // Det2d congruence
    lemma_det2d_congruence::<T>(q2, q, r2, r);  // det2d(q2,r2) ≡ det2d(q,r)
    lemma_det2d_congruence::<T>(p2, p, r2, r);  // det2d(p2,r2) ≡ det2d(p,r)
    lemma_det2d_congruence::<T>(p2, p, q2, q);  // det2d(p2,q2) ≡ det2d(p,q)

    // Product congruence: pw2*det2d(q2,r2) ≡ pw*det2d(q,r)
    ring_lemmas::lemma_mul_congruence::<T>(pw2, pw, det2d(q2, r2), det2d(q, r));
    // qw2*det2d(p2,r2) ≡ qw*det2d(p,r)
    ring_lemmas::lemma_mul_congruence::<T>(qw2, qw, det2d(p2, r2), det2d(p, r));
    // rw2*det2d(p2,q2) ≡ rw*det2d(p,q)
    ring_lemmas::lemma_mul_congruence::<T>(rw2, rw, det2d(p2, q2), det2d(p, q));

    // Combine: (pw2*D1 - qw2*D2) ≡ (pw*D1 - qw*D2)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw2.mul(det2d(q2, r2)), pw.mul(det2d(q, r)),
        qw2.mul(det2d(p2, r2)), qw.mul(det2d(p, r)),
    );

    // Final: (...) + rw2*D3 ≡ (...) + rw*D3
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

// =========================================================================
// Swap antisymmetry
// =========================================================================

/// Swapping a and b negates the incircle determinant.
///
/// incircle2d(b, a, c, d) ≡ -(incircle2d(a, b, c, d))
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

    // Original = A - B + C  where A=pw*det(q,r), B=qw*det(p,r), C=rw*det(p,q)
    // Swapped  = B - A + rw*det(q,p)
    let a_term = pw.mul(det2d(q, r));
    let b_term = qw.mul(det2d(p, r));
    let c_term = rw.mul(det2d(p, q));

    // Step 1: det2d(q, p) ≡ -det2d(p, q)
    lemma_det2d_antisymmetric::<T>(p, q);
    // gives det2d(p, q) ≡ det2d(q, p).neg()
    // We need det2d(q, p) ≡ det2d(p, q).neg()
    lemma_det2d_antisymmetric::<T>(q, p);
    // gives det2d(q, p) ≡ det2d(p, q).neg()

    // Step 2: rw * det2d(q,p) ≡ rw * (-det2d(p,q))
    ring_lemmas::lemma_mul_congruence_right::<T>(rw, det2d(q, p), det2d(p, q).neg());

    // Step 3: rw * (-det2d(p,q)) ≡ -(rw * det2d(p,q)) = -C
    ring_lemmas::lemma_mul_neg_right::<T>(rw, det2d(p, q));

    // Step 4: rw * det2d(q,p) ≡ -C
    T::axiom_eqv_transitive(
        rw.mul(det2d(q, p)),
        rw.mul(det2d(p, q).neg()),
        rw.mul(det2d(p, q)).neg(),
    );

    // Step 5: Swapped = B - A + rw*det(q,p) ≡ B - A + (-C)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b_term.sub(a_term),
        rw.mul(det2d(q, p)),
        c_term.neg(),
    );

    // Now show: -(A - B + C) ≡ B - A + (-C)

    // Step 6: -(A - B + C) ≡ -(A-B) + (-C) by neg_add
    additive_group_lemmas::lemma_neg_add::<T>(a_term.sub(b_term), c_term);

    // Step 7: A.sub(B) ≡ B.sub(A).neg() by sub_antisymmetric
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a_term, b_term);
    // gives a_term.sub(b_term).eqv(b_term.sub(a_term).neg())

    // Step 8: -(A-B) = -(B-A).neg().neg() but easier:
    // A-B ≡ -(B-A), so -(A-B) ≡ -(-(B-A)) ≡ B-A by neg_involution
    additive_group_lemmas::lemma_neg_congruence::<T>(
        a_term.sub(b_term), b_term.sub(a_term).neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(b_term.sub(a_term));
    T::axiom_eqv_transitive(
        a_term.sub(b_term).neg(),
        b_term.sub(a_term).neg().neg(),
        b_term.sub(a_term),
    );

    // Step 9: -(A-B) + (-C) ≡ (B-A) + (-C)
    T::axiom_add_congruence_left(
        a_term.sub(b_term).neg(),
        b_term.sub(a_term),
        c_term.neg(),
    );

    // Step 10: Chain: -(A-B+C) ≡ -(A-B)+(-C) ≡ (B-A)+(-C)
    T::axiom_eqv_transitive(
        a_term.sub(b_term).add(c_term).neg(),
        a_term.sub(b_term).neg().add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    // Step 11: Swapped ≡ (B-A)+(-C) [from Step 5]
    //          -(original) ≡ (B-A)+(-C) [from Step 10]
    // So: Swapped ≡ -(original) by transitivity

    // Need symmetry on the neg side:
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

/// Swapping b and c negates the incircle determinant.
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

    // incircle2d(a, c, b, d) uses: p'=sub2(a,d)=p, q'=sub2(c,d)=r, r'=sub2(b,d)=q
    // = lift(p)*det2d(r, q) - lift(r)*det2d(p, q) + lift(q)*det2d(p, r)

    let a_term = pw.mul(det2d(q, r));  // A in original
    let b_term = qw.mul(det2d(p, r));  // B in original
    let c_term = rw.mul(det2d(p, q));  // C in original

    // Swapped first term: pw*det2d(r, q) ≡ pw*(-det2d(q, r)) ≡ -A
    lemma_det2d_antisymmetric::<T>(r, q);
    ring_lemmas::lemma_mul_congruence_right::<T>(pw, det2d(r, q), det2d(q, r).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(pw, det2d(q, r));
    T::axiom_eqv_transitive(
        pw.mul(det2d(r, q)), pw.mul(det2d(q, r).neg()), a_term.neg(),
    );

    // Swapped = -A - C + B  (the second/third terms are just rearranged)
    // Original = A - B + C
    // Need: -A - C + B ≡ -(A - B + C)

    // -A - C ≡ -(A + C)  by neg_add reversed
    // -A - C + B = -(A+C) + B
    // -(A - B + C) = -A + B - C = B - A - C = B + (-A - C)

    // Step: swapped first term + second:
    // pw*det2d(r,q) - rw*det2d(p,q)  ≡ -A - C

    // sub congruence: pw*det2d(r,q).sub(rw*det2d(p,q)) ≡ (-A).sub(C)
    T::axiom_eqv_reflexive(c_term);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        pw.mul(det2d(r, q)), a_term.neg(),
        rw.mul(det2d(p, q)), c_term,
    );

    // -A - C + B is the swapped expression
    // add congruence:
    T::axiom_eqv_reflexive(b_term);
    additive_group_lemmas::lemma_add_congruence::<T>(
        pw.mul(det2d(r, q)).sub(rw.mul(det2d(p, q))),
        a_term.neg().sub(c_term),
        qw.mul(det2d(p, r)),
        b_term,
    );

    // So swapped ≡ (-A).sub(C).add(B)

    // Now show -(A - B + C) ≡ (-A).sub(C).add(B)
    // -(A - B + C) ≡ -(A-B) + (-C) ≡ (B-A) + (-C)
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

    // Need: (-A).sub(C).add(B) ≡ B.sub(A).add(C.neg())
    // (-A).sub(C) ≡ (-A) + (-C) ≡ -(A) + -(C) which is (-A)+(-C)
    // B.sub(A) + (-C) ≡ (B + (-A)) + (-C)
    // (-A).sub(C).add(B) ≡ ((-A)+(-C)) + B
    // We need: ((-A)+(-C))+B ≡ (B+(-A))+(-C)
    // This is commutativity+associativity: x+y+z ≡ z+x+y where x=-A, y=-C, z=B

    // Actually, let me use a simpler approach. Note that sub is add_neg:
    // (-A).sub(C) = (-A) + (-C) [axiom_sub_is_add_neg]
    T::axiom_sub_is_add_neg(a_term.neg(), c_term);
    // (-A).sub(C).add(B) = ((-A)+(-C))+B

    // B.sub(A) = B + (-A) [axiom_sub_is_add_neg]
    T::axiom_sub_is_add_neg(b_term, a_term);
    // B.sub(A) + (-C) = (B+(-A))+(-C)

    // Need: ((-A)+(-C))+B ≡ (B+(-A))+(-C)
    // = (-A + -C + B) ≡ (B + -A + -C)
    // By commutativity of addition this should hold
    // (-A)+(-C)+B = (-A)+((-C)+B) [assoc] = (-A)+(B+(-C)) [comm] = ((-A)+B)+(-C) [assoc]
    // = (B+(-A))+(-C) [comm on first pair]

    // Assoc: ((-A)+(-C))+B ≡ (-A)+((-C)+B)
    T::axiom_add_associative(a_term.neg(), c_term.neg(), b_term);

    // Comm: (-C)+B ≡ B+(-C)
    T::axiom_add_commutative(c_term.neg(), b_term);

    // Congr: (-A)+((-C)+B) ≡ (-A)+(B+(-C))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a_term.neg(), c_term.neg().add(b_term), b_term.add(c_term.neg()),
    );

    // Chain: ((-A)+(-C))+B ≡ (-A)+((-C)+B) ≡ (-A)+(B+(-C))
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(c_term.neg().add(b_term)),
        a_term.neg().add(b_term.add(c_term.neg())),
    );

    // Assoc back: (-A)+(B+(-C)) ≡ ((-A)+B)+(-C)
    T::axiom_add_associative(a_term.neg(), b_term, c_term.neg());
    T::axiom_eqv_symmetric(
        a_term.neg().add(b_term).add(c_term.neg()),
        a_term.neg().add(b_term.add(c_term.neg())),
    );

    // Chain: (...)+B ≡ (-A)+(B+(-C)) ≡ ((-A)+B)+(-C)
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term.add(c_term.neg())),
        a_term.neg().add(b_term).add(c_term.neg()),
    );

    // Comm: (-A)+B ≡ B+(-A)
    T::axiom_add_commutative(a_term.neg(), b_term);
    T::axiom_add_congruence_left(
        a_term.neg().add(b_term), b_term.add(a_term.neg()), c_term.neg(),
    );

    // Chain: ((-A)+(-C))+B ≡ ((-A)+B)+(-C) ≡ (B+(-A))+(-C)
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term).add(c_term.neg()),
        b_term.add(a_term.neg()).add(c_term.neg()),
    );

    // Now fold back using sub_is_add_neg: B+(-A) ≡ B.sub(A), and +(-C) stays
    T::axiom_eqv_symmetric(b_term.sub(a_term), b_term.add(a_term.neg()));
    T::axiom_add_congruence_left(
        b_term.add(a_term.neg()), b_term.sub(a_term), c_term.neg(),
    );
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        b_term.add(a_term.neg()).add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    // Similarly fold (-A).sub(C) ≡ (-A)+(-C) [already established]
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

    // Now: swapped ≡ (-A).sub(C).add(B) ≡ B.sub(A).add(C.neg()) ≡ -(original)
    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).neg(),
        b_term.sub(a_term).add(c_term.neg()),
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(c_term).add(b_term),
        b_term.sub(a_term).add(c_term.neg()),
        a_term.sub(b_term).add(c_term).neg(),
    );

    // Final: swapped ≡ (-A).sub(C).add(B) ≡ -(original)
    T::axiom_eqv_transitive(
        pw.mul(det2d(r, q)).sub(rw.mul(det2d(p, q))).add(qw.mul(det2d(p, r))),
        a_term.neg().sub(c_term).add(b_term),
        a_term.sub(b_term).add(c_term).neg(),
    );
}

/// Swapping a and c negates the incircle determinant.
/// Derived from swap_ab ∘ swap_bc ∘ swap_ab = swap_ac and
/// three negations = one negation.
pub proof fn lemma_incircle2d_swap_ac<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        incircle2d(c, b, a, d).eqv(incircle2d(a, b, c, d).neg()),
{
    // swap(b,c) on (a,b,c,d) gives -(a,b,c,d)
    lemma_incircle2d_swap_bc::<T>(a, b, c, d);
    // incircle2d(a, c, b, d) ≡ -incircle2d(a, b, c, d)

    // swap(a,b) on (a,c,b,d) gives -(a,c,b,d)
    lemma_incircle2d_swap_ab::<T>(a, c, b, d);
    // incircle2d(c, a, b, d) ≡ -incircle2d(a, c, b, d)

    // Chain: incircle2d(c,a,b,d) ≡ -(-incircle2d(a,b,c,d)) ≡ incircle2d(a,b,c,d)
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
    // So incircle2d(c, a, b, d) ≡ incircle2d(a, b, c, d) [double swap = identity]

    // Now swap(a,b) on (c,a,b,d) gives -(c,a,b,d) = -(a,b,c,d)
    lemma_incircle2d_swap_ab::<T>(c, a, b, d);
    // incircle2d(a, c, b, d)... wait, that gives us swap_ab on (c,a,b,d) → (a,c,b,d)
    // That's not right. Let me redo this.

    // Actually: swap(b,c) on (c,a,b,d) gives (c,b,a,d)
    lemma_incircle2d_swap_bc::<T>(c, a, b, d);
    // incircle2d(c, b, a, d) ≡ -incircle2d(c, a, b, d)

    // incircle2d(c, a, b, d) ≡ incircle2d(a, b, c, d) [proved above]
    // So: incircle2d(c, b, a, d) ≡ -incircle2d(c, a, b, d) ≡ -incircle2d(a, b, c, d)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        incircle2d(c, a, b, d), incircle2d(a, b, c, d),
    );
    T::axiom_eqv_transitive(
        incircle2d(c, b, a, d),
        incircle2d(c, a, b, d).neg(),
        incircle2d(a, b, c, d).neg(),
    );
}

} // verus!
