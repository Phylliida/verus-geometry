use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{norm_sq as vec3_norm_sq, triple, dot, cross};
use crate::point3::*;
use crate::orientation_sign::*;

verus! {

// =========================================================================
// Spec functions
// =========================================================================

/// The "lift" coordinate for insphere: norm_sq(v) = v.x² + v.y² + v.z²
pub open spec fn lift3d<T: Ring>(v: Vec3<T>) -> T {
    vec3_norm_sq(v)
}

/// Insphere determinant: tests if e is inside the circumsphere of (a, b, c, d).
///
/// Defined as the 4×4 determinant with rows built from difference vectors:
///   p = a-e, q = b-e, r = c-e, s = d-e
///   insphere3d = pw·triple(q,r,s) - qw·triple(p,r,s) + rw·triple(p,q,s) - sw·triple(p,q,r)
///
/// Convention: positive when e is inside the circumsphere of a positively-oriented
/// tetrahedron (a, b, c, d).
pub open spec fn insphere3d<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> T {
    let p = sub3(a, e);
    let q = sub3(b, e);
    let r = sub3(c, e);
    let s = sub3(d, e);
    let pw = lift3d(p);
    let qw = lift3d(q);
    let rw = lift3d(r);
    let sw = lift3d(s);
    // Cofactor expansion along the lift column:
    pw.mul(triple(q, r, s))
        .sub(qw.mul(triple(p, r, s)))
        .add(rw.mul(triple(p, q, s)))
        .sub(sw.mul(triple(p, q, r)))
}

/// Sign classification of the insphere predicate.
pub open spec fn insphere3d_sign<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> OrientationSign {
    scalar_sign(insphere3d(a, b, c, d, e))
}

/// e is strictly inside the circumsphere of (a, b, c, d).
pub open spec fn insphere3d_positive<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    T::zero().lt(insphere3d(a, b, c, d, e))
}

/// e is strictly outside the circumsphere of (a, b, c, d).
pub open spec fn insphere3d_negative<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    insphere3d(a, b, c, d, e).lt(T::zero())
}

/// e is on the circumsphere of (a, b, c, d).
pub open spec fn insphere3d_cospherical<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    insphere3d(a, b, c, d, e).eqv(T::zero())
}

// =========================================================================
// Helper: lift3d zero and congruence
// =========================================================================

/// If v is the zero vector at the eqv level, then lift3d(v) ≡ 0.
proof fn lemma_lift3d_zero_eqv<T: Ring>(v: Vec3<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
        v.z.eqv(T::zero()),
    ensures
        lift3d(v).eqv(T::zero()),
{
    // v.x * v.x ≡ 0 * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.x, T::zero(), v.x, T::zero());
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(v.x.mul(v.x), T::zero().mul(T::zero()), T::zero());

    // v.y * v.y ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.y, T::zero(), v.y, T::zero());
    T::axiom_eqv_transitive(v.y.mul(v.y), T::zero().mul(T::zero()), T::zero());

    // v.z * v.z ≡ 0
    ring_lemmas::lemma_mul_congruence::<T>(v.z, T::zero(), v.z, T::zero());
    T::axiom_eqv_transitive(v.z.mul(v.z), T::zero().mul(T::zero()), T::zero());

    // v.x*v.x + v.y*v.y ≡ 0 + 0 ≡ 0
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

    // (v.x*v.x + v.y*v.y) + v.z*v.z ≡ 0 + 0 ≡ 0
    T::axiom_add_congruence_left(
        v.x.mul(v.x).add(v.y.mul(v.y)), T::zero(), v.z.mul(v.z),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), v.z.mul(v.z), T::zero(),
    );
    T::axiom_eqv_transitive(
        v.x.mul(v.x).add(v.y.mul(v.y)).add(v.z.mul(v.z)),
        T::zero().add(v.z.mul(v.z)),
        T::zero().add(T::zero()),
    );
    T::axiom_eqv_transitive(
        v.x.mul(v.x).add(v.y.mul(v.y)).add(v.z.mul(v.z)),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

/// If p ≡ q component-wise, then lift3d(p) ≡ lift3d(q).
proof fn lemma_lift3d_congruence<T: Ring>(p: Vec3<T>, q: Vec3<T>)
    requires
        p.eqv(q),
    ensures
        lift3d(p).eqv(lift3d(q)),
{
    verus_linalg::vec3::ops::lemma_norm_sq_congruence::<T>(p, q);
}

// =========================================================================
// Helper: triple with zero vector
// =========================================================================

/// If v has zero components, triple(v, b, c) ≡ 0.
proof fn lemma_triple_zero_first<T: Ring>(v: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
        v.z.eqv(T::zero()),
    ensures
        triple(v, b, c).eqv(T::zero()),
{
    let zero_vec = Vec3::<T> { x: T::zero(), y: T::zero(), z: T::zero() };
    let w = cross(b, c);
    T::axiom_eqv_reflexive(w.x);
    T::axiom_eqv_reflexive(w.y);
    T::axiom_eqv_reflexive(w.z);
    verus_linalg::vec3::ops::lemma_dot_congruence::<T>(v, zero_vec, w, w);
    verus_linalg::vec3::ops::lemma_dot_zero_left::<T>(w);
    T::axiom_eqv_transitive(
        dot(v, cross(b, c)),
        dot(zero_vec, cross(b, c)),
        T::zero(),
    );
}

/// If v has zero components, triple(a, v, c) ≡ 0.
proof fn lemma_triple_zero_second<T: Ring>(a: Vec3<T>, v: Vec3<T>, c: Vec3<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
        v.z.eqv(T::zero()),
    ensures
        triple(a, v, c).eqv(T::zero()),
{
    // triple(a, v, c) ≡ -triple(v, a, c) by swap_12
    verus_linalg::vec3::ops::lemma_triple_swap_12::<T>(a, v, c);
    // triple(v, a, c) ≡ 0
    lemma_triple_zero_first::<T>(v, a, c);
    // neg(0) ≡ 0
    additive_group_lemmas::lemma_neg_congruence::<T>(triple(v, a, c), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(triple(v, a, c).neg(), T::zero().neg(), T::zero());
    // chain: triple(a,v,c) ≡ triple(v,a,c).neg() ≡ 0
    T::axiom_eqv_transitive(triple(a, v, c), triple(v, a, c).neg(), T::zero());
}

/// If v has zero components, triple(a, b, v) ≡ 0.
proof fn lemma_triple_zero_third<T: Ring>(a: Vec3<T>, b: Vec3<T>, v: Vec3<T>)
    requires
        v.x.eqv(T::zero()),
        v.y.eqv(T::zero()),
        v.z.eqv(T::zero()),
    ensures
        triple(a, b, v).eqv(T::zero()),
{
    // triple(a, v, b) ≡ -triple(a, b, v) by swap_23
    // So triple(a, b, v) ≡ -triple(a, v, b) ... wait, that's not what swap_23 says.
    // swap_23(a, b, v): triple(a, v, b) ≡ triple(a, b, v).neg()
    // We want triple(a, b, v) ≡ 0.
    // Use swap_23(a, v, b): triple(a, b, v) ≡ triple(a, v, b).neg()
    verus_linalg::vec3::ops::lemma_triple_swap_23::<T>(a, v, b);
    // triple(a, b, v) ≡ triple(a, v, b).neg()
    // triple(a, v, b) ≡ 0 by lemma_triple_zero_second
    lemma_triple_zero_second::<T>(a, v, b);
    additive_group_lemmas::lemma_neg_congruence::<T>(triple(a, v, b), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(triple(a, v, b).neg(), T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(triple(a, b, v), triple(a, v, b).neg(), T::zero());
}

// =========================================================================
// Zero-row lemmas: when one difference vector is zero, insphere ≡ 0
// =========================================================================

/// Helper: show that 0·x ≡ 0, given that the first factor is ≡ 0.
proof fn lemma_mul_zero_term_left<T: Ring>(a: T, b: T)
    requires a.eqv(T::zero()),
    ensures a.mul(b).eqv(T::zero()),
{
    T::axiom_mul_congruence_left(a, T::zero(), b);
    ring_lemmas::lemma_mul_zero_left::<T>(b);
    T::axiom_eqv_transitive(a.mul(b), T::zero().mul(b), T::zero());
}

/// Helper: show that x·0 ≡ 0, given that the second factor is ≡ 0.
proof fn lemma_mul_zero_term_right<T: Ring>(a: T, b: T)
    requires b.eqv(T::zero()),
    ensures a.mul(b).eqv(T::zero()),
{
    ring_lemmas::lemma_mul_congruence_right::<T>(a, b, T::zero());
    T::axiom_mul_zero_right(a);
    T::axiom_eqv_transitive(a.mul(b), a.mul(T::zero()), T::zero());
}

/// Helper: ((A - B) + C) - D ≡ 0 when A,B,C,D are all ≡ 0.
proof fn lemma_four_terms_zero<T: Ring>(a: T, b: T, c: T, d: T)
    requires
        a.eqv(T::zero()),
        b.eqv(T::zero()),
        c.eqv(T::zero()),
        d.eqv(T::zero()),
    ensures
        a.sub(b).add(c).sub(d).eqv(T::zero()),
{
    // A - B ≡ 0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(a, T::zero(), b, T::zero());
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(a.sub(b), T::zero().sub(T::zero()), T::zero());

    // (A-B) + C ≡ 0 + 0 ≡ 0
    T::axiom_add_congruence_left(a.sub(b), T::zero(), c);
    additive_group_lemmas::lemma_add_congruence_right::<T>(T::zero(), c, T::zero());
    T::axiom_eqv_transitive(
        a.sub(b).add(c),
        T::zero().add(c),
        T::zero().add(T::zero()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        a.sub(b).add(c),
        T::zero().add(T::zero()),
        T::zero(),
    );

    // ((A-B)+C) - D ≡ 0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.sub(b).add(c), T::zero(), d, T::zero(),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c).sub(d),
        T::zero().sub(T::zero()),
        T::zero(),
    );
}

/// When the first difference vector (p = a-e) is zero.
proof fn lemma_insphere_zero_first_row<T: Ring>(
    p: Vec3<T>, q: Vec3<T>, r: Vec3<T>, s: Vec3<T>,
)
    requires
        p.x.eqv(T::zero()),
        p.y.eqv(T::zero()),
        p.z.eqv(T::zero()),
    ensures ({
        let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
        pw.mul(triple(q,r,s)).sub(qw.mul(triple(p,r,s)))
            .add(rw.mul(triple(p,q,s))).sub(sw.mul(triple(p,q,r))).eqv(T::zero())
    }),
{
    let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
    lemma_lift3d_zero_eqv::<T>(p);
    lemma_mul_zero_term_left::<T>(pw, triple(q, r, s));
    lemma_triple_zero_first::<T>(p, r, s);
    lemma_mul_zero_term_right::<T>(qw, triple(p, r, s));
    lemma_triple_zero_first::<T>(p, q, s);
    lemma_mul_zero_term_right::<T>(rw, triple(p, q, s));
    lemma_triple_zero_first::<T>(p, q, r);
    lemma_mul_zero_term_right::<T>(sw, triple(p, q, r));
    lemma_four_terms_zero::<T>(
        pw.mul(triple(q,r,s)), qw.mul(triple(p,r,s)),
        rw.mul(triple(p,q,s)), sw.mul(triple(p,q,r)),
    );
}

/// When the second difference vector (q = b-e) is zero.
proof fn lemma_insphere_zero_second_row<T: Ring>(
    p: Vec3<T>, q: Vec3<T>, r: Vec3<T>, s: Vec3<T>,
)
    requires
        q.x.eqv(T::zero()),
        q.y.eqv(T::zero()),
        q.z.eqv(T::zero()),
    ensures ({
        let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
        pw.mul(triple(q,r,s)).sub(qw.mul(triple(p,r,s)))
            .add(rw.mul(triple(p,q,s))).sub(sw.mul(triple(p,q,r))).eqv(T::zero())
    }),
{
    let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
    lemma_triple_zero_first::<T>(q, r, s);
    lemma_mul_zero_term_right::<T>(pw, triple(q, r, s));
    lemma_lift3d_zero_eqv::<T>(q);
    lemma_mul_zero_term_left::<T>(qw, triple(p, r, s));
    lemma_triple_zero_second::<T>(p, q, s);
    lemma_mul_zero_term_right::<T>(rw, triple(p, q, s));
    lemma_triple_zero_second::<T>(p, q, r);
    lemma_mul_zero_term_right::<T>(sw, triple(p, q, r));
    lemma_four_terms_zero::<T>(
        pw.mul(triple(q,r,s)), qw.mul(triple(p,r,s)),
        rw.mul(triple(p,q,s)), sw.mul(triple(p,q,r)),
    );
}

/// When the third difference vector (r = c-e) is zero.
proof fn lemma_insphere_zero_third_row<T: Ring>(
    p: Vec3<T>, q: Vec3<T>, r: Vec3<T>, s: Vec3<T>,
)
    requires
        r.x.eqv(T::zero()),
        r.y.eqv(T::zero()),
        r.z.eqv(T::zero()),
    ensures ({
        let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
        pw.mul(triple(q,r,s)).sub(qw.mul(triple(p,r,s)))
            .add(rw.mul(triple(p,q,s))).sub(sw.mul(triple(p,q,r))).eqv(T::zero())
    }),
{
    let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
    lemma_triple_zero_second::<T>(q, r, s);
    lemma_mul_zero_term_right::<T>(pw, triple(q, r, s));
    lemma_triple_zero_second::<T>(p, r, s);
    lemma_mul_zero_term_right::<T>(qw, triple(p, r, s));
    lemma_lift3d_zero_eqv::<T>(r);
    lemma_mul_zero_term_left::<T>(rw, triple(p, q, s));
    lemma_triple_zero_third::<T>(p, q, r);
    lemma_mul_zero_term_right::<T>(sw, triple(p, q, r));
    lemma_four_terms_zero::<T>(
        pw.mul(triple(q,r,s)), qw.mul(triple(p,r,s)),
        rw.mul(triple(p,q,s)), sw.mul(triple(p,q,r)),
    );
}

/// When the fourth difference vector (s = d-e) is zero.
proof fn lemma_insphere_zero_fourth_row<T: Ring>(
    p: Vec3<T>, q: Vec3<T>, r: Vec3<T>, s: Vec3<T>,
)
    requires
        s.x.eqv(T::zero()),
        s.y.eqv(T::zero()),
        s.z.eqv(T::zero()),
    ensures ({
        let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
        pw.mul(triple(q,r,s)).sub(qw.mul(triple(p,r,s)))
            .add(rw.mul(triple(p,q,s))).sub(sw.mul(triple(p,q,r))).eqv(T::zero())
    }),
{
    let pw = lift3d(p); let qw = lift3d(q); let rw = lift3d(r); let sw = lift3d(s);
    lemma_triple_zero_third::<T>(q, r, s);
    lemma_mul_zero_term_right::<T>(pw, triple(q, r, s));
    lemma_triple_zero_third::<T>(p, r, s);
    lemma_mul_zero_term_right::<T>(qw, triple(p, r, s));
    lemma_triple_zero_third::<T>(p, q, s);
    lemma_mul_zero_term_right::<T>(rw, triple(p, q, s));
    lemma_lift3d_zero_eqv::<T>(s);
    lemma_mul_zero_term_left::<T>(sw, triple(p, q, r));
    lemma_four_terms_zero::<T>(
        pw.mul(triple(q,r,s)), qw.mul(triple(p,r,s)),
        rw.mul(triple(p,q,s)), sw.mul(triple(p,q,r)),
    );
}

// =========================================================================
// Degenerate lemmas
// =========================================================================

/// When e coincides with a, the insphere determinant is zero.
pub proof fn lemma_insphere3d_degenerate_ea<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        insphere3d(a, b, c, d, a).eqv(T::zero()),
{
    lemma_sub3_self_zero::<T>(a);
    lemma_insphere_zero_first_row::<T>(sub3(a, a), sub3(b, a), sub3(c, a), sub3(d, a));
}

/// When e coincides with b, the insphere determinant is zero.
pub proof fn lemma_insphere3d_degenerate_eb<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        insphere3d(a, b, c, d, b).eqv(T::zero()),
{
    lemma_sub3_self_zero::<T>(b);
    lemma_insphere_zero_second_row::<T>(sub3(a, b), sub3(b, b), sub3(c, b), sub3(d, b));
}

/// When e coincides with c, the insphere determinant is zero.
pub proof fn lemma_insphere3d_degenerate_ec<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        insphere3d(a, b, c, d, c).eqv(T::zero()),
{
    lemma_sub3_self_zero::<T>(c);
    lemma_insphere_zero_third_row::<T>(sub3(a, c), sub3(b, c), sub3(c, c), sub3(d, c));
}

/// When e coincides with d, the insphere determinant is zero.
pub proof fn lemma_insphere3d_degenerate_ed<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        insphere3d(a, b, c, d, d).eqv(T::zero()),
{
    lemma_sub3_self_zero::<T>(d);
    lemma_insphere_zero_fourth_row::<T>(sub3(a, d), sub3(b, d), sub3(c, d), sub3(d, d));
}

// =========================================================================
// Trichotomy and sign classification
// =========================================================================

/// Exactly one of {positive, negative, cospherical} holds.
pub proof fn lemma_insphere3d_trichotomy<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_positive(a, b, c, d, e) || insphere3d_negative(a, b, c, d, e) || insphere3d_cospherical(a, b, c, d, e),
        !(insphere3d_positive(a, b, c, d, e) && insphere3d_negative(a, b, c, d, e)),
        !(insphere3d_positive(a, b, c, d, e) && insphere3d_cospherical(a, b, c, d, e)),
        !(insphere3d_negative(a, b, c, d, e) && insphere3d_cospherical(a, b, c, d, e)),
{
    let val = insphere3d(a, b, c, d, e);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());
}

/// The sign classification matches the scalar value.
pub proof fn lemma_insphere3d_sign_matches<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        (insphere3d_sign(a, b, c, d, e) == OrientationSign::Positive) == insphere3d_positive(a, b, c, d, e),
        (insphere3d_sign(a, b, c, d, e) == OrientationSign::Negative) == insphere3d_negative(a, b, c, d, e),
        (insphere3d_sign(a, b, c, d, e) == OrientationSign::Zero) == insphere3d_cospherical(a, b, c, d, e),
{
    let val = insphere3d(a, b, c, d, e);
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
// Translation invariance
// =========================================================================

/// Helper: triple congruence in all three arguments.
proof fn lemma_triple_congruence_all<T: Ring>(
    a1: Vec3<T>, a2: Vec3<T>,
    b1: Vec3<T>, b2: Vec3<T>,
    c1: Vec3<T>, c2: Vec3<T>,
)
    requires
        a1.eqv(a2), b1.eqv(b2), c1.eqv(c2),
    ensures
        triple(a1, b1, c1).eqv(triple(a2, b2, c2)),
{
    verus_linalg::vec3::ops::lemma_triple_congruence_first::<T>(a1, a2, b1, c1);
    verus_linalg::vec3::ops::lemma_triple_congruence_second::<T>(a2, b1, b2, c1);
    T::axiom_eqv_transitive(triple(a1, b1, c1), triple(a2, b1, c1), triple(a2, b2, c1));
    verus_linalg::vec3::ops::lemma_triple_congruence_third::<T>(a2, b2, c1, c2);
    T::axiom_eqv_transitive(triple(a1, b1, c1), triple(a2, b2, c1), triple(a2, b2, c2));
}

/// Insphere3d is invariant under uniform translation of all five points.
pub proof fn lemma_insphere3d_translation<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
    v: Vec3<T>,
)
    ensures
        insphere3d(add_vec3(a, v), add_vec3(b, v), add_vec3(c, v), add_vec3(d, v), add_vec3(e, v))
            .eqv(insphere3d(a, b, c, d, e)),
{
    let a2 = add_vec3(a, v);
    let b2 = add_vec3(b, v);
    let c2 = add_vec3(c, v);
    let d2 = add_vec3(d, v);
    let e2 = add_vec3(e, v);

    // Difference vectors are equivalent after translation
    lemma_sub3_translation::<T>(e, a, v);
    lemma_sub3_translation::<T>(e, b, v);
    lemma_sub3_translation::<T>(e, c, v);
    lemma_sub3_translation::<T>(e, d, v);

    let p2 = sub3(a2, e2); let p = sub3(a, e);
    let q2 = sub3(b2, e2); let q = sub3(b, e);
    let r2 = sub3(c2, e2); let r = sub3(c, e);
    let s2 = sub3(d2, e2); let s = sub3(d, e);

    // Lift congruence
    lemma_lift3d_congruence::<T>(p2, p);
    lemma_lift3d_congruence::<T>(q2, q);
    lemma_lift3d_congruence::<T>(r2, r);
    lemma_lift3d_congruence::<T>(s2, s);

    let pw2 = lift3d(p2); let pw = lift3d(p);
    let qw2 = lift3d(q2); let qw = lift3d(q);
    let rw2 = lift3d(r2); let rw = lift3d(r);
    let sw2 = lift3d(s2); let sw = lift3d(s);

    // Triple congruence
    lemma_triple_congruence_all::<T>(q2, q, r2, r, s2, s);
    lemma_triple_congruence_all::<T>(p2, p, r2, r, s2, s);
    lemma_triple_congruence_all::<T>(p2, p, q2, q, s2, s);
    lemma_triple_congruence_all::<T>(p2, p, q2, q, r2, r);

    // Product congruence
    ring_lemmas::lemma_mul_congruence::<T>(pw2, pw, triple(q2,r2,s2), triple(q,r,s));
    ring_lemmas::lemma_mul_congruence::<T>(qw2, qw, triple(p2,r2,s2), triple(p,r,s));
    ring_lemmas::lemma_mul_congruence::<T>(rw2, rw, triple(p2,q2,s2), triple(p,q,s));
    ring_lemmas::lemma_mul_congruence::<T>(sw2, sw, triple(p2,q2,r2), triple(p,q,r));

    let t1a = pw2.mul(triple(q2,r2,s2)); let t1b = pw.mul(triple(q,r,s));
    let t2a = qw2.mul(triple(p2,r2,s2)); let t2b = qw.mul(triple(p,r,s));
    let t3a = rw2.mul(triple(p2,q2,s2)); let t3b = rw.mul(triple(p,q,s));
    let t4a = sw2.mul(triple(p2,q2,r2)); let t4b = sw.mul(triple(p,q,r));

    // Combine: (t1a - t2a) ≡ (t1b - t2b)
    additive_group_lemmas::lemma_sub_congruence::<T>(t1a, t1b, t2a, t2b);

    // (t1a - t2a) + t3a ≡ (t1b - t2b) + t3b
    T::axiom_add_congruence_left(t1a.sub(t2a), t1b.sub(t2b), t3a);
    additive_group_lemmas::lemma_add_congruence_right::<T>(t1b.sub(t2b), t3a, t3b);
    T::axiom_eqv_transitive(
        t1a.sub(t2a).add(t3a),
        t1b.sub(t2b).add(t3a),
        t1b.sub(t2b).add(t3b),
    );

    // ((t1a-t2a)+t3a) - t4a ≡ ((t1b-t2b)+t3b) - t4b
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t1a.sub(t2a).add(t3a), t1b.sub(t2b).add(t3b),
        t4a, t4b,
    );
}

// =========================================================================
// Swap antisymmetry: helper for algebraic rearrangement
// =========================================================================

/// Helper: negate a 4-term sub-add-sub expression.
/// Shows: -(((A-B)+C)-D) ≡ ((B-A)+(-C))-(-D)
proof fn lemma_negate_four_term<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).add(c).sub(d).neg()
            .eqv(b.sub(a).add(c.neg()).sub(d.neg())),
{
    let original = a.sub(b).add(c).sub(d);
    let x = a.sub(b).add(c); // X = (A-B)+C

    // Step 1: neg(original) ≡ D.sub(X)
    // sub_antisymmetric(X, D): X.sub(D) ≡ D.sub(X).neg()
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(x, d);
    // neg(X.sub(D)) : apply neg_congruence + neg_involution
    additive_group_lemmas::lemma_neg_congruence::<T>(x.sub(d), d.sub(x).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(d.sub(x));
    T::axiom_eqv_transitive(original.neg(), d.sub(x).neg().neg(), d.sub(x));

    // Step 2: D.sub(X) ≡ D.add(X.neg())
    T::axiom_sub_is_add_neg(d, x);

    // Step 3: X.neg() = ((A-B)+C).neg() ≡ (A-B).neg() + C.neg()
    additive_group_lemmas::lemma_neg_add::<T>(a.sub(b), c);

    // Step 4: (A-B).neg() ≡ B-A
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a, b);
    additive_group_lemmas::lemma_neg_congruence::<T>(a.sub(b), b.sub(a).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(b.sub(a));
    T::axiom_eqv_transitive(a.sub(b).neg(), b.sub(a).neg().neg(), b.sub(a));

    // Step 5: X.neg() ≡ (B-A) + (-C)
    T::axiom_add_congruence_left(a.sub(b).neg(), b.sub(a), c.neg());
    T::axiom_eqv_transitive(
        x.neg(),
        a.sub(b).neg().add(c.neg()),
        b.sub(a).add(c.neg()),
    );

    // Step 6: D.add(X.neg()) ≡ D.add((B-A)+(-C))
    additive_group_lemmas::lemma_add_congruence_right::<T>(d, x.neg(), b.sub(a).add(c.neg()));

    // Step 7: D.sub(X) ≡ D.add(X.neg()) ≡ D.add((B-A)+(-C))
    T::axiom_eqv_transitive(
        d.sub(x),
        d.add(x.neg()),
        d.add(b.sub(a).add(c.neg())),
    );

    // Step 8: D + L ≡ L + D where L = (B-A)+(-C)
    let l = b.sub(a).add(c.neg());
    T::axiom_add_commutative(d, l);

    // Step 9: chain D.sub(X) ≡ D+L ≡ L+D
    T::axiom_eqv_transitive(d.sub(x), d.add(l), l.add(d));

    // Step 10: L+D ≡ L.sub((-D))
    // sub_is_add_neg(L, D.neg()): L.sub(D.neg()) = L.add(D.neg().neg())
    T::axiom_sub_is_add_neg(l, d.neg());
    // D.neg().neg() ≡ D
    additive_group_lemmas::lemma_neg_involution::<T>(d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(l, d.neg().neg(), d);
    // L.sub(D.neg()) ≡ L.add(D.neg().neg()) ≡ L.add(D)
    T::axiom_eqv_transitive(
        l.sub(d.neg()),
        l.add(d.neg().neg()),
        l.add(d),
    );
    // symmetric: L.add(D) ≡ L.sub(D.neg())
    T::axiom_eqv_symmetric(l.sub(d.neg()), l.add(d));

    // Step 11: chain D.sub(X) ≡ L+D ≡ L.sub(D.neg())
    T::axiom_eqv_transitive(d.sub(x), l.add(d), l.sub(d.neg()));

    // Step 12: overall: original.neg() ≡ D.sub(X) ≡ L.sub(D.neg())
    T::axiom_eqv_transitive(original.neg(), d.sub(x), l.sub(d.neg()));
}

// =========================================================================
// Swap lemmas
// =========================================================================

/// Helper: bridge a triple-swap to show w·triple(a,b,c) ≡ -(w·triple(b,a,c))
/// via triple_swap_12.
proof fn lemma_bridge_swap_12<T: Ring>(w: T, a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        w.mul(triple(a, b, c)).eqv(w.mul(triple(b, a, c)).neg()),
{
    verus_linalg::vec3::ops::lemma_triple_swap_12::<T>(a, b, c);
    // triple(a,b,c) ≡ triple(b,a,c).neg()
    ring_lemmas::lemma_mul_congruence_right::<T>(w, triple(a, b, c), triple(b, a, c).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(w, triple(b, a, c));
    T::axiom_eqv_transitive(
        w.mul(triple(a, b, c)),
        w.mul(triple(b, a, c).neg()),
        w.mul(triple(b, a, c)).neg(),
    );
}

/// Helper: bridge a triple-swap to show w·triple(a,c,b) ≡ -(w·triple(a,b,c))
/// via triple_swap_23.
proof fn lemma_bridge_swap_23<T: Ring>(w: T, a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        w.mul(triple(a, c, b)).eqv(w.mul(triple(a, b, c)).neg()),
{
    verus_linalg::vec3::ops::lemma_triple_swap_23::<T>(a, b, c);
    // triple(a,c,b) ≡ triple(a,b,c).neg()
    ring_lemmas::lemma_mul_congruence_right::<T>(w, triple(a, c, b), triple(a, b, c).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(w, triple(a, b, c));
    T::axiom_eqv_transitive(
        w.mul(triple(a, c, b)),
        w.mul(triple(a, b, c).neg()),
        w.mul(triple(a, b, c)).neg(),
    );
}

/// Helper: substitute congruent terms in the 4-term expression.
/// If t1≡t1', t2≡t2', t3≡t3', t4≡t4', then (t1-t2+t3-t4)≡(t1'-t2'+t3'-t4').
proof fn lemma_four_term_congruence<T: Ring>(
    t1: T, t1p: T, t2: T, t2p: T, t3: T, t3p: T, t4: T, t4p: T,
)
    requires
        t1.eqv(t1p), t2.eqv(t2p), t3.eqv(t3p), t4.eqv(t4p),
    ensures
        t1.sub(t2).add(t3).sub(t4).eqv(t1p.sub(t2p).add(t3p).sub(t4p)),
{
    additive_group_lemmas::lemma_sub_congruence::<T>(t1, t1p, t2, t2p);
    T::axiom_add_congruence_left(t1.sub(t2), t1p.sub(t2p), t3);
    additive_group_lemmas::lemma_add_congruence_right::<T>(t1p.sub(t2p), t3, t3p);
    T::axiom_eqv_transitive(
        t1.sub(t2).add(t3), t1p.sub(t2p).add(t3), t1p.sub(t2p).add(t3p),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        t1.sub(t2).add(t3), t1p.sub(t2p).add(t3p), t4, t4p,
    );
}

/// Swapping a and b negates the insphere determinant.
pub proof fn lemma_insphere3d_swap_ab<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(b, a, c, d, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    let p = sub3(a, e); let q = sub3(b, e);
    let r = sub3(c, e); let s = sub3(d, e);
    let pw = lift3d(p); let qw = lift3d(q);
    let rw = lift3d(r); let sw = lift3d(s);

    let a_term = pw.mul(triple(q, r, s));
    let b_term = qw.mul(triple(p, r, s));
    let c_term = rw.mul(triple(p, q, s));
    let d_term = sw.mul(triple(p, q, r));

    // Swapped: insphere3d(b,a,c,d,e) has p'=q, q'=p
    // = qw·T(p,r,s) - pw·T(q,r,s) + rw·T(q,p,s) - sw·T(q,p,r)
    // = B - A + rw·T(q,p,s) - sw·T(q,p,r)

    // Bridge terms 3,4 via triple_swap_12
    lemma_bridge_swap_12::<T>(rw, q, p, s);
    // rw·T(q,p,s) ≡ -(rw·T(p,q,s)) = -C
    lemma_bridge_swap_12::<T>(sw, q, p, r);
    // sw·T(q,p,r) ≡ -(sw·T(p,q,r)) = -D

    // Swapped ≡ B - A + (-C) - (-D) via four_term_congruence
    T::axiom_eqv_reflexive(b_term);
    T::axiom_eqv_reflexive(a_term);
    lemma_four_term_congruence::<T>(
        b_term, b_term,
        a_term, a_term,
        rw.mul(triple(q, p, s)), c_term.neg(),
        sw.mul(triple(q, p, r)), d_term.neg(),
    );

    // neg(original) ≡ B.sub(A).add(C.neg()).sub(D.neg())
    lemma_negate_four_term::<T>(a_term, b_term, c_term, d_term);

    // Chain: swapped ≡ B-A+(-C)-(-D) ≡ neg(original)
    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
        b_term.sub(a_term).add(c_term.neg()).sub(d_term.neg()),
    );
    T::axiom_eqv_transitive(
        b_term.sub(a_term).add(rw.mul(triple(q, p, s))).sub(sw.mul(triple(q, p, r))),
        b_term.sub(a_term).add(c_term.neg()).sub(d_term.neg()),
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
    );
}

/// Swapping c and d negates the insphere determinant.
pub proof fn lemma_insphere3d_swap_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(a, b, d, c, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    let p = sub3(a, e); let q = sub3(b, e);
    let r = sub3(c, e); let s = sub3(d, e);
    let pw = lift3d(p); let qw = lift3d(q);
    let rw = lift3d(r); let sw = lift3d(s);

    let a_term = pw.mul(triple(q, r, s));
    let b_term = qw.mul(triple(p, r, s));
    let c_term = rw.mul(triple(p, q, s));
    let d_term = sw.mul(triple(p, q, r));

    // Swapped: insphere3d(a,b,d,c,e) has r'=s, s'=r
    // = pw·T(q,s,r) - qw·T(p,s,r) + sw·T(p,q,r) - rw·T(p,q,s)
    // = pw·T(q,s,r) - qw·T(p,s,r) + D - C

    // Bridge terms 1,2 via triple_swap_23
    lemma_bridge_swap_23::<T>(pw, q, r, s);
    // pw·T(q,s,r) ≡ -(pw·T(q,r,s)) = -A
    lemma_bridge_swap_23::<T>(qw, p, r, s);
    // qw·T(p,s,r) ≡ -(qw·T(p,r,s)) = -B

    // Swapped ≡ (-A) - (-B) + D - C via four_term_congruence
    T::axiom_eqv_reflexive(d_term);
    T::axiom_eqv_reflexive(c_term);
    lemma_four_term_congruence::<T>(
        pw.mul(triple(q, s, r)), a_term.neg(),
        qw.mul(triple(p, s, r)), b_term.neg(),
        sw.mul(triple(p, q, r)), d_term,
        rw.mul(triple(p, q, s)), c_term,
    );

    // Now: swapped ≡ (-A).sub((-B)).add(D).sub(C)
    // Need: this ≡ -(A.sub(B).add(C).sub(D))
    //
    // Use lemma_negate_four_term with args (A, B, C, D):
    // -(A-B+C-D) ≡ (B-A)+(-C)-(-D)
    // But we have (-A)-(-B)+D-C, which is different.
    //
    // Alternative: use lemma_negate_four_term with (C, D, A, B):
    // -(C-D+A-B) ≡ (D-C)+(-A)-(-B)
    // We need -(A-B+C-D) though.
    //
    // Actually, observe: neg(A-B+C-D) = neg(A) - neg(B) + neg(C) - neg(D)... no.
    // Let me use a different approach.
    //
    // Swap is (A,B,C,D) -> (-A,-B,D,C).
    // Claim: (-A)-(-B)+D-C ≡ -(A-B+C-D)
    // Both equal: -A+B+D-C = -A+B-C+D (rearranging D and -C is commutative)
    // And neg(A-B+C-D) = -A+B-C+D.

    // Approach: show (-A).sub((-B)).add(D).sub(C) ≡ (B-A)+(-C)-(-D) first,
    // then use lemma_negate_four_term.

    // Actually easier: treat this as a new rearrangement.
    // neg(A-B+C-D):
    lemma_negate_four_term::<T>(a_term, b_term, c_term, d_term);
    // gives: neg(original) ≡ (B-A)+(-C)-(-D)

    // We have swapped ≡ (-A)-(-B)+D-C
    // Need to show: (-A)-(-B)+D-C ≡ (B-A)+(-C)-(-D)

    // Step: (-A)-(-B) ≡ (-A)+B [since sub(neg(B)) = add(neg(neg(B))) = add(B)]
    T::axiom_sub_is_add_neg(a_term.neg(), b_term.neg());
    additive_group_lemmas::lemma_neg_involution::<T>(b_term);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a_term.neg(), b_term.neg().neg(), b_term,
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(b_term.neg()),
        a_term.neg().add(b_term.neg().neg()),
        a_term.neg().add(b_term),
    );

    // And: B-A ≡ B+(-A) [sub_is_add_neg]
    T::axiom_sub_is_add_neg(b_term, a_term);

    // (-A)+B ≡ B+(-A) [add_commutative]
    T::axiom_add_commutative(a_term.neg(), b_term);

    // So: (-A)+B ≡ B+(-A) ≡ B-A
    T::axiom_eqv_symmetric(b_term.sub(a_term), b_term.add(a_term.neg()));
    T::axiom_eqv_transitive(
        a_term.neg().add(b_term),
        b_term.add(a_term.neg()),
        b_term.sub(a_term),
    );

    // Chain: (-A)-(-B) ≡ (-A)+B ≡ B-A
    T::axiom_eqv_transitive(
        a_term.neg().sub(b_term.neg()),
        a_term.neg().add(b_term),
        b_term.sub(a_term),
    );

    // Now propagate: ((-A)-(-B))+D ≡ (B-A)+D
    T::axiom_add_congruence_left(
        a_term.neg().sub(b_term.neg()), b_term.sub(a_term), d_term,
    );

    // (B-A)+D ≡ (B-A)+(-C)-(-D)?  No, we need more work.
    // We have: ((-A)-(-B)+D)-C ≡ ((B-A)+D)-C
    // And target: (B-A)+(-C)-(-D)
    // These differ: ((B-A)+D)-C vs ((B-A)+(-C))-(-D)
    // In flat add: (B-A)+D+(-C) vs (B-A)+(-C)+D
    // Commute D and (-C):

    // (B-A)+D ≡ (B-A)+D [have]
    // Need: ((B-A)+D)-C ≡ ((B-A)+(-C))-(-D)

    // Convert to add: ((B-A)+D)-C = ((B-A)+D)+(-C) [sub_is_add_neg]
    let ba = b_term.sub(a_term);
    T::axiom_sub_is_add_neg(ba.add(d_term), c_term);

    // ((B-A)+(-C))-(-D) = ((B-A)+(-C))+D [sub_is_add_neg + neg_involution]
    T::axiom_sub_is_add_neg(ba.add(c_term.neg()), d_term.neg());
    additive_group_lemmas::lemma_neg_involution::<T>(d_term);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        ba.add(c_term.neg()), d_term.neg().neg(), d_term,
    );
    T::axiom_eqv_transitive(
        ba.add(c_term.neg()).sub(d_term.neg()),
        ba.add(c_term.neg()).add(d_term.neg().neg()),
        ba.add(c_term.neg()).add(d_term),
    );

    // Need: ((B-A)+D)+(-C) ≡ ((B-A)+(-C))+D
    // Assoc: ((B-A)+D)+(-C) ≡ (B-A)+(D+(-C)) [assoc]
    T::axiom_add_associative(ba, d_term, c_term.neg());
    // Comm: D+(-C) ≡ (-C)+D [comm]
    T::axiom_add_commutative(d_term, c_term.neg());
    // Congr: (B-A)+(D+(-C)) ≡ (B-A)+((-C)+D) [congruence_right]
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        ba, d_term.add(c_term.neg()), c_term.neg().add(d_term),
    );
    // Chain: (B-A)+D+(-C) ≡ (B-A)+(D+(-C)) ≡ (B-A)+((-C)+D)
    T::axiom_eqv_transitive(
        ba.add(d_term).add(c_term.neg()),
        ba.add(d_term.add(c_term.neg())),
        ba.add(c_term.neg().add(d_term)),
    );
    // Assoc back: (B-A)+((-C)+D) ≡ ((B-A)+(-C))+D [reverse assoc]
    T::axiom_add_associative(ba, c_term.neg(), d_term);
    T::axiom_eqv_symmetric(
        ba.add(c_term.neg()).add(d_term),
        ba.add(c_term.neg().add(d_term)),
    );
    T::axiom_eqv_transitive(
        ba.add(d_term).add(c_term.neg()),
        ba.add(c_term.neg().add(d_term)),
        ba.add(c_term.neg()).add(d_term),
    );

    // Now fold back from add to sub form:
    // ((B-A)+D)+(-C) = ((B-A)+D).sub(C) [sub_is_add_neg, symmetric]
    T::axiom_eqv_symmetric(
        ba.add(d_term).sub(c_term),
        ba.add(d_term).add(c_term.neg()),
    );
    // ((B-A)+(-C))+D = ((B-A)+(-C)).sub((-D)) [proved above, symmetric]
    T::axiom_eqv_symmetric(
        ba.add(c_term.neg()).sub(d_term.neg()),
        ba.add(c_term.neg()).add(d_term),
    );

    // Chain: ((B-A)+D).sub(C) ≡ ((B-A)+D)+(-C) ≡ ((B-A)+(-C))+D ≡ ((B-A)+(-C)).sub((-D))
    T::axiom_eqv_transitive(
        ba.add(d_term).sub(c_term),
        ba.add(d_term).add(c_term.neg()),
        ba.add(c_term.neg()).add(d_term),
    );
    T::axiom_eqv_transitive(
        ba.add(d_term).sub(c_term),
        ba.add(c_term.neg()).add(d_term),
        ba.add(c_term.neg()).sub(d_term.neg()),
    );

    // Propagate from ((-A)-(-B)+D)-C to ((B-A)+D)-C:
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a_term.neg().sub(b_term.neg()).add(d_term),
        ba.add(d_term),
        c_term, c_term,
    );

    // Chain: swapped ≡ ((-A)-(-B)+D)-C ≡ ((B-A)+D)-C ≡ ((B-A)+(-C))-(-D) ≡ neg(original)
    T::axiom_eqv_reflexive(c_term);
    T::axiom_eqv_transitive(
        a_term.neg().sub(b_term.neg()).add(d_term).sub(c_term),
        ba.add(d_term).sub(c_term),
        ba.add(c_term.neg()).sub(d_term.neg()),
    );

    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
        ba.add(c_term.neg()).sub(d_term.neg()),
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(b_term.neg()).add(d_term).sub(c_term),
        ba.add(c_term.neg()).sub(d_term.neg()),
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
    );

    // Final: chain four_term_congruence result with algebraic chain
    // four_term_congruence gave: insphere3d(a,b,d,c,e) ≡ intermediate
    // algebraic chain gave: intermediate ≡ neg(original)
    T::axiom_eqv_transitive(
        pw.mul(triple(q, s, r)).sub(qw.mul(triple(p, s, r)))
            .add(sw.mul(triple(p, q, r))).sub(rw.mul(triple(p, q, s))),
        a_term.neg().sub(b_term.neg()).add(d_term).sub(c_term),
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
    );
}

/// Swapping b and c negates the insphere determinant.
pub proof fn lemma_insphere3d_swap_bc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(a, c, b, d, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    let p = sub3(a, e); let q = sub3(b, e);
    let r = sub3(c, e); let s = sub3(d, e);
    let pw = lift3d(p); let qw = lift3d(q);
    let rw = lift3d(r); let sw = lift3d(s);

    let a_term = pw.mul(triple(q, r, s));
    let b_term = qw.mul(triple(p, r, s));
    let c_term = rw.mul(triple(p, q, s));
    let d_term = sw.mul(triple(p, q, r));

    // Swapped: insphere3d(a,c,b,d,e) has q'=r, r'=q
    // = pw·T(r,q,s) - rw·T(p,q,s) + qw·T(p,r,s) - sw·T(p,r,q)

    // Bridge terms 1 and 4 via triple_swap
    lemma_bridge_swap_12::<T>(pw, r, q, s);
    // pw·T(r,q,s) ≡ -(pw·T(q,r,s)) = -A
    lemma_bridge_swap_23::<T>(sw, p, q, r);
    // sw·T(p,r,q) ≡ -(sw·T(p,q,r)) = -D

    // Terms 2,3: rw·T(p,q,s) = C and qw·T(p,r,s) = B (swapped positions)

    // Swapped ≡ (-A) - C + B - (-D) via four_term_congruence
    T::axiom_eqv_reflexive(c_term);
    T::axiom_eqv_reflexive(b_term);
    lemma_four_term_congruence::<T>(
        pw.mul(triple(r, q, s)), a_term.neg(),
        rw.mul(triple(p, q, s)), c_term,
        qw.mul(triple(p, r, s)), b_term,
        sw.mul(triple(p, r, q)), d_term.neg(),
    );

    // Have: swapped ≡ (-A).sub(C).add(B).sub((-D))
    // Target: neg(original) = -(A-B+C-D)
    // Use lemma_negate_four_term:
    lemma_negate_four_term::<T>(a_term, b_term, c_term, d_term);
    // neg(original) ≡ (B-A)+(-C)-(-D)

    // Need: (-A).sub(C).add(B).sub((-D)) ≡ (B-A)+(-C)-(-D)
    // In flat add: (-A)+(-C)+B+D vs B+(-A)+(-C)+D (= (-A)+B+(-C)+D after comm)
    // Commute (-A) and B, then (-C) stays... wait:
    // swapped flat: (-A)+(-C)+B+D
    // target flat:  B+(-A)+(-C)+D  ... which is (-A)+B+(-C)+D after comm first pair
    // Hmm, (-A)+(-C)+B+D vs (-A)+B+(-C)+D
    // Commute (-C) and B in the middle.

    // (-A).sub(C) = (-A)+(-C) [sub_is_add_neg]
    T::axiom_sub_is_add_neg(a_term.neg(), c_term);

    // ((-A)+(-C))+B [have this from sub→add conversion]
    // Need: ((-A)+B)+(-C) [for the target]

    // Assoc: ((-A)+(-C))+B ≡ (-A)+((-C)+B) [assoc]
    T::axiom_add_associative(a_term.neg(), c_term.neg(), b_term);
    // Comm: (-C)+B ≡ B+(-C) [comm]
    T::axiom_add_commutative(c_term.neg(), b_term);
    // Congr: (-A)+((-C)+B) ≡ (-A)+(B+(-C)) [congr_right]
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
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term.add(c_term.neg())),
        a_term.neg().add(b_term).add(c_term.neg()),
    );

    // ((-A)+B) ≡ (B+(-A)) ≡ B-A [comm + fold sub]
    T::axiom_add_commutative(a_term.neg(), b_term);
    T::axiom_sub_is_add_neg(b_term, a_term);
    T::axiom_eqv_symmetric(b_term.sub(a_term), b_term.add(a_term.neg()));
    T::axiom_eqv_transitive(
        a_term.neg().add(b_term),
        b_term.add(a_term.neg()),
        b_term.sub(a_term),
    );

    // ((-A)+B)+(-C) ≡ (B-A)+(-C)
    T::axiom_add_congruence_left(
        a_term.neg().add(b_term), b_term.sub(a_term), c_term.neg(),
    );
    // Chain all: ((-A)+(-C))+B ≡ ((-A)+B)+(-C) ≡ (B-A)+(-C)
    T::axiom_eqv_transitive(
        a_term.neg().add(c_term.neg()).add(b_term),
        a_term.neg().add(b_term).add(c_term.neg()),
        b_term.sub(a_term).add(c_term.neg()),
    );

    // Now propagate the sub(D.neg()) part: both sides have the same sub(D.neg()) term.
    // Have: ((-A)+(-C)+B).sub(D.neg()) [swapped, after sub_is_add_neg conversion]
    // Target: ((B-A)+(-C)).sub(D.neg()) [from negate_four_term]

    // First fold (-A).sub(C) back:
    T::axiom_eqv_symmetric(
        a_term.neg().sub(c_term),
        a_term.neg().add(c_term.neg()),
    );
    // (-A).sub(C).add(B) ≡ ((-A)+(-C)).add(B) [congruence_left]
    T::axiom_add_congruence_left(
        a_term.neg().sub(c_term), a_term.neg().add(c_term.neg()), b_term,
    );
    // ((-A)+(-C)).add(B) ≡ (B-A)+(-C)  [proved above]
    T::axiom_eqv_transitive(
        a_term.neg().sub(c_term).add(b_term),
        a_term.neg().add(c_term.neg()).add(b_term),
        b_term.sub(a_term).add(c_term.neg()),
    );

    // Propagate sub(D.neg()):
    T::axiom_eqv_reflexive(d_term.neg());
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a_term.neg().sub(c_term).add(b_term),
        b_term.sub(a_term).add(c_term.neg()),
        d_term.neg(), d_term.neg(),
    );

    // swapped ≡ (-A).sub(C).add(B).sub(D.neg()) ≡ (B-A)+(-C)-(-D) ≡ neg(original)
    T::axiom_eqv_symmetric(
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
        b_term.sub(a_term).add(c_term.neg()).sub(d_term.neg()),
    );
    T::axiom_eqv_transitive(
        a_term.neg().sub(c_term).add(b_term).sub(d_term.neg()),
        b_term.sub(a_term).add(c_term.neg()).sub(d_term.neg()),
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
    );

    // Final: chain four_term_congruence result with algebraic chain
    T::axiom_eqv_transitive(
        pw.mul(triple(r, q, s)).sub(rw.mul(triple(p, q, s)))
            .add(qw.mul(triple(p, r, s))).sub(sw.mul(triple(p, r, q))),
        a_term.neg().sub(c_term).add(b_term).sub(d_term.neg()),
        a_term.sub(b_term).add(c_term).sub(d_term).neg(),
    );
}

// =========================================================================
// Even permutations
// =========================================================================

/// Double swap ab+cd preserves the insphere determinant.
pub proof fn lemma_insphere3d_double_swap_ab_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(b, a, d, c, e).eqv(insphere3d(a, b, c, d, e)),
{
    lemma_insphere3d_swap_ab::<T>(a, b, c, d, e);
    // insphere3d(b,a,c,d,e) ≡ -insphere3d(a,b,c,d,e)

    lemma_insphere3d_swap_cd::<T>(b, a, c, d, e);
    // insphere3d(b,a,d,c,e) ≡ -insphere3d(b,a,c,d,e)

    // Chain: insphere3d(b,a,d,c,e) ≡ -(-insphere3d(a,b,c,d,e))
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(b, a, c, d, e), insphere3d(a, b, c, d, e).neg(),
    );
    T::axiom_eqv_transitive(
        insphere3d(b, a, d, c, e),
        insphere3d(b, a, c, d, e).neg(),
        insphere3d(a, b, c, d, e).neg().neg(),
    );

    // Double negation
    additive_group_lemmas::lemma_neg_involution::<T>(insphere3d(a, b, c, d, e));
    T::axiom_eqv_transitive(
        insphere3d(b, a, d, c, e),
        insphere3d(a, b, c, d, e).neg().neg(),
        insphere3d(a, b, c, d, e),
    );
}

// =========================================================================
// Sign swap lemmas
// =========================================================================

/// Swapping a and b reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_ab<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(b, a, c, d, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_ab::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(b, a, c, d, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(b, a, c, d, e);
}

/// Swapping c and d reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_cd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(a, b, d, c, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_cd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(a, b, d, c, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, b, d, c, e);
}

/// Swapping b and c reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_bc<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(a, c, b, d, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_bc::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(a, c, b, d, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, c, b, d, e);
}

// =========================================================================
// Composite negating swaps (odd permutations from 3 adjacent transpositions)
// =========================================================================

/// Helper: if mid ≡ -original and result ≡ -mid, then result ≡ original.
pub proof fn lemma_compose_two_negations_preserves<T: Ring>(original: T, mid: T, result: T)
    requires
        mid.eqv(original.neg()),
        result.eqv(mid.neg()),
    ensures
        result.eqv(original),
{
    additive_group_lemmas::lemma_neg_congruence::<T>(mid, original.neg());
    // mid.neg() ≡ original.neg().neg()
    T::axiom_eqv_transitive(result, mid.neg(), original.neg().neg());
    additive_group_lemmas::lemma_neg_involution::<T>(original);
    T::axiom_eqv_transitive(result, original.neg().neg(), original);
}

/// Swapping a and c negates insphere: insphere3d(c,b,a,d,e) ≡ -insphere3d(a,b,c,d,e).
/// Composition: swap_ab → swap_bc → swap_ab (3 transpositions = odd).
pub proof fn lemma_insphere3d_swap_ac<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(c, b, a, d, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    // (a,b,c,d,e) -swap_ab-> (b,a,c,d,e) ≡ -orig
    lemma_insphere3d_swap_ab::<T>(a, b, c, d, e);
    // (b,a,c,d,e) -swap_bc-> (b,c,a,d,e) ≡ -(b,a,c,d,e)
    lemma_insphere3d_swap_bc::<T>(b, a, c, d, e);
    // (b,c,a,d,e) ≡ -(-(a,b,c,d,e)) ≡ orig
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(b, a, c, d, e),
        insphere3d(b, c, a, d, e),
    );
    // (b,c,a,d,e) -swap_ab-> (c,b,a,d,e) ≡ -(b,c,a,d,e)
    lemma_insphere3d_swap_ab::<T>(b, c, a, d, e);
    // insphere3d(c,b,a,d,e) ≡ -insphere3d(b,c,a,d,e) ≡ -insphere3d(a,b,c,d,e)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(b, c, a, d, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(c, b, a, d, e),
        insphere3d(b, c, a, d, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );
}

/// Swapping b and d negates insphere: insphere3d(a,d,c,b,e) ≡ -insphere3d(a,b,c,d,e).
/// Composition: swap_bc → swap_cd → swap_bc (3 transpositions = odd).
pub proof fn lemma_insphere3d_swap_bd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(a, d, c, b, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    // swap_bc: (a,b,c,d,e) -> (a,c,b,d,e) ≡ -orig
    lemma_insphere3d_swap_bc::<T>(a, b, c, d, e);
    // swap_cd on (a,c,b,d,e): -> (a,c,d,b,e) ≡ -(a,c,b,d,e)
    lemma_insphere3d_swap_cd::<T>(a, c, b, d, e);
    // (a,c,d,b,e) ≡ -(-(a,b,c,d,e)) ≡ orig
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(a, c, b, d, e),
        insphere3d(a, c, d, b, e),
    );
    // swap_bc on (a,c,d,b,e): -> (a,d,c,b,e) ≡ -(a,c,d,b,e)
    lemma_insphere3d_swap_bc::<T>(a, c, d, b, e);
    // Chain: (a,d,c,b,e) ≡ -(a,c,d,b,e) ≡ -(a,b,c,d,e)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(a, c, d, b, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(a, d, c, b, e),
        insphere3d(a, c, d, b, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );
}

/// Swapping a and d negates insphere: insphere3d(d,b,c,a,e) ≡ -insphere3d(a,b,c,d,e).
/// Composition: swap_ab → swap_bd → swap_ab (depends on swap_bd).
pub proof fn lemma_insphere3d_swap_ad<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(d, b, c, a, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    // swap_ab: (a,b,c,d,e) -> (b,a,c,d,e) ≡ -orig
    lemma_insphere3d_swap_ab::<T>(a, b, c, d, e);
    // swap_bd on (b,a,c,d,e): -> (b,d,c,a,e) ≡ -(b,a,c,d,e)
    lemma_insphere3d_swap_bd::<T>(b, a, c, d, e);
    // (b,d,c,a,e) ≡ -(-(a,b,c,d,e)) ≡ orig
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(b, a, c, d, e),
        insphere3d(b, d, c, a, e),
    );
    // swap_ab on (b,d,c,a,e): -> (d,b,c,a,e) ≡ -(b,d,c,a,e)
    lemma_insphere3d_swap_ab::<T>(b, d, c, a, e);
    // Chain: (d,b,c,a,e) ≡ -(b,d,c,a,e) ≡ -(a,b,c,d,e)
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(b, d, c, a, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(d, b, c, a, e),
        insphere3d(b, d, c, a, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );
}

// =========================================================================
// Even permutations — value-preserving (double negation)
// =========================================================================

/// Cyclic permutation (a,b,c) preserves insphere: insphere3d(b,c,a,d,e) ≡ insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_cycle_abc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(b, c, a, d, e).eqv(insphere3d(a, b, c, d, e)),
{
    lemma_insphere3d_swap_ab::<T>(a, b, c, d, e);
    lemma_insphere3d_swap_bc::<T>(b, a, c, d, e);
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(b, a, c, d, e),
        insphere3d(b, c, a, d, e),
    );
}

/// Cyclic permutation (b,c,d) preserves insphere: insphere3d(a,c,d,b,e) ≡ insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_cycle_bcd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(a, c, d, b, e).eqv(insphere3d(a, b, c, d, e)),
{
    lemma_insphere3d_swap_bc::<T>(a, b, c, d, e);
    lemma_insphere3d_swap_cd::<T>(a, c, b, d, e);
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(a, c, b, d, e),
        insphere3d(a, c, d, b, e),
    );
}

/// Double swap (bc)(ad) preserves insphere: insphere3d(d,c,b,a,e) ≡ insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_double_swap_bc_ad<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(d, c, b, a, e).eqv(insphere3d(a, b, c, d, e)),
{
    lemma_insphere3d_swap_bc::<T>(a, b, c, d, e);
    // (a,c,b,d,e) ≡ -orig
    lemma_insphere3d_swap_ad::<T>(a, c, b, d, e);
    // (d,c,b,a,e) ≡ -(a,c,b,d,e)
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(a, c, b, d, e),
        insphere3d(d, c, b, a, e),
    );
}

/// Double swap (ac)(bd) preserves insphere: insphere3d(c,d,a,b,e) ≡ insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_double_swap_ac_bd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(c, d, a, b, e).eqv(insphere3d(a, b, c, d, e)),
{
    lemma_insphere3d_swap_ac::<T>(a, b, c, d, e);
    // (c,b,a,d,e) ≡ -orig
    lemma_insphere3d_swap_bd::<T>(c, b, a, d, e);
    // (c,d,a,b,e) ≡ -(c,b,a,d,e)
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(c, b, a, d, e),
        insphere3d(c, d, a, b, e),
    );
}

// =========================================================================
// 4-cycles — odd permutations (negating)
// =========================================================================

/// Cyclic 4-permutation (a→b→c→d→a) negates insphere: insphere3d(b,c,d,a,e) ≡ -insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_cyclic_abcd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(b, c, d, a, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    // cycle_abc: (b,c,a,d,e) ≡ orig (even)
    lemma_insphere3d_cycle_abc::<T>(a, b, c, d, e);
    // swap_cd on (b,c,a,d,e): -> (b,c,d,a,e) ≡ -(b,c,a,d,e)
    lemma_insphere3d_swap_cd::<T>(b, c, a, d, e);
    // Chain: (b,c,d,a,e) ≡ -(b,c,a,d,e) ≡ -orig
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(b, c, a, d, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(b, c, d, a, e),
        insphere3d(b, c, a, d, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );
}

/// Reverse 4-cycle (d→c→b→a→d) negates insphere: insphere3d(d,a,b,c,e) ≡ -insphere3d(a,b,c,d,e).
pub proof fn lemma_insphere3d_cyclic_dcba<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d(d, a, b, c, e).eqv(insphere3d(a, b, c, d, e).neg()),
{
    // cycle_bcd: (a,c,d,b,e) ≡ orig (even)
    lemma_insphere3d_cycle_bcd::<T>(a, b, c, d, e);
    // swap_ab on (a,c,d,b,e): -> (c,a,d,b,e)... wait, we need (d,a,b,c,e).
    // Better: swap_ad: (d,b,c,a,e) ≡ -orig, then cycle_bcd on that
    lemma_insphere3d_swap_ad::<T>(a, b, c, d, e);
    // (d,b,c,a,e) ≡ -orig
    // cycle_bcd on (d,b,c,a,e): (d,c,a,b,e) ≡ (d,b,c,a,e)
    lemma_insphere3d_cycle_bcd::<T>(d, b, c, a, e);
    T::axiom_eqv_transitive(
        insphere3d(d, c, a, b, e),
        insphere3d(d, b, c, a, e),
        insphere3d(a, b, c, d, e).neg(),
    );
    // Hmm, that gives (d,c,a,b,e), not (d,a,b,c,e).
    // Let me use: swap_ab gives (b,a,c,d,e) ≡ -orig, then cycle_bcd on (b,a,c,d,e)
    // = (b,c,d,a,e). That's cyclic_abcd, not what we want.
    //
    // Direct approach: (d,a,b,c,e)
    // From orig, apply swap_ad: (d,b,c,a,e) ≡ -orig
    // Then swap_bc on (d,b,c,a,e): (d,c,b,a,e) ≡ -(d,b,c,a,e)
    // Then swap_cd on... hmm too many steps.
    //
    // Better: double_swap_ac_bd gives (c,d,a,b,e) ≡ orig
    // swap_ab on (c,d,a,b,e): (d,c,a,b,e) ≡ -(c,d,a,b,e) ≡ -orig
    // swap_bc on (d,c,a,b,e): (d,a,c,b,e) ≡ -(d,c,a,b,e)
    // Two negations compose: (d,a,c,b,e) ≡ orig
    // swap_cd on (d,a,c,b,e): (d,a,b,c,e) ≡ -(d,a,c,b,e) ≡ -orig ✓
    //
    // Let's just restart cleanly:
    lemma_insphere3d_double_swap_ac_bd::<T>(a, b, c, d, e);
    // (c,d,a,b,e) ≡ orig
    lemma_insphere3d_swap_ab::<T>(c, d, a, b, e);
    // (d,c,a,b,e) ≡ -(c,d,a,b,e)
    // Chain: (d,c,a,b,e) ≡ -(c,d,a,b,e) ≡ -orig
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(c, d, a, b, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(d, c, a, b, e),
        insphere3d(c, d, a, b, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );

    // (d,c,a,b,e) ≡ -orig
    // swap_bc on (d,c,a,b,e): (d,a,c,b,e) ≡ -(d,c,a,b,e)
    lemma_insphere3d_swap_bc::<T>(d, c, a, b, e);
    // compose two negations: (d,a,c,b,e) ≡ orig
    lemma_compose_two_negations_preserves::<T>(
        insphere3d(a, b, c, d, e),
        insphere3d(d, c, a, b, e),
        insphere3d(d, a, c, b, e),
    );

    // swap_cd on (d,a,c,b,e): (d,a,b,c,e) ≡ -(d,a,c,b,e) ≡ -orig
    lemma_insphere3d_swap_cd::<T>(d, a, c, b, e);
    additive_group_lemmas::lemma_neg_congruence::<T>(
        insphere3d(d, a, c, b, e), insphere3d(a, b, c, d, e),
    );
    T::axiom_eqv_transitive(
        insphere3d(d, a, b, c, e),
        insphere3d(d, a, c, b, e).neg(),
        insphere3d(a, b, c, d, e).neg(),
    );
}

// =========================================================================
// Sign variants for composite permutations
// =========================================================================

/// Swapping a and c reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_ac<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(c, b, a, d, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_ac::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(c, b, a, d, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(c, b, a, d, e);
}

/// Swapping b and d reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_bd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(a, d, c, b, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_bd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(a, d, c, b, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, d, c, b, e);
}

/// Swapping a and d reverses the insphere sign classification.
pub proof fn lemma_insphere3d_sign_swap_ad<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(d, b, c, a, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_swap_ad::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(d, b, c, a, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(d, b, c, a, e);
}

/// Cyclic 4-permutation (a→b→c→d→a) reverses insphere sign.
pub proof fn lemma_insphere3d_sign_cyclic_abcd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(b, c, d, a, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_cyclic_abcd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(b, c, d, a, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(b, c, d, a, e);
}

/// Reverse 4-cycle (d→c→b→a→d) reverses insphere sign.
pub proof fn lemma_insphere3d_sign_cyclic_dcba<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(d, a, b, c, e) == match insphere3d_sign(a, b, c, d, e) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_insphere3d_cyclic_dcba::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_neg_flips_sign::<T>(
        insphere3d(d, a, b, c, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(d, a, b, c, e);
}

/// Cyclic (a,b,c) preserves insphere sign.
pub proof fn lemma_insphere3d_sign_cycle_abc<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(b, c, a, d, e) == insphere3d_sign(a, b, c, d, e),
{
    lemma_insphere3d_cycle_abc::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        insphere3d(b, c, a, d, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(b, c, a, d, e);
}

/// Cyclic (b,c,d) preserves insphere sign.
pub proof fn lemma_insphere3d_sign_cycle_bcd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(a, c, d, b, e) == insphere3d_sign(a, b, c, d, e),
{
    lemma_insphere3d_cycle_bcd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        insphere3d(a, c, d, b, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, c, d, b, e);
}

/// Double swap (bc)(ad) preserves insphere sign.
pub proof fn lemma_insphere3d_sign_double_swap_bc_ad<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(d, c, b, a, e) == insphere3d_sign(a, b, c, d, e),
{
    lemma_insphere3d_double_swap_bc_ad::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        insphere3d(d, c, b, a, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(d, c, b, a, e);
}

/// Double swap (ac)(bd) preserves insphere sign.
pub proof fn lemma_insphere3d_sign_double_swap_ac_bd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(c, d, a, b, e) == insphere3d_sign(a, b, c, d, e),
{
    lemma_insphere3d_double_swap_ac_bd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        insphere3d(c, d, a, b, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(c, d, a, b, e);
}

/// Double swap (ab)(cd) preserves insphere sign.
pub proof fn lemma_insphere3d_sign_double_swap_ab_cd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        insphere3d_sign(b, a, d, c, e) == insphere3d_sign(a, b, c, d, e),
{
    lemma_insphere3d_double_swap_ab_cd::<T>(a, b, c, d, e);
    crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
        insphere3d(b, a, d, c, e), insphere3d(a, b, c, d, e),
    );
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(b, a, d, c, e);
}

} // verus!
