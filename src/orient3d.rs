use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::*;
use crate::point3::*;

verus! {

// ---------------------------------------------------------------------------
// Spec function
// ---------------------------------------------------------------------------

/// 3D orientation predicate: orient3d(a, b, c, d) = triple(b-a, c-a, d-a)
pub open spec fn orient3d<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    triple(sub3(b, a), sub3(c, a), sub3(d, a))
}

// ---------------------------------------------------------------------------
// Private helper
// ---------------------------------------------------------------------------

/// cross product congruence: a1≡a2, b1≡b2 implies cross(a1,b1) ≡ cross(a2,b2)
proof fn lemma_cross_congruence<T: Ring>(
    a1: Vec3<T>, a2: Vec3<T>, b1: Vec3<T>, b2: Vec3<T>,
)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        cross(a1, b1).eqv(cross(a2, b2)),
{
    // cross(a,b).x = a.y*b.z - a.z*b.y
    // Need: a1.y*b1.z ≡ a2.y*b2.z and a1.z*b1.y ≡ a2.z*b2.y
    // Then sub_congruence for each component

    // x component: a.y*b.z - a.z*b.y
    ring_lemmas::lemma_mul_congruence::<T>(a1.y, a2.y, b1.z, b2.z);
    ring_lemmas::lemma_mul_congruence::<T>(a1.z, a2.z, b1.y, b2.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.y.mul(b1.z), a2.y.mul(b2.z),
        a1.z.mul(b1.y), a2.z.mul(b2.y),
    );

    // y component: a.z*b.x - a.x*b.z
    ring_lemmas::lemma_mul_congruence::<T>(a1.z, a2.z, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence::<T>(a1.x, a2.x, b1.z, b2.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.z.mul(b1.x), a2.z.mul(b2.x),
        a1.x.mul(b1.z), a2.x.mul(b2.z),
    );

    // z component: a.x*b.y - a.y*b.x
    ring_lemmas::lemma_mul_congruence::<T>(a1.x, a2.x, b1.y, b2.y);
    ring_lemmas::lemma_mul_congruence::<T>(a1.y, a2.y, b1.x, b2.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.x.mul(b1.y), a2.x.mul(b2.y),
        a1.y.mul(b1.x), a2.y.mul(b2.x),
    );
}

// ---------------------------------------------------------------------------
// Public orient3d lemmas
// ---------------------------------------------------------------------------

/// orient3d(a, b, d, c) ≡ -orient3d(a, b, c, d)  (swap last two)
pub proof fn lemma_orient3d_swap_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d(a, b, d, c).eqv(orient3d(a, b, c, d).neg()),
{
    // orient3d(a,b,d,c) = triple(b-a, d-a, c-a)
    // orient3d(a,b,c,d) = triple(b-a, c-a, d-a)
    // triple_swap_23: triple(x, z, y) ≡ -triple(x, y, z)
    lemma_triple_swap_23::<T>(sub3(b, a), sub3(c, a), sub3(d, a));
}

/// orient3d(a, c, b, d) ≡ -orient3d(a, b, c, d)  (swap middle two)
pub proof fn lemma_orient3d_swap_bc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d(a, c, b, d).eqv(orient3d(a, b, c, d).neg()),
{
    // orient3d(a,c,b,d) = triple(c-a, b-a, d-a)
    // orient3d(a,b,c,d) = triple(b-a, c-a, d-a)
    // triple_swap_12: triple(x, y, z) ≡ -triple(y, x, z)
    // So triple(c-a, b-a, d-a) ≡ -triple(b-a, c-a, d-a)
    lemma_triple_swap_12::<T>(sub3(c, a), sub3(b, a), sub3(d, a));
}

/// orient3d(a, c, d, b) ≡ orient3d(a, b, c, d)  (cyclic permutation of b,c,d)
pub proof fn lemma_orient3d_cycle_bcd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d(a, c, d, b).eqv(orient3d(a, b, c, d)),
{
    // orient3d(a,c,d,b) = triple(c-a, d-a, b-a)
    // orient3d(a,b,c,d) = triple(b-a, c-a, d-a)
    // triple_cyclic: triple(x, y, z) ≡ triple(y, z, x)
    // triple(b-a, c-a, d-a) ≡ triple(c-a, d-a, b-a)
    lemma_triple_cyclic::<T>(sub3(b, a), sub3(c, a), sub3(d, a));
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, d),
        orient3d(a, c, d, b),
    );
}

/// orient3d(a, a, c, d) ≡ 0  (degenerate: a = b)
pub proof fn lemma_orient3d_degenerate_ab<T: Ring>(
    a: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d(a, a, c, d).eqv(T::zero()),
{
    // orient3d(a,a,c,d) = triple(a-a, c-a, d-a)
    // a-a ≡ zero_vec
    lemma_sub3_self_zero::<T>(a);
    let zero_vec = Vec3 { x: T::zero(), y: T::zero(), z: T::zero() };
    // triple(zero_vec, c-a, d-a) = dot(zero_vec, cross(c-a, d-a)) ≡ 0
    Vec3::<T>::axiom_eqv_reflexive(cross(sub3(c, a), sub3(d, a)));
    lemma_dot_congruence::<T>(
        sub3(a, a), zero_vec,
        cross(sub3(c, a), sub3(d, a)), cross(sub3(c, a), sub3(d, a)),
    );
    lemma_dot_zero_left::<T>(cross(sub3(c, a), sub3(d, a)));
    T::axiom_eqv_transitive(
        orient3d(a, a, c, d),
        dot(zero_vec, cross(sub3(c, a), sub3(d, a))),
        T::zero(),
    );
}

/// orient3d(a, b, c, c) ≡ 0  (degenerate: c = d)
pub proof fn lemma_orient3d_degenerate_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        orient3d(a, b, c, c).eqv(T::zero()),
{
    // orient3d(a,b,c,c) = triple(b-a, c-a, c-a)
    // triple_self_zero_23: triple(x, y, y) ≡ 0
    lemma_triple_self_zero_23::<T>(sub3(b, a), sub3(c, a));
}

/// orient3d is translation-invariant
pub proof fn lemma_orient3d_translation<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, t: Vec3<T>,
)
    ensures
        orient3d(add_vec3(a, t), add_vec3(b, t), add_vec3(c, t), add_vec3(d, t))
            .eqv(orient3d(a, b, c, d)),
{
    let at = add_vec3(a, t);
    let bt = add_vec3(b, t);
    let ct = add_vec3(c, t);
    let dt = add_vec3(d, t);

    // sub3(bt, at) ≡ sub3(b, a)
    lemma_sub3_translation::<T>(a, b, t);
    // sub3(ct, at) ≡ sub3(c, a)
    lemma_sub3_translation::<T>(a, c, t);
    // sub3(dt, at) ≡ sub3(d, a)
    lemma_sub3_translation::<T>(a, d, t);

    // orient3d(at,bt,ct,dt) = triple(sub3(bt,at), sub3(ct,at), sub3(dt,at))
    // ≡ triple(sub3(b,a), sub3(c,a), sub3(d,a))  via dot_congruence + cross_congruence

    // cross(sub3(ct,at), sub3(dt,at)) ≡ cross(sub3(c,a), sub3(d,a))
    lemma_cross_congruence::<T>(sub3(ct, at), sub3(c, a), sub3(dt, at), sub3(d, a));

    // dot(sub3(bt,at), cross(...)) ≡ dot(sub3(b,a), cross(...))
    lemma_dot_congruence::<T>(
        sub3(bt, at), sub3(b, a),
        cross(sub3(ct, at), sub3(dt, at)), cross(sub3(c, a), sub3(d, a)),
    );
}

// ---------------------------------------------------------------------------
// Helpers for even-permutation lemma
// ---------------------------------------------------------------------------

/// (a - p) - (b - p) ≡ a - b for Ring elements.
proof fn lemma_sub_rebase<T: Ring>(a: T, b: T, p: T)
    ensures
        a.sub(p).sub(b.sub(p)).eqv(a.sub(b)),
{
    // a.sub(p) ≡ a + (-p)
    T::axiom_sub_is_add_neg(a, p);
    // b.sub(p) ≡ b + (-p)
    T::axiom_sub_is_add_neg(b, p);
    // b.sub(p).neg() ≡ (b + (-p)).neg() ≡ (-b) + p
    T::axiom_neg_congruence(b.sub(p), b.add(p.neg()));
    additive_group_lemmas::lemma_neg_add::<T>(b, p.neg());
    additive_group_lemmas::lemma_neg_involution::<T>(p);
    additive_group_lemmas::lemma_add_congruence_right::<T>(b.neg(), p.neg().neg(), p);
    T::axiom_eqv_transitive(
        b.add(p.neg()).neg(),
        b.neg().add(p.neg().neg()),
        b.neg().add(p),
    );
    T::axiom_eqv_transitive(
        b.sub(p).neg(),
        b.add(p.neg()).neg(),
        b.neg().add(p),
    );

    // a.sub(p).sub(b.sub(p)) ≡ a.sub(p).add(b.sub(p).neg()) [sub_is_add_neg]
    T::axiom_sub_is_add_neg(a.sub(p), b.sub(p));
    // ≡ (a + (-p)) + ((-b) + p)  [congruence]
    T::axiom_add_congruence_left(a.sub(p), a.add(p.neg()), b.sub(p).neg());
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.sub(p).add(b.sub(p).neg()),
        a.add(p.neg()).add(b.sub(p).neg()),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(p.neg()), b.sub(p).neg(), b.neg().add(p),
    );
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.add(p.neg()).add(b.sub(p).neg()),
        a.add(p.neg()).add(b.neg().add(p)),
    );

    // Rearrange: (a + (-p)) + ((-b) + p) ≡ (a + (-b)) + ((-p) + p) [rearrange_2x2]
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, p.neg(), b.neg(), p);
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.add(p.neg()).add(b.neg().add(p)),
        a.add(b.neg()).add(p.neg().add(p)),
    );

    // (-p) + p ≡ p + (-p) ≡ 0
    T::axiom_add_commutative(p.neg(), p);
    T::axiom_add_inverse_right(p);
    T::axiom_eqv_transitive(p.neg().add(p), p.add(p.neg()), T::zero());
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(b.neg()), p.neg().add(p), T::zero(),
    );
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.add(b.neg()).add(p.neg().add(p)),
        a.add(b.neg()).add(T::zero()),
    );

    // x + 0 ≡ x
    T::axiom_add_zero_right(a.add(b.neg()));
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.add(b.neg()).add(T::zero()),
        a.add(b.neg()),
    );

    // a + (-b) ≡ a.sub(b)
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    T::axiom_eqv_transitive(
        a.sub(p).sub(b.sub(p)),
        a.add(b.neg()),
        a.sub(b),
    );
}

/// sub3(a, b) ≡ sub3(a, p).sub(sub3(b, p)) for any anchor point p.
proof fn lemma_sub3_rebase<T: Ring>(a: Point3<T>, b: Point3<T>, p: Point3<T>)
    ensures
        sub3(a, b).eqv(sub3(a, p).sub(sub3(b, p))),
{
    // Vec3 componentwise sub: (sub3(a,p)).sub(sub3(b,p)).x = a.x.sub(p.x).sub(b.x.sub(p.x))
    lemma_sub_rebase::<T>(a.x, b.x, p.x);
    T::axiom_eqv_symmetric(a.x.sub(p.x).sub(b.x.sub(p.x)), a.x.sub(b.x));
    lemma_sub_rebase::<T>(a.y, b.y, p.y);
    T::axiom_eqv_symmetric(a.y.sub(p.y).sub(b.y.sub(p.y)), a.y.sub(b.y));
    lemma_sub_rebase::<T>(a.z, b.z, p.z);
    T::axiom_eqv_symmetric(a.z.sub(p.z).sub(b.z.sub(p.z)), a.z.sub(b.z));
}

/// sub3(a, b) ≡ sub3(b, a).neg()
proof fn lemma_sub3_antisymmetric<T: Ring>(a: Point3<T>, b: Point3<T>)
    ensures
        sub3(a, b).eqv(sub3(b, a).neg()),
{
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.x, b.x);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.y, b.y);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.z, b.z);
}

// ---------------------------------------------------------------------------
// Even permutation: orient3d(d,c,b,a) ≡ orient3d(a,b,c,d)
// ---------------------------------------------------------------------------

/// orient3d(d, c, b, a) ≡ orient3d(a, b, c, d)
///
/// The permutation (a,b,c,d) → (d,c,b,a) is even (product of two transpositions),
/// so the sign is preserved.
pub proof fn lemma_orient3d_even_perm_dcba<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d(d, c, b, a).eqv(orient3d(a, b, c, d)),
{
    let u = sub3(b, a);
    let v = sub3(c, a);
    let w = sub3(d, a);

    // orient3d(d,c,b,a) = triple(sub3(c,d), sub3(b,d), sub3(a,d))
    // Show: sub3(c,d) ≡ v.sub(w), sub3(b,d) ≡ u.sub(w), sub3(a,d) ≡ w.neg()

    // sub3(c, d) ≡ sub3(c, a).sub(sub3(d, a)) = v.sub(w)
    lemma_sub3_rebase::<T>(c, d, a);
    // sub3(b, d) ≡ sub3(b, a).sub(sub3(d, a)) = u.sub(w)
    lemma_sub3_rebase::<T>(b, d, a);
    // sub3(a, d) ≡ sub3(d, a).neg() = w.neg()
    lemma_sub3_antisymmetric::<T>(a, d);

    // By congruence: triple(sub3(c,d), sub3(b,d), sub3(a,d))
    //              ≡ triple(v.sub(w), u.sub(w), w.neg())
    lemma_triple_congruence_third::<T>(sub3(c, d), sub3(b, d), sub3(a, d), w.neg());
    // Need congruence in first two args. Use cyclic + congruence_third.
    // Actually, easier: use dot + cross congruence directly.

    // sub3(c,d) ≡ v.sub(w)
    // sub3(b,d) ≡ u.sub(w)
    // sub3(a,d) ≡ w.neg()
    // So cross(sub3(b,d), sub3(a,d)) ≡ cross(u.sub(w), w.neg())
    lemma_cross_congruence::<T>(sub3(b, d), u.sub(w), sub3(a, d), w.neg());
    // And dot(sub3(c,d), cross(...)) ≡ dot(v.sub(w), cross(...))
    lemma_dot_congruence::<T>(
        sub3(c, d), v.sub(w),
        cross(sub3(b, d), sub3(a, d)), cross(u.sub(w), w.neg()),
    );
    // So orient3d(d,c,b,a) ≡ triple(v.sub(w), u.sub(w), w.neg())

    // Now prove: triple(v.sub(w), u.sub(w), w.neg()) ≡ triple(u, v, w)
    // Step A: neg_third: triple(v.sub(w), u.sub(w), w.neg()) ≡ -triple(v.sub(w), u.sub(w), w)
    lemma_triple_neg_third::<T>(v.sub(w), u.sub(w), w);
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(v.sub(w), u.sub(w), w.neg()),
        triple(v.sub(w), u.sub(w), w).neg(),
    );

    // Step B: sub_is_add_neg for v.sub(w) ≡ v.add(w.neg())
    Vec3::<T>::axiom_sub_is_add_neg(v, w);
    lemma_triple_congruence_first::<T>(v.sub(w), v.add(w.neg()), u.sub(w), w);
    // triple(v.sub(w), u.sub(w), w) ≡ triple(v.add(w.neg()), u.sub(w), w)
    T::axiom_neg_congruence(
        triple(v.sub(w), u.sub(w), w),
        triple(v.add(w.neg()), u.sub(w), w),
    );
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(v.sub(w), u.sub(w), w).neg(),
        triple(v.add(w.neg()), u.sub(w), w).neg(),
    );

    // Step C: linear_first: triple(v + (-w), X, w) ≡ triple(v, X, w) + triple(-w, X, w)
    lemma_triple_linear_first::<T>(v, w.neg(), u.sub(w), w);
    // triple(v.add(w.neg()), u.sub(w), w) ≡ triple(v, u.sub(w), w) + triple(w.neg(), u.sub(w), w)

    // Step D: triple(w.neg(), u.sub(w), w):
    //   neg_first: ≡ -triple(w, u.sub(w), w)
    lemma_triple_neg_first::<T>(w, u.sub(w), w);
    //   self_zero_13: triple(w, u.sub(w), w) ≡ 0
    lemma_triple_self_zero_13::<T>(w, u.sub(w));
    //   So -triple(w, u.sub(w), w) ≡ -0 ≡ 0
    T::axiom_neg_congruence(triple(w, u.sub(w), w), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(
        triple(w.neg(), u.sub(w), w),
        triple(w, u.sub(w), w).neg(),
        T::zero().neg(),
    );
    T::axiom_eqv_transitive(
        triple(w.neg(), u.sub(w), w),
        T::zero().neg(),
        T::zero(),
    );

    // triple(v, X, w) + 0 ≡ triple(v, X, w)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        triple(v, u.sub(w), w),
        triple(w.neg(), u.sub(w), w),
        T::zero(),
    );
    T::axiom_add_zero_right(triple(v, u.sub(w), w));
    T::axiom_eqv_transitive(
        triple(v, u.sub(w), w).add(triple(w.neg(), u.sub(w), w)),
        triple(v, u.sub(w), w).add(T::zero()),
        triple(v, u.sub(w), w),
    );

    // So triple(v.add(w.neg()), u.sub(w), w) ≡ triple(v, u.sub(w), w)
    T::axiom_eqv_transitive(
        triple(v.add(w.neg()), u.sub(w), w),
        triple(v, u.sub(w), w).add(triple(w.neg(), u.sub(w), w)),
        triple(v, u.sub(w), w),
    );

    // Neg congruence: -triple(v.add(w.neg()), u.sub(w), w) ≡ -triple(v, u.sub(w), w)
    T::axiom_neg_congruence(
        triple(v.add(w.neg()), u.sub(w), w),
        triple(v, u.sub(w), w),
    );
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(v.add(w.neg()), u.sub(w), w).neg(),
        triple(v, u.sub(w), w).neg(),
    );

    // Step E: Expand triple(v, u.sub(w), w) via linearity in second arg
    // sub_is_add_neg: u.sub(w) ≡ u.add(w.neg())
    Vec3::<T>::axiom_sub_is_add_neg(u, w);
    lemma_triple_congruence_second::<T>(v, u.sub(w), u.add(w.neg()), w);
    // linear_second: triple(v, u + (-w), w) ≡ triple(v, u, w) + triple(v, -w, w)
    lemma_triple_linear_second::<T>(v, u, w.neg(), w);

    // triple(v, w.neg(), w): neg_second ≡ -triple(v, w, w) ≡ -0 ≡ 0
    lemma_triple_neg_second::<T>(v, w, w);
    lemma_triple_self_zero_23::<T>(v, w);
    T::axiom_neg_congruence(triple(v, w, w), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(
        triple(v, w.neg(), w),
        triple(v, w, w).neg(),
        T::zero().neg(),
    );
    T::axiom_eqv_transitive(
        triple(v, w.neg(), w),
        T::zero().neg(),
        T::zero(),
    );

    // triple(v, u, w) + 0 ≡ triple(v, u, w)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        triple(v, u, w),
        triple(v, w.neg(), w),
        T::zero(),
    );
    T::axiom_add_zero_right(triple(v, u, w));
    T::axiom_eqv_transitive(
        triple(v, u, w).add(triple(v, w.neg(), w)),
        triple(v, u, w).add(T::zero()),
        triple(v, u, w),
    );

    // triple(v, u.add(w.neg()), w) ≡ triple(v, u, w)
    T::axiom_eqv_transitive(
        triple(v, u.add(w.neg()), w),
        triple(v, u, w).add(triple(v, w.neg(), w)),
        triple(v, u, w),
    );
    // triple(v, u.sub(w), w) ≡ triple(v, u, w)
    T::axiom_eqv_transitive(
        triple(v, u.sub(w), w),
        triple(v, u.add(w.neg()), w),
        triple(v, u, w),
    );

    // -triple(v, u.sub(w), w) ≡ -triple(v, u, w)
    T::axiom_neg_congruence(triple(v, u.sub(w), w), triple(v, u, w));
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(v, u.sub(w), w).neg(),
        triple(v, u, w).neg(),
    );

    // Step F: -triple(v, u, w) ≡ triple(u, v, w)
    //   swap_12: triple(v, u, w) ≡ triple(u, v, w).neg()
    //   so -triple(v, u, w) ≡ -(triple(u, v, w).neg()) ≡ triple(u, v, w)
    lemma_triple_swap_12::<T>(v, u, w);
    T::axiom_neg_congruence(triple(v, u, w), triple(u, v, w).neg());
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(v, u, w).neg(),
        triple(u, v, w).neg().neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(triple(u, v, w));
    T::axiom_eqv_transitive(
        orient3d(d, c, b, a),
        triple(u, v, w).neg().neg(),
        triple(u, v, w),
    );
    // triple(u, v, w) = orient3d(a, b, c, d). QED.
}

} // verus!
