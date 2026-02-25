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

} // verus!
