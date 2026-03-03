use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::*;
use crate::point2::*;
use crate::point3::*;
use crate::orient2d::*;
use crate::orient3d::{orient3d, lemma_orient3d_swap_cd, lemma_orient3d_swap_bc,
    lemma_orient3d_cycle_bcd, lemma_orient3d_degenerate_ab, lemma_orient3d_degenerate_cd};
use crate::intersection3d::{project_drop_x, project_drop_y, project_drop_z};

verus! {

// =========================================================================
// 2.1 — Collinearity (2D)
// =========================================================================

/// Three 2D points are collinear iff orient2d(a, b, c) ≡ 0.
pub open spec fn collinear2d<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    orient2d(a, b, c).eqv(T::zero())
}

/// collinear2d(a, a, c) always holds (degenerate: a = b).
pub proof fn lemma_collinear2d_degenerate_ab<T: Ring>(a: Point2<T>, c: Point2<T>)
    ensures
        collinear2d(a, a, c),
{
    lemma_orient2d_degenerate_ab::<T>(a, c);
}

/// collinear2d(a, b, b) always holds (degenerate: b = c).
pub proof fn lemma_collinear2d_degenerate_bc<T: Ring>(a: Point2<T>, b: Point2<T>)
    ensures
        collinear2d(a, b, b),
{
    lemma_orient2d_degenerate_bc::<T>(a, b);
}

/// Cyclic permutation: collinear2d(a, b, c) == collinear2d(b, c, a).
pub proof fn lemma_collinear2d_cyclic<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        collinear2d(a, b, c) == collinear2d(b, c, a),
{
    // orient2d(a,b,c) ≡ orient2d(b,c,a) by cyclic lemma
    lemma_orient2d_cyclic::<T>(a, b, c);
    // If orient2d(a,b,c) ≡ 0 then orient2d(b,c,a) ≡ 0 via transitivity
    if collinear2d(a, b, c) {
        // orient2d(b,c,a) ≡ orient2d(a,b,c) (symmetric of cyclic)
        T::axiom_eqv_symmetric(orient2d(a, b, c), orient2d(b, c, a));
        T::axiom_eqv_transitive(orient2d(b, c, a), orient2d(a, b, c), T::zero());
    }
    if collinear2d(b, c, a) {
        T::axiom_eqv_transitive(orient2d(a, b, c), orient2d(b, c, a), T::zero());
    }
}

/// Swap b, c: collinear2d(a, b, c) == collinear2d(a, c, b).
pub proof fn lemma_collinear2d_swap_bc<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        collinear2d(a, b, c) == collinear2d(a, c, b),
{
    // orient2d(a, c, b) ≡ -orient2d(a, b, c) by swap lemma
    lemma_orient2d_swap_bc::<T>(a, b, c);
    if collinear2d(a, b, c) {
        // orient2d(a,b,c) ≡ 0, so -orient2d(a,b,c) ≡ -0 ≡ 0
        T::axiom_neg_congruence(orient2d(a, b, c), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(
            orient2d(a, b, c).neg(), T::zero().neg(), T::zero(),
        );
        T::axiom_eqv_transitive(
            orient2d(a, c, b), orient2d(a, b, c).neg(), T::zero(),
        );
    }
    if collinear2d(a, c, b) {
        // orient2d(a,c,b) ≡ 0 and orient2d(a,c,b) ≡ -orient2d(a,b,c)
        // So -orient2d(a,b,c) ≡ 0, hence orient2d(a,b,c) ≡ -0 ≡ 0
        T::axiom_eqv_symmetric(orient2d(a, c, b), orient2d(a, b, c).neg());
        T::axiom_eqv_transitive(
            orient2d(a, b, c).neg(), orient2d(a, c, b), T::zero(),
        );
        // -val ≡ 0 implies val ≡ 0:
        // neg both sides: --val ≡ -0, involution: val ≡ --val, -0 ≡ 0
        let val = orient2d(a, b, c);
        additive_group_lemmas::lemma_neg_involution::<T>(val);
        T::axiom_eqv_symmetric(val.neg().neg(), val);
        T::axiom_neg_congruence(val.neg(), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(val, val.neg().neg(), T::zero());
    }
}

/// Full permutation invariance: collinear2d is the same for any permutation of a, b, c.
pub proof fn lemma_collinear2d_permutation<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        collinear2d(a, b, c) == collinear2d(a, c, b),
        collinear2d(a, b, c) == collinear2d(b, a, c),
        collinear2d(a, b, c) == collinear2d(b, c, a),
        collinear2d(a, b, c) == collinear2d(c, a, b),
        collinear2d(a, b, c) == collinear2d(c, b, a),
{
    // (a,b,c) == (a,c,b): swap_bc
    lemma_collinear2d_swap_bc::<T>(a, b, c);
    // (a,b,c) == (b,c,a): cyclic
    lemma_collinear2d_cyclic::<T>(a, b, c);
    // (a,b,c) == (c,a,b): cyclic twice: (a,b,c)==(b,c,a)==(c,a,b)
    lemma_collinear2d_cyclic::<T>(b, c, a);
    // (a,b,c) == (b,a,c): cyclic to get (b,c,a), then swap_bc on (b,c,a)
    lemma_collinear2d_swap_bc::<T>(b, c, a);
    // (a,b,c) == (c,b,a): cyclic to get (c,a,b), then swap_bc on (c,a,b)
    lemma_collinear2d_swap_bc::<T>(c, a, b);
}

// =========================================================================
// 2.2 — Collinearity (3D)
// =========================================================================

/// Three 3D points are collinear iff cross(b-a, c-a) ≡ Vec3::zero().
pub open spec fn collinear3d<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    cross(sub3(b, a), sub3(c, a)).eqv(Vec3::<T>::zero())
}

/// Helper: cross(zero_vec, v) ≡ zero_vec.
proof fn lemma_cross_zero_left<T: Ring>(v: Vec3<T>)
    ensures
        cross(Vec3::<T>::zero(), v).eqv(Vec3::<T>::zero()),
{
    let z = Vec3::<T>::zero();
    // cross(z, v).x = z.y*v.z - z.z*v.y = 0*v.z - 0*v.y
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(v.z), T::zero(),
        T::zero().mul(v.y), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(cross(z, v).x, T::zero().sub(T::zero()), T::zero());

    // cross(z, v).y = z.z*v.x - z.x*v.z = 0*v.x - 0*v.z
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(v.x), T::zero(),
        T::zero().mul(v.z), T::zero(),
    );
    T::axiom_eqv_transitive(cross(z, v).y, T::zero().sub(T::zero()), T::zero());

    // cross(z, v).z = z.x*v.y - z.y*v.x = 0*v.y - 0*v.x
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(v.y), T::zero(),
        T::zero().mul(v.x), T::zero(),
    );
    T::axiom_eqv_transitive(cross(z, v).z, T::zero().sub(T::zero()), T::zero());
}

/// collinear3d(a, a, c) always holds (degenerate: a = b).
pub proof fn lemma_collinear3d_degenerate_ab<T: Ring>(a: Point3<T>, c: Point3<T>)
    ensures
        collinear3d(a, a, c),
{
    // sub3(a, a) ≡ zero_vec
    lemma_sub3_self_zero::<T>(a);
    // cross(sub3(a,a), sub3(c,a)) ≡ cross(zero_vec, sub3(c,a)) via congruence
    let z = Vec3::<T>::zero();
    Vec3::<T>::axiom_eqv_reflexive(sub3(c, a));
    lemma_cross_congruence::<T>(sub3(a, a), z, sub3(c, a), sub3(c, a));
    // cross(zero_vec, sub3(c,a)) ≡ zero_vec
    lemma_cross_zero_left::<T>(sub3(c, a));
    Vec3::<T>::axiom_eqv_transitive(
        cross(sub3(a, a), sub3(c, a)),
        cross(z, sub3(c, a)),
        z,
    );
}

/// collinear3d(a, b, b) always holds (degenerate: b = c).
pub proof fn lemma_collinear3d_degenerate_bc<T: Ring>(a: Point3<T>, b: Point3<T>)
    ensures
        collinear3d(a, b, b),
{
    // cross(sub3(b,a), sub3(b,a)) ≡ zero_vec
    lemma_cross_self_zero::<T>(sub3(b, a));
}

/// Swap b, c: collinear3d(a, b, c) == collinear3d(a, c, b).
pub proof fn lemma_collinear3d_swap_bc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        collinear3d(a, b, c) == collinear3d(a, c, b),
{
    let u = cross(sub3(b, a), sub3(c, a));
    let v = cross(sub3(c, a), sub3(b, a));
    let z = Vec3::<T>::zero();

    // anticommutative(c-a, b-a): v ≡ u.neg()
    lemma_cross_anticommutative::<T>(sub3(c, a), sub3(b, a));

    if collinear3d(a, b, c) {
        // u ≡ 0, so u.neg() ≡ 0.neg() ≡ 0 (component-wise)
        T::axiom_neg_congruence(u.x, T::zero());
        T::axiom_neg_congruence(u.y, T::zero());
        T::axiom_neg_congruence(u.z, T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(u.x.neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(u.y.neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(u.z.neg(), T::zero().neg(), T::zero());
        // v ≡ u.neg() ≡ 0
        Vec3::<T>::axiom_eqv_transitive(v, u.neg(), z);
    }
    if collinear3d(a, c, b) {
        // v ≡ 0 and v ≡ u.neg(), so u.neg() ≡ 0
        Vec3::<T>::axiom_eqv_symmetric(v, u.neg());
        Vec3::<T>::axiom_eqv_transitive(u.neg(), v, z);
        // u.neg().x ≡ 0, neg both sides to get u.x ≡ 0
        T::axiom_neg_congruence(u.x.neg(), T::zero());
        T::axiom_neg_congruence(u.y.neg(), T::zero());
        T::axiom_neg_congruence(u.z.neg(), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(u.x.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(u.y.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(u.z.neg().neg(), T::zero().neg(), T::zero());
        additive_group_lemmas::lemma_neg_involution::<T>(u.x);
        additive_group_lemmas::lemma_neg_involution::<T>(u.y);
        additive_group_lemmas::lemma_neg_involution::<T>(u.z);
        T::axiom_eqv_symmetric(u.x.neg().neg(), u.x);
        T::axiom_eqv_symmetric(u.y.neg().neg(), u.y);
        T::axiom_eqv_symmetric(u.z.neg().neg(), u.z);
        T::axiom_eqv_transitive(u.x, u.x.neg().neg(), T::zero());
        T::axiom_eqv_transitive(u.y, u.y.neg().neg(), T::zero());
        T::axiom_eqv_transitive(u.z, u.z.neg().neg(), T::zero());
    }
}

// =========================================================================
// 2.3 — Coplanarity
// =========================================================================

/// Four 3D points are coplanar iff orient3d(a, b, c, d) ≡ 0.
pub open spec fn coplanar<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> bool {
    orient3d(a, b, c, d).eqv(T::zero())
}

/// coplanar(a, a, c, d) always holds (degenerate: a = b).
pub proof fn lemma_coplanar_degenerate_ab<T: Ring>(
    a: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        coplanar(a, a, c, d),
{
    lemma_orient3d_degenerate_ab::<T>(a, c, d);
}

/// coplanar(a, b, c, c) always holds (degenerate: c = d).
pub proof fn lemma_coplanar_degenerate_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        coplanar(a, b, c, c),
{
    lemma_orient3d_degenerate_cd::<T>(a, b, c);
}

/// Swap c, d: coplanar(a, b, c, d) == coplanar(a, b, d, c).
pub proof fn lemma_coplanar_swap_cd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        coplanar(a, b, c, d) == coplanar(a, b, d, c),
{
    // orient3d(a,b,d,c) ≡ -orient3d(a,b,c,d)
    lemma_orient3d_swap_cd::<T>(a, b, c, d);
    let val = orient3d(a, b, c, d);
    let swapped = orient3d(a, b, d, c);
    if coplanar(a, b, c, d) {
        T::axiom_neg_congruence(val, T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val.neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(swapped, val.neg(), T::zero());
    }
    if coplanar(a, b, d, c) {
        T::axiom_eqv_symmetric(swapped, val.neg());
        T::axiom_eqv_transitive(val.neg(), swapped, T::zero());
        additive_group_lemmas::lemma_neg_involution::<T>(val);
        T::axiom_eqv_symmetric(val.neg().neg(), val);
        T::axiom_neg_congruence(val.neg(), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(val, val.neg().neg(), T::zero());
    }
}

/// Swap b, c: coplanar(a, b, c, d) == coplanar(a, c, b, d).
pub proof fn lemma_coplanar_swap_bc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        coplanar(a, b, c, d) == coplanar(a, c, b, d),
{
    lemma_orient3d_swap_bc::<T>(a, b, c, d);
    let val = orient3d(a, b, c, d);
    let swapped = orient3d(a, c, b, d);
    if coplanar(a, b, c, d) {
        T::axiom_neg_congruence(val, T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val.neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(swapped, val.neg(), T::zero());
    }
    if coplanar(a, c, b, d) {
        T::axiom_eqv_symmetric(swapped, val.neg());
        T::axiom_eqv_transitive(val.neg(), swapped, T::zero());
        additive_group_lemmas::lemma_neg_involution::<T>(val);
        T::axiom_eqv_symmetric(val.neg().neg(), val);
        T::axiom_neg_congruence(val.neg(), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(val, val.neg().neg(), T::zero());
    }
}

/// Cyclic permutation of b, c, d: coplanar(a, b, c, d) == coplanar(a, c, d, b).
pub proof fn lemma_coplanar_cycle_bcd<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        coplanar(a, b, c, d) == coplanar(a, c, d, b),
{
    // orient3d(a,c,d,b) ≡ orient3d(a,b,c,d) by cycle_bcd
    lemma_orient3d_cycle_bcd::<T>(a, b, c, d);
    if coplanar(a, b, c, d) {
        T::axiom_eqv_symmetric(orient3d(a, b, c, d), orient3d(a, c, d, b));
        T::axiom_eqv_transitive(orient3d(a, c, d, b), orient3d(a, b, c, d), T::zero());
    }
    if coplanar(a, c, d, b) {
        // cycle_bcd gives orient3d(a,c,d,b).eqv(orient3d(a,b,c,d))
        // Need orient3d(a,b,c,d).eqv(orient3d(a,c,d,b)) for transitive
        T::axiom_eqv_symmetric(orient3d(a, c, d, b), orient3d(a, b, c, d));
        T::axiom_eqv_transitive(orient3d(a, b, c, d), orient3d(a, c, d, b), T::zero());
    }
}

/// Any three points are coplanar with themselves: coplanar(a, b, c, a).
pub proof fn lemma_coplanar_three_points_a<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        coplanar(a, b, c, a),
{
    // orient3d(a, b, c, a) = triple(b-a, c-a, a-a) = triple(b-a, c-a, 0) ≡ 0
    // Use triple_self_zero_23 won't work directly. Let's use the degenerate approach:
    // orient3d(a, b, c, a): d = a, so sub3(d, a) = sub3(a, a) ≡ zero_vec
    // triple(b-a, c-a, zero_vec) = dot(b-a, cross(c-a, zero_vec))
    // cross(c-a, zero_vec) = -cross(zero_vec, c-a) ≡ -zero_vec ≡ zero_vec
    // dot(b-a, zero_vec) ≡ 0

    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let aa = sub3(a, a);
    let z = Vec3::<T>::zero();

    // aa ≡ z
    lemma_sub3_self_zero::<T>(a);

    // We need triple(ba, ca, aa) ≡ 0
    // triple(ba, ca, aa) = dot(ba, cross(ca, aa))
    // cross(ca, aa) ≡ cross(ca, z) by congruence
    Vec3::<T>::axiom_eqv_reflexive(ca);
    lemma_cross_congruence::<T>(ca, ca, aa, z);
    // cross(ca, z): use anticommutative with cross_zero_left
    // cross(ca, z) ≡ -cross(z, ca)
    lemma_cross_anticommutative::<T>(z, ca);
    // cross(z, ca) ≡ z by cross_zero_left
    lemma_cross_zero_left::<T>(ca);
    // -cross(z, ca) ≡ -z ≡ z
    Vec3::<T>::axiom_eqv_symmetric(cross(z, ca), z.neg());
    // cross(ca, z) ≡ -cross(z, ca), and -cross(z, ca) needs to be z
    // Actually cross_anticommutative gives: cross(z, ca) ≡ cross(ca, z).neg()
    // So cross(ca, z).neg() ≡ cross(z, ca) ≡ z (by cross_zero_left)
    // Hence cross(ca, z) ≡ ... let me use a cleaner approach

    // cross(z, ca) ≡ z (by cross_zero_left)
    // cross(z, ca) ≡ -cross(ca, z) (by anticommutative)
    // So -cross(ca, z) ≡ z
    // Hence cross(ca, z) ≡ -z ≡ z (via neg_zero componentwise)
    lemma_cross_anticommutative::<T>(ca, z);
    // cross(ca, z) ≡ cross(z, ca).neg()
    // cross(z, ca) ≡ z, so cross(z, ca).neg() ≡ z.neg()
    Vec3::<T>::axiom_eqv_reflexive(z);
    // We need cross(ca, z).neg() ... let me just use a simpler path

    // cross(ca, aa): we have cross(ca, aa) ≡ cross(ca, z) from congruence above
    // Now prove cross(ca, z) ≡ z directly component-by-component
    // cross(ca, z).x = ca.y * 0 - ca.z * 0 = 0 - 0 = 0
    T::axiom_mul_zero_right(ca.y);
    T::axiom_mul_zero_right(ca.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        ca.y.mul(T::zero()), T::zero(),
        ca.z.mul(T::zero()), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(cross(ca, z).x, T::zero().sub(T::zero()), T::zero());

    // cross(ca, z).y = ca.z * 0 - ca.x * 0 = 0 - 0 = 0
    T::axiom_mul_zero_right(ca.z);
    T::axiom_mul_zero_right(ca.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        ca.z.mul(T::zero()), T::zero(),
        ca.x.mul(T::zero()), T::zero(),
    );
    T::axiom_eqv_transitive(cross(ca, z).y, T::zero().sub(T::zero()), T::zero());

    // cross(ca, z).z = ca.x * 0 - ca.y * 0 = 0 - 0 = 0
    T::axiom_mul_zero_right(ca.x);
    T::axiom_mul_zero_right(ca.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        ca.x.mul(T::zero()), T::zero(),
        ca.y.mul(T::zero()), T::zero(),
    );
    T::axiom_eqv_transitive(cross(ca, z).z, T::zero().sub(T::zero()), T::zero());

    // cross(ca, z) ≡ z
    // cross(ca, aa) ≡ cross(ca, z) ≡ z
    Vec3::<T>::axiom_eqv_transitive(cross(ca, aa), cross(ca, z), z);

    // triple(ba, ca, aa) = dot(ba, cross(ca, aa))
    // dot(ba, cross(ca, aa)) ≡ dot(ba, z) via dot congruence
    Vec3::<T>::axiom_eqv_reflexive(ba);
    lemma_dot_congruence::<T>(ba, ba, cross(ca, aa), z);
    // dot(ba, z) ≡ 0
    lemma_dot_zero_right::<T>(ba);
    T::axiom_eqv_transitive(
        orient3d(a, b, c, a),
        dot(ba, z),
        T::zero(),
    );
}

/// Any three points are coplanar with themselves: coplanar(a, b, c, b).
pub proof fn lemma_coplanar_three_points_b<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        coplanar(a, b, c, b),
{
    // orient3d(a, b, c, b) = triple(b-a, c-a, b-a)
    // triple_self_zero_13: triple(x, y, x) ≡ 0
    lemma_triple_self_zero_13::<T>(sub3(b, a), sub3(c, a));
}

/// Any three points are coplanar with themselves: coplanar(a, b, c, c).
pub proof fn lemma_coplanar_three_points_c<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        coplanar(a, b, c, c),
{
    lemma_orient3d_degenerate_cd::<T>(a, b, c);
}

// =========================================================================
// Cross-predicate lemma: collinear3d implies coplanar
// =========================================================================

/// If three points are collinear in 3D, they are coplanar with any fourth point.
///
/// Proof: collinear3d(a,b,c) means cross(b-a, c-a) ≡ 0.
/// orient3d(a,b,c,d) = triple(b-a, c-a, d-a) = dot(d-a, cross(b-a, c-a))
/// (via cyclic property of triple product), so dot(d-a, 0) ≡ 0.
pub proof fn lemma_collinear3d_implies_coplanar<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    requires
        collinear3d(a, b, c),
    ensures
        coplanar(a, b, c, d),
{
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let da = sub3(d, a);
    let z = Vec3::<T>::zero();

    // collinear3d(a,b,c) gives: cross(ba, ca) ≡ z
    // orient3d(a,b,c,d) = triple(ba, ca, da)

    // Step 1: triple(ba, ca, da) ≡ triple(ca, da, ba)  [cyclic]
    lemma_triple_cyclic::<T>(ba, ca, da);

    // Step 2: triple(ca, da, ba) ≡ triple(da, ba, ca)  [cyclic]
    lemma_triple_cyclic::<T>(ca, da, ba);

    // Step 3: chain — triple(ba, ca, da) ≡ triple(da, ba, ca)
    T::axiom_eqv_transitive(
        triple(ba, ca, da),
        triple(ca, da, ba),
        triple(da, ba, ca),
    );

    // Step 4: triple(da, ba, ca) = dot(da, cross(ba, ca))
    // cross(ba, ca) ≡ z (from collinear3d)
    // dot_congruence: dot(da, cross(ba, ca)) ≡ dot(da, z)
    Vec3::<T>::axiom_eqv_reflexive(da);
    lemma_dot_congruence::<T>(da, da, cross(ba, ca), z);

    // Step 5: dot(da, z) ≡ 0
    lemma_dot_zero_right::<T>(da);

    // Chain: orient3d(a,b,c,d) = triple(ba, ca, da)
    //   ≡ triple(da, ba, ca) = dot(da, cross(ba, ca))
    //   ≡ dot(da, z) ≡ 0
    T::axiom_eqv_transitive(
        triple(ba, ca, da),
        triple(da, ba, ca),
        dot(da, z),
    );
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d),
        dot(da, z),
        T::zero(),
    );
}

// =========================================================================
// Collinear3d implies all 2D projections are collinear
// =========================================================================

/// collinear3d(a, b, c) implies collinear2d on the drop-z projection.
///
/// orient2d(pz_a, pz_b, pz_c) is syntactically the same expression as
/// cross(sub3(b,a), sub3(c,a)).z after unfolding all open spec fns.
pub proof fn lemma_collinear3d_implies_collinear2d_drop_z<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        collinear3d(a, b, c),
    ensures
        collinear2d(project_drop_z(a), project_drop_z(b), project_drop_z(c)),
{
    // collinear3d gives cross(sub3(b,a), sub3(c,a)) ≡ Vec3::zero()
    // so cross.z ≡ 0.
    // orient2d(pz_a, pz_b, pz_c) unfolds to the same term as cross.z.
}

/// collinear3d(a, b, c) implies collinear2d on the drop-x projection.
///
/// orient2d(px_a, px_b, px_c) is syntactically the same expression as
/// cross(sub3(b,a), sub3(c,a)).x after unfolding.
pub proof fn lemma_collinear3d_implies_collinear2d_drop_x<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        collinear3d(a, b, c),
    ensures
        collinear2d(project_drop_x(a), project_drop_x(b), project_drop_x(c)),
{
    // cross.x ≡ 0, and orient2d of drop_x projection IS cross.x.
}

/// collinear3d(a, b, c) implies collinear2d on the drop-y projection.
///
/// orient2d(py_a, py_b, py_c) = A.sub(B) while cross.y = B.sub(A).
/// By sub_antisymmetric: A.sub(B) ≡ -(B.sub(A)) = -(cross.y) ≡ -0 ≡ 0.
pub proof fn lemma_collinear3d_implies_collinear2d_drop_y<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        collinear3d(a, b, c),
    ensures
        collinear2d(project_drop_y(a), project_drop_y(b), project_drop_y(c)),
{
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    // orient2d(py_a, py_b, py_c) = ba.x*ca.z - ba.z*ca.x  (after unfolding)
    // cross(ba, ca).y            = ba.z*ca.x - ba.x*ca.z  (after unfolding)
    // These differ by sign: orient2d = -(cross.y) via sub_antisymmetric.
    let big_a = ba.x.mul(ca.z);
    let big_b = ba.z.mul(ca.x);
    // sub_antisymmetric: A.sub(B) ≡ B.sub(A).neg()
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(big_a, big_b);
    // orient2d ≡ -(cross.y)
    // collinear3d gives cross.y ≡ 0
    // -(cross.y) ≡ -(0) ≡ 0
    T::axiom_neg_congruence(cross(ba, ca).y, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(cross(ba, ca).y.neg(), T::zero().neg(), T::zero());
    // orient2d = A.sub(B) ≡ B.sub(A).neg() = cross.y.neg() ≡ 0
    T::axiom_eqv_transitive(
        orient2d(project_drop_y(a), project_drop_y(b), project_drop_y(c)),
        cross(ba, ca).y.neg(),
        T::zero(),
    );
}

/// collinear3d(a, b, c) implies all three 2D projections are collinear.
pub proof fn lemma_collinear3d_implies_all_projections_collinear<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        collinear3d(a, b, c),
    ensures
        collinear2d(project_drop_x(a), project_drop_x(b), project_drop_x(c)),
        collinear2d(project_drop_y(a), project_drop_y(b), project_drop_y(c)),
        collinear2d(project_drop_z(a), project_drop_z(b), project_drop_z(c)),
{
    lemma_collinear3d_implies_collinear2d_drop_x::<T>(a, b, c);
    lemma_collinear3d_implies_collinear2d_drop_y::<T>(a, b, c);
    lemma_collinear3d_implies_collinear2d_drop_z::<T>(a, b, c);
}

} // verus!
