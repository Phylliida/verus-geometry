use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec3::ops::{dot};
use crate::point3::*;
use crate::orient3d::orient3d;
use crate::orientation_sign::*;
use crate::intersection3d::triangle_normal;

verus! {

// =========================================================================
// Face normal lemmas
// =========================================================================

/// The normal of a triangle is orthogonal to both edges.
/// dot(normal, b - a) ≡ 0 and dot(normal, c - a) ≡ 0.
pub proof fn lemma_normal_orthogonal_to_edges<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        dot(triangle_normal(a, b, c), sub3(b, a)).eqv(T::zero()),
        dot(triangle_normal(a, b, c), sub3(c, a)).eqv(T::zero()),
{
    let u = sub3(b, a);
    let v = sub3(c, a);
    // triangle_normal = cross(u, v)
    // dot(cross(u,v), u) ≡ 0 [cross orthogonal to left]
    verus_linalg::vec3::ops::lemma_cross_orthogonal_left::<T>(u, v);
    // dot(cross(u,v), v) ≡ 0 [cross orthogonal to right]
    verus_linalg::vec3::ops::lemma_cross_orthogonal_right::<T>(u, v);
}

/// Swapping b and c negates the normal.
/// triangle_normal(a, c, b) ≡ -triangle_normal(a, b, c)
pub proof fn lemma_normal_swap_bc<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        triangle_normal(a, c, b).eqv(triangle_normal(a, b, c).neg()),
{
    let u = sub3(b, a);
    let v = sub3(c, a);
    // triangle_normal(a,b,c) = cross(u, v)
    // triangle_normal(a,c,b) = cross(v, u)
    // cross(v, u) ≡ -cross(u, v)  [anticommutative]
    verus_linalg::vec3::ops::lemma_cross_anticommutative::<T>(v, u);
}

// =========================================================================
// Consistent face orientation
// =========================================================================

/// Two adjacent triangles sharing edge (b, c) have consistent orientation
/// if their normals point "the same way."
/// Triangle (a, b, c) and (d, c, b) share edge (b, c).
/// Consistent if d is on the positive side of plane(a, b, c).
pub open spec fn faces_consistently_oriented<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> bool {
    orient3d_positive(a, b, c, d)
}

/// Consistent face orientation is symmetric:
/// if d is above plane(a,b,c), then a is above plane(d,c,b).
///
/// Proof requires: orient3d(a,b,c,d) ≡ orient3d(d,c,b,a)
/// which follows from the even permutation (a,b,c,d) → (d,c,b,a)
/// = (1 4)(2 3) being a product of two transpositions.
/// The proof needs orient3d swap_ab or a full permutation lemma
/// that is not yet available in orient3d.rs.
pub proof fn lemma_consistent_orientation_symmetric<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    requires
        faces_consistently_oriented(a, b, c, d),
    ensures
        faces_consistently_oriented(d, c, b, a),
{
    // faces_consistently_oriented = orient3d_positive = 0.lt(orient3d(...))
    // Key: orient3d(d,c,b,a) ≡ orient3d(a,b,c,d) [even permutation]
    crate::orient3d::lemma_orient3d_even_perm_dcba::<T>(a, b, c, d);
    T::axiom_eqv_symmetric(orient3d(d, c, b, a), orient3d(a, b, c, d));
    let val_abcd = orient3d(a, b, c, d);
    let val_dcba = orient3d(d, c, b, a);

    // Decompose: 0 < val_abcd iff 0 <= val_abcd && !0.eqv(val_abcd)
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), val_abcd);

    // le congruence: 0 <= val_abcd && val_abcd ≡ val_dcba => 0 <= val_dcba
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        T::zero(), val_abcd, val_dcba,
    );

    // !eqv: if 0 ≡ val_dcba, by transitivity with val_dcba ≡ val_abcd: 0 ≡ val_abcd, contradiction
    assert(!T::zero().eqv(val_dcba)) by {
        if T::zero().eqv(val_dcba) {
            T::axiom_eqv_transitive(T::zero(), val_dcba, val_abcd);
        }
    };

    // Reassemble: 0 <= val_dcba && !0.eqv(val_dcba) => 0 < val_dcba
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), val_dcba);
}

} // verus!
