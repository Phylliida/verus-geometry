use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec3::ops::{dot};
use crate::point3::*;
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

} // verus!
