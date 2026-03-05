use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{cross, dot};
use crate::point3::*;

verus! {

// ---------------------------------------------------------------------------
// Möller-Trumbore ray-triangle intersection
// ---------------------------------------------------------------------------

/// Edge vectors of the triangle.
pub open spec fn edge1<T: Ring>(v0: Point3<T>, v1: Point3<T>) -> Vec3<T> {
    sub3(v1, v0)
}

pub open spec fn edge2<T: Ring>(v0: Point3<T>, v2: Point3<T>) -> Vec3<T> {
    sub3(v2, v0)
}

/// Determinant for ray-triangle test: dot(edge1, cross(dir, edge2)).
/// This is the scalar triple product of (edge1, dir, edge2).
/// Zero means the ray is parallel to the triangle plane.
pub open spec fn ray_tri_det<T: Ring>(
    dir: Vec3<T>, v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T {
    let e1 = edge1(v0, v1);
    let e2 = edge2(v0, v2);
    let p = cross(dir, e2);
    dot(e1, p)
}

/// Barycentric u coordinate (unnormalized): dot(T, P) where T = origin - v0,
/// P = cross(dir, edge2). Divide by det to get actual u.
pub open spec fn ray_tri_u_unnorm<T: Ring>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T {
    let e2 = edge2(v0, v2);
    let p = cross(dir, e2);
    let tvec = sub3(origin, v0);
    dot(tvec, p)
}

/// Barycentric v coordinate (unnormalized): dot(dir, Q) where Q = cross(T, edge1).
/// Divide by det to get actual v.
pub open spec fn ray_tri_v_unnorm<T: Ring>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T {
    let e1 = edge1(v0, v1);
    let tvec = sub3(origin, v0);
    let q = cross(tvec, e1);
    dot(dir, q)
}

/// Ray parameter t (unnormalized): dot(edge2, Q). Divide by det to get actual t.
pub open spec fn ray_tri_t_unnorm<T: Ring>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T {
    let e1 = edge1(v0, v1);
    let e2 = edge2(v0, v2);
    let tvec = sub3(origin, v0);
    let q = cross(tvec, e1);
    dot(e2, q)
}

/// Normalized barycentric u: u_unnorm / det.
pub open spec fn ray_tri_u<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T
    recommends !ray_tri_det(dir, v0, v1, v2).eqv(T::zero()),
{
    ray_tri_u_unnorm(origin, dir, v0, v1, v2)
        .div(ray_tri_det(dir, v0, v1, v2))
}

/// Normalized barycentric v: v_unnorm / det.
pub open spec fn ray_tri_v<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T
    recommends !ray_tri_det(dir, v0, v1, v2).eqv(T::zero()),
{
    ray_tri_v_unnorm(origin, dir, v0, v1, v2)
        .div(ray_tri_det(dir, v0, v1, v2))
}

/// Normalized ray parameter t: t_unnorm / det.
pub open spec fn ray_tri_t<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> T
    recommends !ray_tri_det(dir, v0, v1, v2).eqv(T::zero()),
{
    ray_tri_t_unnorm(origin, dir, v0, v1, v2)
        .div(ray_tri_det(dir, v0, v1, v2))
}

/// Ray (origin + t*dir, t ≥ 0) hits triangle (v0, v1, v2).
///
/// Uses Möller-Trumbore: computes barycentric (u, v) and ray parameter t.
/// Hit iff: det ≢ 0, u ≥ 0, v ≥ 0, u + v ≤ 1, t ≥ 0.
pub open spec fn ray_hits_triangle<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> bool {
    let det = ray_tri_det(dir, v0, v1, v2);
    if det.eqv(T::zero()) {
        false
    } else {
        let u = ray_tri_u(origin, dir, v0, v1, v2);
        let v = ray_tri_v(origin, dir, v0, v1, v2);
        let t = ray_tri_t(origin, dir, v0, v1, v2);
        T::zero().le(u) && T::zero().le(v) && u.add(v).le(T::one()) && T::zero().le(t)
    }
}

// ---------------------------------------------------------------------------
// Alternative: sign-based test avoiding division
// ---------------------------------------------------------------------------

/// Ray-triangle hit test using sign comparisons, avoiding division.
///
/// Instead of dividing by det, we multiply the bounds by det and flip
/// inequalities when det < 0. This avoids requiring OrderedField.
///
/// Equivalent to `ray_hits_triangle` when both are defined.
pub open spec fn ray_hits_triangle_nodiv<T: OrderedRing>(
    origin: Point3<T>, dir: Vec3<T>,
    v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
) -> bool {
    let det = ray_tri_det(dir, v0, v1, v2);
    let u = ray_tri_u_unnorm(origin, dir, v0, v1, v2);
    let v = ray_tri_v_unnorm(origin, dir, v0, v1, v2);
    let t = ray_tri_t_unnorm(origin, dir, v0, v1, v2);

    if det.eqv(T::zero()) {
        false
    } else if T::zero().lt(det) {
        // det > 0: u ≥ 0, v ≥ 0, u + v ≤ det, t ≥ 0
        T::zero().le(u) && T::zero().le(v) && u.add(v).le(det) && T::zero().le(t)
    } else {
        // det < 0: u ≤ 0, v ≤ 0, u + v ≥ det, t ≤ 0
        u.le(T::zero()) && v.le(T::zero()) && det.le(u.add(v)) && t.le(T::zero())
    }
}

} // verus!
