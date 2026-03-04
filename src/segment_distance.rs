use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{dot, scale, norm_sq};
use crate::point3::*;

verus! {

// =========================================================================
// Line-line closest approach specs
// =========================================================================

/// Point on the line through a and b at parameter t: a + t*(b - a).
pub open spec fn line_point_3d<T: Ring>(
    a: Point3<T>, b: Point3<T>, t: T,
) -> Point3<T> {
    add_vec3(a, scale(t, sub3(b, a)))
}

/// The Gram matrix entries for lines (a,b) and (c,d).
/// u = b-a, v = d-c, w = a-c.
/// Returns (dot(u,u), dot(v,v), dot(u,v), dot(u,w), dot(v,w)).
pub open spec fn gram_entries<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> (T, T, T, T, T) {
    let u = sub3(b, a);
    let v = sub3(d, c);
    let w = sub3(a, c);
    (dot(u, u), dot(v, v), dot(u, v), dot(u, w), dot(v, w))
}

/// Denominator of the closest-approach system: |u|²|v|² - (u·v)².
/// This is zero iff the lines are parallel.
pub open spec fn gram_determinant<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (uu, vv, uv, _, _) = gram_entries(a, b, c, d);
    uu.mul(vv).sub(uv.mul(uv))
}

/// Closest-approach parameter on line (a,b):
/// s = (uv * vw - vv * uw) / denom
pub open spec fn closest_parameter_s<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (_, vv, uv, uw, vw) = gram_entries(a, b, c, d);
    let denom = gram_determinant(a, b, c, d);
    uv.mul(vw).sub(vv.mul(uw)).div(denom)
}

/// Closest-approach parameter on line (c,d):
/// t = (uu * vw - uv * uw) / denom
pub open spec fn closest_parameter_t<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (uu, _, uv, uw, vw) = gram_entries(a, b, c, d);
    let denom = gram_determinant(a, b, c, d);
    uu.mul(vw).sub(uv.mul(uw)).div(denom)
}

/// Squared distance between the closest approach points on two lines.
pub open spec fn line_line_squared_distance<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let s = closest_parameter_s(a, b, c, d);
    let t = closest_parameter_t(a, b, c, d);
    let p1 = line_point_3d(a, b, s);
    let p2 = line_point_3d(c, d, t);
    norm_sq(sub3(p1, p2))
}

} // verus!
