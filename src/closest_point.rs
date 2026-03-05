use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::{dot as dot2, norm_sq as norm_sq2, scale as scale2};
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{dot as dot3, norm_sq as norm_sq3, scale as scale3};
use crate::point2::*;
use crate::point3::*;

verus! {

// ---------------------------------------------------------------------------
// Clamp to [0, 1]
// ---------------------------------------------------------------------------

/// Clamp a scalar to the interval [0, 1].
pub open spec fn clamp01<T: OrderedRing>(t: T) -> T {
    if t.le(T::zero()) {
        T::zero()
    } else if T::one().le(t) {
        T::one()
    } else {
        t
    }
}

/// clamp01 always returns a value in [0, 1].
pub proof fn lemma_clamp01_bounds<T: OrderedRing>(t: T)
    ensures
        T::zero().le(clamp01(t)),
        clamp01(t).le(T::one()),
{
    // 0 < 1, so 0 ≤ 1
    ordered_ring_lemmas::lemma_zero_lt_one::<T>();
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), T::one());
    // Now: T::zero().le(T::one())

    if t.le(T::zero()) {
        // clamp01(t) = zero
        T::axiom_le_reflexive(T::zero());
        // 0 ≤ 0 ✓, 0 ≤ 1 ✓
    } else if T::one().le(t) {
        // clamp01(t) = one
        T::axiom_le_reflexive(T::one());
        // 0 ≤ 1 ✓, 1 ≤ 1 ✓
    } else {
        // clamp01(t) = t, ¬(t ≤ 0) and ¬(1 ≤ t)
        // By totality: 0 ≤ t (since ¬(t ≤ 0) → 0 ≤ t by total order)
        T::axiom_le_total(T::zero(), t);
        // By totality: t ≤ 1 (since ¬(1 ≤ t) → t ≤ 1 by total order)
        T::axiom_le_total(t, T::one());
    }
}

// ---------------------------------------------------------------------------
// 2D: Point-segment closest point
// ---------------------------------------------------------------------------

/// Unclamped projection parameter of q onto line through a, b.
/// t = dot(q - a, b - a) / norm_sq(b - a)
pub open spec fn segment_project_parameter_2d<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> T
    recommends !norm_sq2(sub2(b, a)).eqv(T::zero()),
{
    let d = sub2(b, a);
    let w = sub2(q, a);
    dot2(w, d).div(norm_sq2(d))
}

/// Clamped parameter for closest point on segment [a, b] to query q.
pub open spec fn closest_parameter_2d<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> T
    recommends !norm_sq2(sub2(b, a)).eqv(T::zero()),
{
    clamp01(segment_project_parameter_2d(q, a, b))
}

/// Closest point on segment [a, b] to query point q.
/// Returns a + clamp01(t) * (b - a).
pub open spec fn closest_point_on_segment_2d<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> Point2<T>
    recommends !norm_sq2(sub2(b, a)).eqv(T::zero()),
{
    let t = closest_parameter_2d(q, a, b);
    add_vec2(a, scale2(t, sub2(b, a)))
}

/// Squared distance from point q to segment [a, b].
pub open spec fn squared_distance_point_segment_2d<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> T
    recommends !norm_sq2(sub2(b, a)).eqv(T::zero()),
{
    let cp = closest_point_on_segment_2d(q, a, b);
    norm_sq2(sub2(cp, q))
}

// ---------------------------------------------------------------------------
// 3D: Point-segment closest point
// ---------------------------------------------------------------------------

/// Unclamped projection parameter of q onto line through a, b.
/// t = dot(q - a, b - a) / norm_sq(b - a)
pub open spec fn segment_project_parameter_3d<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>,
) -> T
    recommends !norm_sq3(sub3(b, a)).eqv(T::zero()),
{
    let d = sub3(b, a);
    let w = sub3(q, a);
    dot3(w, d).div(norm_sq3(d))
}

/// Clamped parameter for closest point on segment [a, b] to query q.
pub open spec fn closest_parameter_3d<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>,
) -> T
    recommends !norm_sq3(sub3(b, a)).eqv(T::zero()),
{
    clamp01(segment_project_parameter_3d(q, a, b))
}

/// Closest point on segment [a, b] to query point q.
/// Returns a + clamp01(t) * (b - a).
pub open spec fn closest_point_on_segment_3d<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>,
) -> Point3<T>
    recommends !norm_sq3(sub3(b, a)).eqv(T::zero()),
{
    let t = closest_parameter_3d(q, a, b);
    add_vec3(a, scale3(t, sub3(b, a)))
}

/// Squared distance from point q to segment [a, b].
pub open spec fn squared_distance_point_segment_3d<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>,
) -> T
    recommends !norm_sq3(sub3(b, a)).eqv(T::zero()),
{
    let cp = closest_point_on_segment_3d(q, a, b);
    norm_sq3(sub3(cp, q))
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// The closest parameter is in [0, 1].
pub proof fn lemma_closest_parameter_2d_bounds<T: OrderedField>(
    q: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    requires
        !norm_sq2(sub2(b, a)).eqv(T::zero()),
    ensures
        T::zero().le(closest_parameter_2d(q, a, b)),
        closest_parameter_2d(q, a, b).le(T::one()),
{
    lemma_clamp01_bounds::<T>(segment_project_parameter_2d(q, a, b));
}

/// The closest parameter is in [0, 1].
pub proof fn lemma_closest_parameter_3d_bounds<T: OrderedField>(
    q: Point3<T>, a: Point3<T>, b: Point3<T>,
)
    requires
        !norm_sq3(sub3(b, a)).eqv(T::zero()),
    ensures
        T::zero().le(closest_parameter_3d(q, a, b)),
        closest_parameter_3d(q, a, b).le(T::one()),
{
    lemma_clamp01_bounds::<T>(segment_project_parameter_3d(q, a, b));
}

} // verus!
