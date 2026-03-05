use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::scale as scale3;
use crate::point3::*;
use crate::point2::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::scale as scale2;

verus! {

// ---------------------------------------------------------------------------
// Ray definitions
// ---------------------------------------------------------------------------

/// A point on a 3D ray: origin + t * dir
pub open spec fn ray_point_3d<T: Ring>(
    origin: Point3<T>, dir: Vec3<T>, t: T,
) -> Point3<T> {
    add_vec3(origin, scale3(t, dir))
}

/// A point on a 2D ray: origin + t * dir
pub open spec fn ray_point_2d<T: Ring>(
    origin: Point2<T>, dir: Vec2<T>, t: T,
) -> Point2<T> {
    add_vec2(origin, scale2(t, dir))
}

// ---------------------------------------------------------------------------
// Ray-AABB intersection (3D)
// ---------------------------------------------------------------------------

/// Per-axis slab test result for a single axis.
/// Given axis offset bounds [lo, hi] (lo = min_c - origin_c, hi = max_c - origin_c)
/// and direction component dir_c:
///
/// - If dir_c > 0: ray enters slab at t = lo/dir_c, exits at t = hi/dir_c
/// - If dir_c < 0: ray enters slab at t = hi/dir_c, exits at t = lo/dir_c
/// - If dir_c ≡ 0: ray is parallel; hits slab iff lo ≤ 0 ≤ hi

/// Is the ray parallel to this axis and outside the slab?
/// (dir_c ≡ 0 and origin is outside [min_c, max_c])
pub open spec fn axis_parallel_miss<T: OrderedRing>(
    origin_c: T, dir_c: T, min_c: T, max_c: T,
) -> bool {
    dir_c.eqv(T::zero()) && (origin_c.lt(min_c) || max_c.lt(origin_c))
}

/// For a non-parallel axis, the t value where the ray enters the slab.
/// If dir > 0: t_near = (min - origin) / dir
/// If dir < 0: t_near = (max - origin) / dir
pub open spec fn slab_t_near<T: OrderedField>(
    origin_c: T, dir_c: T, min_c: T, max_c: T,
) -> T
    recommends !dir_c.eqv(T::zero()),
{
    if T::zero().lt(dir_c) {
        min_c.sub(origin_c).div(dir_c)
    } else {
        max_c.sub(origin_c).div(dir_c)
    }
}

/// For a non-parallel axis, the t value where the ray exits the slab.
/// If dir > 0: t_far = (max - origin) / dir
/// If dir < 0: t_far = (min - origin) / dir
pub open spec fn slab_t_far<T: OrderedField>(
    origin_c: T, dir_c: T, min_c: T, max_c: T,
) -> T
    recommends !dir_c.eqv(T::zero()),
{
    if T::zero().lt(dir_c) {
        max_c.sub(origin_c).div(dir_c)
    } else {
        min_c.sub(origin_c).div(dir_c)
    }
}

/// Ray-AABB intersection test (3D) via slab method.
///
/// Returns true iff the ray (origin + t*dir, t ≥ 0) hits the AABB [min, max].
///
/// Algorithm:
/// 1. For each axis where dir != 0, compute [t_near, t_far].
/// 2. Track the intersection of all per-axis intervals.
/// 3. Check that the final interval overlaps [0, ∞).
/// 4. If any axis has dir = 0 and origin outside slab, return false.
pub open spec fn ray_hits_aabb3<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    aabb_min: Point3<T>, aabb_max: Point3<T>,
) -> bool {
    // If any parallel axis misses, ray doesn't hit
    if axis_parallel_miss(origin.x, dir.x, aabb_min.x, aabb_max.x)
        || axis_parallel_miss(origin.y, dir.y, aabb_min.y, aabb_max.y)
        || axis_parallel_miss(origin.z, dir.z, aabb_min.z, aabb_max.z)
    {
        false
    } else {
        // Collect t_near / t_far for non-parallel axes
        // t_enter = max of all t_nears (and 0 for the t≥0 constraint)
        // t_exit = min of all t_fars
        // Hit iff t_enter ≤ t_exit

        // Start with t_enter = 0 (ray parameter must be ≥ 0)
        // Start with t_exit = +∞ (we'll use a large bound, or track individually)

        // For axes with dir != 0, update t_enter and t_exit
        // For axes with dir == 0 (but origin in slab), no constraint on t

        // We compute via conditional max/min of the non-parallel axes
        ray_slab_overlap_3d(origin, dir, aabb_min, aabb_max)
    }
}

/// Helper: compute whether the intersection of per-axis slab intervals
/// overlaps with [0, ∞). Assumes no axis has a parallel miss.
pub open spec fn ray_slab_overlap_3d<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    aabb_min: Point3<T>, aabb_max: Point3<T>,
) -> bool {
    // Collect t_enter = max(0, t_near_x?, t_near_y?, t_near_z?)
    // where t_near_c is only included if dir.c != 0
    let t_enter = slab_t_enter_3d(origin, dir, aabb_min, aabb_max);
    // Collect t_exit = min(t_far_x?, t_far_y?, t_far_z?)
    let t_exit = slab_t_exit_3d(origin, dir, aabb_min, aabb_max);
    t_enter.le(t_exit)
}

/// t_enter = max(0, t_near for each non-parallel axis)
pub open spec fn slab_t_enter_3d<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    aabb_min: Point3<T>, aabb_max: Point3<T>,
) -> T {
    let mut t = T::zero();

    // X axis
    let t = if !dir.x.eqv(T::zero()) {
        let tn = slab_t_near(origin.x, dir.x, aabb_min.x, aabb_max.x);
        if tn.le(t) { t } else { tn }
    } else { t };

    // Y axis
    let t = if !dir.y.eqv(T::zero()) {
        let tn = slab_t_near(origin.y, dir.y, aabb_min.y, aabb_max.y);
        if tn.le(t) { t } else { tn }
    } else { t };

    // Z axis
    if !dir.z.eqv(T::zero()) {
        let tn = slab_t_near(origin.z, dir.z, aabb_min.z, aabb_max.z);
        if tn.le(t) { t } else { tn }
    } else { t }
}

/// t_exit = min(t_far for each non-parallel axis)
/// If no axis is non-parallel, returns a large value (conceptually +∞).
/// We handle this by returning one() as a sentinel for "no constraint"
/// when all axes are parallel (but we know origin is in the box).
pub open spec fn slab_t_exit_3d<T: OrderedField>(
    origin: Point3<T>, dir: Vec3<T>,
    aabb_min: Point3<T>, aabb_max: Point3<T>,
) -> T {
    let has_x = !dir.x.eqv(T::zero());
    let has_y = !dir.y.eqv(T::zero());
    let has_z = !dir.z.eqv(T::zero());

    let tf_x = slab_t_far(origin.x, dir.x, aabb_min.x, aabb_max.x);
    let tf_y = slab_t_far(origin.y, dir.y, aabb_min.y, aabb_max.y);
    let tf_z = slab_t_far(origin.z, dir.z, aabb_min.z, aabb_max.z);

    if has_x && has_y && has_z {
        let t = tf_x;
        let t = if tf_y.le(t) { tf_y } else { t };
        if tf_z.le(t) { tf_z } else { t }
    } else if has_x && has_y {
        if tf_y.le(tf_x) { tf_y } else { tf_x }
    } else if has_x && has_z {
        if tf_z.le(tf_x) { tf_z } else { tf_x }
    } else if has_y && has_z {
        if tf_z.le(tf_y) { tf_z } else { tf_y }
    } else if has_x {
        tf_x
    } else if has_y {
        tf_y
    } else if has_z {
        tf_z
    } else {
        // All axes parallel, origin in box → any t ≥ 0 works.
        // Return something ≥ 0 so t_enter ≤ t_exit.
        T::zero()
    }
}

// ---------------------------------------------------------------------------
// Ray-AABB intersection (2D)
// ---------------------------------------------------------------------------

/// Ray-AABB intersection test (2D) via slab method.
pub open spec fn ray_hits_aabb2<T: OrderedField>(
    origin: Point2<T>, dir: Vec2<T>,
    aabb_min: Point2<T>, aabb_max: Point2<T>,
) -> bool {
    if axis_parallel_miss(origin.x, dir.x, aabb_min.x, aabb_max.x)
        || axis_parallel_miss(origin.y, dir.y, aabb_min.y, aabb_max.y)
    {
        false
    } else {
        ray_slab_overlap_2d(origin, dir, aabb_min, aabb_max)
    }
}

pub open spec fn ray_slab_overlap_2d<T: OrderedField>(
    origin: Point2<T>, dir: Vec2<T>,
    aabb_min: Point2<T>, aabb_max: Point2<T>,
) -> bool {
    let t_enter = slab_t_enter_2d(origin, dir, aabb_min, aabb_max);
    let t_exit = slab_t_exit_2d(origin, dir, aabb_min, aabb_max);
    t_enter.le(t_exit)
}

pub open spec fn slab_t_enter_2d<T: OrderedField>(
    origin: Point2<T>, dir: Vec2<T>,
    aabb_min: Point2<T>, aabb_max: Point2<T>,
) -> T {
    let mut t = T::zero();
    let t = if !dir.x.eqv(T::zero()) {
        let tn = slab_t_near(origin.x, dir.x, aabb_min.x, aabb_max.x);
        if tn.le(t) { t } else { tn }
    } else { t };
    if !dir.y.eqv(T::zero()) {
        let tn = slab_t_near(origin.y, dir.y, aabb_min.y, aabb_max.y);
        if tn.le(t) { t } else { tn }
    } else { t }
}

pub open spec fn slab_t_exit_2d<T: OrderedField>(
    origin: Point2<T>, dir: Vec2<T>,
    aabb_min: Point2<T>, aabb_max: Point2<T>,
) -> T {
    let has_x = !dir.x.eqv(T::zero());
    let has_y = !dir.y.eqv(T::zero());

    let tf_x = slab_t_far(origin.x, dir.x, aabb_min.x, aabb_max.x);
    let tf_y = slab_t_far(origin.y, dir.y, aabb_min.y, aabb_max.y);

    if has_x && has_y {
        if tf_y.le(tf_x) { tf_y } else { tf_x }
    } else if has_x {
        tf_x
    } else if has_y {
        tf_y
    } else {
        T::zero()
    }
}

} // verus!
