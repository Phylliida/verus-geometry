use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::ray::*;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// Per-axis slab helpers
// ---------------------------------------------------------------------------

/// Check if ray is parallel to axis and misses slab.
fn axis_parallel_miss_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: bool)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
    ensures
        out == axis_parallel_miss::<RationalModel>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    let dir_is_zero = dir_c.eq(&zero);
    if dir_is_zero {
        origin_c.lt(min_c) || max_c.lt(origin_c)
    } else {
        false
    }
}

/// Compute t_near for a non-parallel axis.
fn slab_t_near_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == slab_t_near::<RationalModel>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    if zero.lt(dir_c) {
        min_c.sub(origin_c).div(dir_c)
    } else {
        max_c.sub(origin_c).div(dir_c)
    }
}

/// Compute t_far for a non-parallel axis.
fn slab_t_far_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv_spec(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == slab_t_far::<RationalModel>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    if zero.lt(dir_c) {
        max_c.sub(origin_c).div(dir_c)
    } else {
        min_c.sub(origin_c).div(dir_c)
    }
}

// ---------------------------------------------------------------------------
// 3D ray-AABB exec
// ---------------------------------------------------------------------------

/// Ray-AABB intersection test (3D) at runtime.
pub fn ray_hits_aabb3_exec(
    origin: &RuntimePoint3, dir: &RuntimePoint3,
    aabb_min: &RuntimePoint3, aabb_max: &RuntimePoint3,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out == ray_hits_aabb3::<RationalModel>(
            origin@,
            verus_linalg::vec3::Vec3 { x: dir@.x, y: dir@.y, z: dir@.z },
            aabb_min@, aabb_max@,
        ),
{
    // Check parallel misses
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z) {
        return false;
    }

    // Compute t_enter = max(0, t_near for non-parallel axes)
    let zero = RuntimeRational::from_int(0);
    let dir_x_zero = dir.x.eq(&zero);
    let dir_y_zero = dir.y.eq(&zero);
    let dir_z_zero = dir.z.eq(&zero);

    // t_enter starts at 0
    let mut t_enter = RuntimeRational::from_int(0);

    if !dir_x_zero {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t_enter) {
            t_enter = tn;
        }
    }
    if !dir_y_zero {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t_enter) {
            t_enter = tn;
        }
    }
    if !dir_z_zero {
        let tn = slab_t_near_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        if !tn.le(&t_enter) {
            t_enter = tn;
        }
    }

    // t_exit = min(t_far for non-parallel axes)
    // Need to handle: which axes are non-parallel?
    let has_x = !dir_x_zero;
    let has_y = !dir_y_zero;
    let has_z = !dir_z_zero;

    let t_exit = if has_x && has_y && has_z {
        let tf_x = slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        let tf_y = slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        let tf_z = slab_t_far_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        let t = tf_x;
        let t = if tf_y.le(&t) { tf_y } else { t };
        if tf_z.le(&t) { tf_z } else { t }
    } else if has_x && has_y {
        let tf_x = slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        let tf_y = slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if tf_y.le(&tf_x) { tf_y } else { tf_x }
    } else if has_x && has_z {
        let tf_x = slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        let tf_z = slab_t_far_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        if tf_z.le(&tf_x) { tf_z } else { tf_x }
    } else if has_y && has_z {
        let tf_y = slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        let tf_z = slab_t_far_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        if tf_z.le(&tf_y) { tf_z } else { tf_y }
    } else if has_x {
        slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x)
    } else if has_y {
        slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y)
    } else if has_z {
        slab_t_far_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z)
    } else {
        // All parallel, origin in box → hit at t=0
        RuntimeRational::from_int(0)
    };

    t_enter.le(&t_exit)
}

// ---------------------------------------------------------------------------
// 2D ray-AABB exec
// ---------------------------------------------------------------------------

/// Ray-AABB intersection test (2D) at runtime.
pub fn ray_hits_aabb2_exec(
    origin: &RuntimePoint2, dir: &RuntimePoint2,
    aabb_min: &RuntimePoint2, aabb_max: &RuntimePoint2,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out == ray_hits_aabb2::<RationalModel>(
            origin@,
            verus_linalg::vec2::Vec2 { x: dir@.x, y: dir@.y },
            aabb_min@, aabb_max@,
        ),
{
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) {
        return false;
    }

    let zero = RuntimeRational::from_int(0);
    let dir_x_zero = dir.x.eq(&zero);
    let dir_y_zero = dir.y.eq(&zero);

    let has_x = !dir_x_zero;
    let has_y = !dir_y_zero;

    // t_enter = max(0, t_nears)
    let mut t_enter = RuntimeRational::from_int(0);
    if has_x {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t_enter) {
            t_enter = tn;
        }
    }
    if has_y {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t_enter) {
            t_enter = tn;
        }
    }

    // t_exit = min(t_fars)
    let t_exit = if has_x && has_y {
        let tf_x = slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        let tf_y = slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if tf_y.le(&tf_x) { tf_y } else { tf_x }
    } else if has_x {
        slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x)
    } else if has_y {
        slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y)
    } else {
        RuntimeRational::from_int(0)
    };

    t_enter.le(&t_exit)
}

} // verus!
