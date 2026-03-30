use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::ray::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  Per-axis slab helpers
//  ---------------------------------------------------------------------------

///  Check if ray is parallel to axis and misses slab.
fn axis_parallel_miss_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: bool)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
    ensures
        out == axis_parallel_miss::<Rational>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    let dir_is_zero = dir_c.eq(&zero);
    if dir_is_zero {
        origin_c.lt(min_c) || max_c.lt(origin_c)
    } else {
        false
    }
}

///  Compute t_near for a non-parallel axis.
fn slab_t_near_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv_spec(Rational::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_near::<Rational>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    if zero.lt(dir_c) {
        min_c.sub(origin_c).div(dir_c)
    } else {
        max_c.sub(origin_c).div(dir_c)
    }
}

///  Compute t_far for a non-parallel axis.
fn slab_t_far_exec(
    origin_c: &RuntimeRational, dir_c: &RuntimeRational,
    min_c: &RuntimeRational, max_c: &RuntimeRational,
) -> (out: RuntimeRational)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(),
        min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv_spec(Rational::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_far::<Rational>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = RuntimeRational::from_int(0);
    if zero.lt(dir_c) {
        max_c.sub(origin_c).div(dir_c)
    } else {
        min_c.sub(origin_c).div(dir_c)
    }
}

//  ---------------------------------------------------------------------------
//  3D slab t_enter / t_exit helpers (extracted to reduce Z3 path explosion)
//  ---------------------------------------------------------------------------

///  Compute t_enter = max(0, t_near for non-parallel axes) at runtime (3D).
fn slab_t_enter_3d_exec(
    origin: &RuntimePoint3<RuntimeRational, Rational>, dir: &RuntimePoint3<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint3<RuntimeRational, Rational>, aabb_max: &RuntimePoint3<RuntimeRational, Rational>,
) -> (out: RuntimeRational)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_enter_3d::<Rational>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            aabb_min.model@, aabb_max.model@,
        ),
{
    let zero = RuntimeRational::from_int(0);
    let mut t = RuntimeRational::from_int(0);
    if !dir.x.eq(&zero) {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t) { t = tn; }
    }
    if !dir.y.eq(&zero) {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t) { t = tn; }
    }
    if !dir.z.eq(&zero) {
        let tn = slab_t_near_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        if !tn.le(&t) { t = tn; }
    }
    t
}

///  Compute t_exit = min(t_far for non-parallel axes) at runtime (3D).
fn slab_t_exit_3d_exec(
    origin: &RuntimePoint3<RuntimeRational, Rational>, dir: &RuntimePoint3<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint3<RuntimeRational, Rational>, aabb_max: &RuntimePoint3<RuntimeRational, Rational>,
) -> (out: RuntimeRational)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_exit_3d::<Rational>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            aabb_min.model@, aabb_max.model@,
        ),
{
    let zero = RuntimeRational::from_int(0);
    let has_x = !dir.x.eq(&zero);
    let has_y = !dir.y.eq(&zero);
    let has_z = !dir.z.eq(&zero);

    if has_x && has_y && has_z {
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
        RuntimeRational::from_int(0)
    }
}

//  ---------------------------------------------------------------------------
//  3D ray-AABB exec
//  ---------------------------------------------------------------------------

///  Ray-AABB intersection test (3D) at runtime.
pub fn ray_hits_aabb3_exec(
    origin: &RuntimePoint3<RuntimeRational, Rational>, dir: &RuntimePoint3<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint3<RuntimeRational, Rational>, aabb_max: &RuntimePoint3<RuntimeRational, Rational>,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out == ray_hits_aabb3::<Rational>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            aabb_min.model@, aabb_max.model@,
        ),
{
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z) {
        return false;
    }

    let t_enter = slab_t_enter_3d_exec(origin, dir, aabb_min, aabb_max);
    let t_exit = slab_t_exit_3d_exec(origin, dir, aabb_min, aabb_max);
    t_enter.le(&t_exit)
}

//  ---------------------------------------------------------------------------
//  2D slab t_enter / t_exit helpers
//  ---------------------------------------------------------------------------

///  Compute t_enter = max(0, t_near for non-parallel axes) at runtime (2D).
fn slab_t_enter_2d_exec(
    origin: &RuntimePoint2<RuntimeRational, Rational>, dir: &RuntimePoint2<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint2<RuntimeRational, Rational>, aabb_max: &RuntimePoint2<RuntimeRational, Rational>,
) -> (out: RuntimeRational)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_enter_2d::<Rational>(
            origin.model@,
            verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
            aabb_min.model@, aabb_max.model@,
        ),
{
    let zero = RuntimeRational::from_int(0);
    let mut t = RuntimeRational::from_int(0);
    if !dir.x.eq(&zero) {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t) { t = tn; }
    }
    if !dir.y.eq(&zero) {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t) { t = tn; }
    }
    t
}

///  Compute t_exit = min(t_far for non-parallel axes) at runtime (2D).
fn slab_t_exit_2d_exec(
    origin: &RuntimePoint2<RuntimeRational, Rational>, dir: &RuntimePoint2<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint2<RuntimeRational, Rational>, aabb_max: &RuntimePoint2<RuntimeRational, Rational>,
) -> (out: RuntimeRational)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == slab_t_exit_2d::<Rational>(
            origin.model@,
            verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
            aabb_min.model@, aabb_max.model@,
        ),
{
    let zero = RuntimeRational::from_int(0);
    let has_x = !dir.x.eq(&zero);
    let has_y = !dir.y.eq(&zero);

    if has_x && has_y {
        let tf_x = slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        let tf_y = slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if tf_y.le(&tf_x) { tf_y } else { tf_x }
    } else if has_x {
        slab_t_far_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x)
    } else if has_y {
        slab_t_far_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y)
    } else {
        RuntimeRational::from_int(0)
    }
}

//  ---------------------------------------------------------------------------
//  2D ray-AABB exec
//  ---------------------------------------------------------------------------

///  Ray-AABB intersection test (2D) at runtime.
pub fn ray_hits_aabb2_exec(
    origin: &RuntimePoint2<RuntimeRational, Rational>, dir: &RuntimePoint2<RuntimeRational, Rational>,
    aabb_min: &RuntimePoint2<RuntimeRational, Rational>, aabb_max: &RuntimePoint2<RuntimeRational, Rational>,
) -> (out: bool)
    requires
        origin.wf_spec(), dir.wf_spec(),
        aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures
        out == ray_hits_aabb2::<Rational>(
            origin.model@,
            verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
            aabb_min.model@, aabb_max.model@,
        ),
{
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) {
        return false;
    }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) {
        return false;
    }

    let t_enter = slab_t_enter_2d_exec(origin, dir, aabb_min, aabb_max);
    let t_exit = slab_t_exit_2d_exec(origin, dir, aabb_min, aabb_max);
    t_enter.le(&t_exit)
}

} //  verus!
