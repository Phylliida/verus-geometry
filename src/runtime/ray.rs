#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::ray::*;

#[cfg(verus_keep_ghost)]
verus! {

fn axis_parallel_miss_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin_c: &R, dir_c: &R, min_c: &R, max_c: &R,
) -> (out: bool)
    requires origin_c.wf_spec(), dir_c.wf_spec(), min_c.wf_spec(), max_c.wf_spec(),
    ensures out == axis_parallel_miss::<V>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = dir_c.zero_like();
    if dir_c.eq(&zero) {
        origin_c.lt(min_c) || max_c.lt(origin_c)
    } else {
        false
    }
}

fn slab_t_near_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin_c: &R, dir_c: &R, min_c: &R, max_c: &R,
) -> (out: R)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(), min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv(V::zero()),
    ensures out.wf_spec(), out@ == slab_t_near::<V>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = dir_c.zero_like();
    if zero.lt(dir_c) {
        min_c.sub(origin_c).div(dir_c)
    } else {
        max_c.sub(origin_c).div(dir_c)
    }
}

fn slab_t_far_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin_c: &R, dir_c: &R, min_c: &R, max_c: &R,
) -> (out: R)
    requires
        origin_c.wf_spec(), dir_c.wf_spec(), min_c.wf_spec(), max_c.wf_spec(),
        !dir_c@.eqv(V::zero()),
    ensures out.wf_spec(), out@ == slab_t_far::<V>(origin_c@, dir_c@, min_c@, max_c@),
{
    let zero = dir_c.zero_like();
    if zero.lt(dir_c) {
        max_c.sub(origin_c).div(dir_c)
    } else {
        min_c.sub(origin_c).div(dir_c)
    }
}

fn slab_t_enter_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    aabb_min: &RuntimePoint3<R, V>, aabb_max: &RuntimePoint3<R, V>,
) -> (out: R)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out.wf_spec(),
        out@ == slab_t_enter_3d::<V>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            aabb_min.model@, aabb_max.model@),
{
    let zero = origin.x.zero_like();
    let mut t = origin.x.zero_like();
    if !dir.x.eq(&zero) {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t) { t = tn; }
    }
    let zero = origin.x.zero_like();
    if !dir.y.eq(&zero) {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t) { t = tn; }
    }
    let zero = origin.x.zero_like();
    if !dir.z.eq(&zero) {
        let tn = slab_t_near_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z);
        if !tn.le(&t) { t = tn; }
    }
    t
}

fn slab_t_exit_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    aabb_min: &RuntimePoint3<R, V>, aabb_max: &RuntimePoint3<R, V>,
) -> (out: R)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out.wf_spec(),
        out@ == slab_t_exit_3d::<V>(
            origin.model@,
            verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
            aabb_min.model@, aabb_max.model@),
{
    let zero = origin.x.zero_like();
    let has_x = !dir.x.eq(&zero);
    let zero = origin.x.zero_like();
    let has_y = !dir.y.eq(&zero);
    let zero = origin.x.zero_like();
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
        origin.x.zero_like()
    }
}

pub fn ray_hits_aabb3_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    aabb_min: &RuntimePoint3<R, V>, aabb_max: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out == ray_hits_aabb3::<V>(
        origin.model@,
        verus_linalg::vec3::Vec3 { x: dir.model@.x, y: dir.model@.y, z: dir.model@.z },
        aabb_min.model@, aabb_max.model@),
{
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) { return false; }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) { return false; }
    if axis_parallel_miss_exec(&origin.z, &dir.z, &aabb_min.z, &aabb_max.z) { return false; }
    let t_enter = slab_t_enter_3d_exec(origin, dir, aabb_min, aabb_max);
    let t_exit = slab_t_exit_3d_exec(origin, dir, aabb_min, aabb_max);
    t_enter.le(&t_exit)
}

fn slab_t_enter_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint2<R, V>, dir: &RuntimePoint2<R, V>,
    aabb_min: &RuntimePoint2<R, V>, aabb_max: &RuntimePoint2<R, V>,
) -> (out: R)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out.wf_spec(),
        out@ == slab_t_enter_2d::<V>(
            origin.model@,
            verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
            aabb_min.model@, aabb_max.model@),
{
    let zero = origin.x.zero_like();
    let mut t = origin.x.zero_like();
    if !dir.x.eq(&zero) {
        let tn = slab_t_near_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x);
        if !tn.le(&t) { t = tn; }
    }
    let zero = origin.x.zero_like();
    if !dir.y.eq(&zero) {
        let tn = slab_t_near_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y);
        if !tn.le(&t) { t = tn; }
    }
    t
}

fn slab_t_exit_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint2<R, V>, dir: &RuntimePoint2<R, V>,
    aabb_min: &RuntimePoint2<R, V>, aabb_max: &RuntimePoint2<R, V>,
) -> (out: R)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out.wf_spec(),
        out@ == slab_t_exit_2d::<V>(
            origin.model@,
            verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
            aabb_min.model@, aabb_max.model@),
{
    let zero = origin.x.zero_like();
    let has_x = !dir.x.eq(&zero);
    let zero = origin.x.zero_like();
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
        origin.x.zero_like()
    }
}

pub fn ray_hits_aabb2_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    origin: &RuntimePoint2<R, V>, dir: &RuntimePoint2<R, V>,
    aabb_min: &RuntimePoint2<R, V>, aabb_max: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires origin.wf_spec(), dir.wf_spec(), aabb_min.wf_spec(), aabb_max.wf_spec(),
    ensures out == ray_hits_aabb2::<V>(
        origin.model@,
        verus_linalg::vec2::Vec2 { x: dir.model@.x, y: dir.model@.y },
        aabb_min.model@, aabb_max.model@),
{
    if axis_parallel_miss_exec(&origin.x, &dir.x, &aabb_min.x, &aabb_max.x) { return false; }
    if axis_parallel_miss_exec(&origin.y, &dir.y, &aabb_min.y, &aabb_max.y) { return false; }
    let t_enter = slab_t_enter_2d_exec(origin, dir, aabb_min, aabb_max);
    let t_exit = slab_t_exit_2d_exec(origin, dir, aabb_min, aabb_max);
    t_enter.le(&t_exit)
}

} //  verus!
