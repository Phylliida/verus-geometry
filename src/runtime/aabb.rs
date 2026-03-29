#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::aabb::*;

#[cfg(verus_keep_ghost)]
verus! {

///  Point p is inside the 2D AABB [min, max].
pub fn point_in_aabb2_exec(
    p: &RuntimePoint2, min: &RuntimePoint2, max: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        min.wf_spec(),
        max.wf_spec(),
    ensures
        out == point_in_aabb2::<RationalModel>(p@, min@, max@),
{
    min.x.le(&p.x) && p.x.le(&max.x)
    && min.y.le(&p.y) && p.y.le(&max.y)
}

///  Point p is inside the 3D AABB [min, max].
pub fn point_in_aabb3_exec(
    p: &RuntimePoint3, min: &RuntimePoint3, max: &RuntimePoint3,
) -> (out: bool)
    requires
        p.wf_spec(),
        min.wf_spec(),
        max.wf_spec(),
    ensures
        out == point_in_aabb3::<RationalModel>(p@, min@, max@),
{
    min.x.le(&p.x) && p.x.le(&max.x)
    && min.y.le(&p.y) && p.y.le(&max.y)
    && min.z.le(&p.z) && p.z.le(&max.z)
}

///  Two 2D AABBs are separated along some axis.
pub fn aabb2_separated_exec(
    min_a: &RuntimePoint2, max_a: &RuntimePoint2,
    min_b: &RuntimePoint2, max_b: &RuntimePoint2,
) -> (out: bool)
    requires
        min_a.wf_spec(),
        max_a.wf_spec(),
        min_b.wf_spec(),
        max_b.wf_spec(),
    ensures
        out == aabb2_separated::<RationalModel>(min_a@, max_a@, min_b@, max_b@),
{
    max_a.x.lt(&min_b.x) || max_b.x.lt(&min_a.x)
    || max_a.y.lt(&min_b.y) || max_b.y.lt(&min_a.y)
}

///  Two 3D AABBs are separated along some axis.
pub fn aabb3_separated_exec(
    min_a: &RuntimePoint3, max_a: &RuntimePoint3,
    min_b: &RuntimePoint3, max_b: &RuntimePoint3,
) -> (out: bool)
    requires
        min_a.wf_spec(),
        max_a.wf_spec(),
        min_b.wf_spec(),
        max_b.wf_spec(),
    ensures
        out == aabb3_separated::<RationalModel>(min_a@, max_a@, min_b@, max_b@),
{
    max_a.x.lt(&min_b.x) || max_b.x.lt(&min_a.x)
    || max_a.y.lt(&min_b.y) || max_b.y.lt(&min_a.y)
    || max_a.z.lt(&min_b.z) || max_b.z.lt(&min_a.z)
}

} //  verus!
