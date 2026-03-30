#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::aabb::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
verus! {

pub fn point_in_aabb2_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, min: &RuntimePoint2<R, V>, max: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), min.wf_spec(), max.wf_spec(),
    ensures out == point_in_aabb2::<V>(p.model@, min.model@, max.model@),
{
    min.x.le(&p.x) && p.x.le(&max.x)
    && min.y.le(&p.y) && p.y.le(&max.y)
}

pub fn point_in_aabb3_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>, min: &RuntimePoint3<R, V>, max: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires p.wf_spec(), min.wf_spec(), max.wf_spec(),
    ensures out == point_in_aabb3::<V>(p.model@, min.model@, max.model@),
{
    min.x.le(&p.x) && p.x.le(&max.x)
    && min.y.le(&p.y) && p.y.le(&max.y)
    && min.z.le(&p.z) && p.z.le(&max.z)
}

pub fn aabb2_separated_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    min_a: &RuntimePoint2<R, V>, max_a: &RuntimePoint2<R, V>,
    min_b: &RuntimePoint2<R, V>, max_b: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires min_a.wf_spec(), max_a.wf_spec(), min_b.wf_spec(), max_b.wf_spec(),
    ensures out == aabb2_separated::<V>(min_a.model@, max_a.model@, min_b.model@, max_b.model@),
{
    max_a.x.lt(&min_b.x) || max_b.x.lt(&min_a.x)
    || max_a.y.lt(&min_b.y) || max_b.y.lt(&min_a.y)
}

pub fn aabb3_separated_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    min_a: &RuntimePoint3<R, V>, max_a: &RuntimePoint3<R, V>,
    min_b: &RuntimePoint3<R, V>, max_b: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires min_a.wf_spec(), max_a.wf_spec(), min_b.wf_spec(), max_b.wf_spec(),
    ensures out == aabb3_separated::<V>(min_a.model@, max_a.model@, min_b.model@, max_b.model@),
{
    max_a.x.lt(&min_b.x) || max_b.x.lt(&min_a.x)
    || max_a.y.lt(&min_b.y) || max_b.y.lt(&min_a.y)
    || max_a.z.lt(&min_b.z) || max_b.z.lt(&min_a.z)
}

} //  verus!
