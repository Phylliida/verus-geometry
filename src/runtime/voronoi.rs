#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use crate::voronoi::sq_dist_2d;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;

#[cfg(verus_keep_ghost)]
verus! {

pub fn sq_dist_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, q: &RuntimePoint2<R, V>,
) -> (out: R)
    requires p.wf_spec(), q.wf_spec(),
    ensures out.wf_spec(), out.model() == sq_dist_2d::<V>(p.model@, q.model@),
{
    let d = p.sub(q);
    d.norm_sq()
}

} //  verus!
