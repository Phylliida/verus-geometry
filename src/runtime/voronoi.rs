use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::voronoi::sq_dist_2d;

use super::point2::{RuntimePoint2, sub2_exec};

verus! {

/// Squared distance between two RuntimePoint2s.
pub fn sq_dist_2d_exec(p: &RuntimePoint2, q: &RuntimePoint2) -> (out: RuntimeRational)
    requires
        p.wf_spec(),
        q.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == sq_dist_2d::<RationalModel>(p@, q@),
{
    let v = sub2_exec(p, q);
    v.norm_sq_exec()
}

} // verus!
