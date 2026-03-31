#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::polygon::RuntimePolygon2;
#[cfg(verus_keep_ghost)]
use crate::area::*;
#[cfg(verus_keep_ghost)]
use crate::convex_polygon::polygon_next_index;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
verus! {

fn cross_origin_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, q: &RuntimePoint2<R, V>,
) -> (out: R)
    requires p.wf_spec(), q.wf_spec(),
    ensures out.wf_spec(), out@ == cross_origin::<V>(p.model@, q.model@),
{
    let a = p.x.mul(&q.y);
    let b = p.y.mul(&q.x);
    a.sub(&b)
}

pub fn signed_area_2x_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    polygon: &RuntimePolygon2<R, V>,
) -> (out: R)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out.wf_spec(),
        out@ == signed_area_2x::<V>(polygon@),
{
    let n = polygon.len();
    let first = polygon.get(0);
    let mut acc = first.x.zero_like();
    let mut i: usize = 0;

    proof {
        assert(acc@ == V::zero());
        assert(signed_area_2x_prefix::<V>(polygon@, 0) == V::zero());
    }

    while i < n
        invariant
            0 <= i <= n,
            n == polygon.vertices@.len(),
            n >= 3,
            polygon.wf_spec(),
            acc.wf_spec(),
            acc@ == signed_area_2x_prefix::<V>(polygon@, i as int),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0usize };

        proof {
            assert(j as int == polygon_next_index(n as int, i as int));
        }

        let pi = polygon.get(i);
        let pj = polygon.get(j);
        let term = cross_origin_exec(pi, pj);
        acc = acc.add(&term);

        proof {
            assert(acc@ == signed_area_2x_prefix::<V>(
                polygon@, (i + 1) as int));
        }

        i = i + 1;
    }

    acc
}

} //  verus!
