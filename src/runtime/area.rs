use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::polygon::RuntimePolygon2;
#[cfg(verus_keep_ghost)]
use crate::area::*;
#[cfg(verus_keep_ghost)]
use crate::convex_polygon::polygon_next_index;

#[cfg(verus_keep_ghost)]
verus! {

/// Compute cross_origin(p, q) = p.x * q.y - p.y * q.x at runtime.
fn cross_origin_exec(p: &RuntimePoint2, q: &RuntimePoint2) -> (out: RuntimeRational)
    requires
        p.wf_spec(),
        q.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cross_origin::<RationalModel>(p@, q@),
{
    let a = p.x.mul(&q.y);
    let b = p.y.mul(&q.x);
    a.sub(&b)
}

/// Compute twice the signed area of a simple polygon (shoelace formula).
///
/// Returns a RuntimeRational whose view equals signed_area_2x(polygon.model()).
pub fn signed_area_2x_exec(polygon: &RuntimePolygon2) -> (out: RuntimeRational)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out.wf_spec(),
        out@ == signed_area_2x::<RationalModel>(polygon.model()),
{
    let n = polygon.len();
    let mut acc = RuntimeRational::from_int(0);
    let mut i: usize = 0;

    proof {
        assert(acc@ == RationalModel::from_int_spec(0));
        assert(signed_area_2x_prefix::<RationalModel>(polygon.model(), 0)
            == RationalModel::from_int_spec(0));
    }

    while i < n
        invariant
            0 <= i <= n,
            n == polygon.vertices@.len(),
            n >= 3,
            polygon.wf_spec(),
            acc.wf_spec(),
            acc@ == signed_area_2x_prefix::<RationalModel>(polygon.model(), i as int),
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
            // acc now equals old_acc + cross_origin(polygon[i], polygon[j])
            // which equals signed_area_2x_prefix(polygon.model(), i+1)
            assert(acc@ == signed_area_2x_prefix::<RationalModel>(
                polygon.model(), (i + 1) as int));
        }

        i = i + 1;
    }

    acc
}

} // verus!
