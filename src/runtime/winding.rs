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
use super::polygon::RuntimePolygon2;
#[cfg(verus_keep_ghost)]
use super::orient::orient2d_exec;
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::winding::*;
#[cfg(verus_keep_ghost)]
use crate::convex_polygon::polygon_next_index;

#[cfg(verus_keep_ghost)]
verus! {

fn winding_edge_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, p0: &RuntimePoint2<R, V>, p1: &RuntimePoint2<R, V>,
) -> (out: i64)
    requires q.wf_spec(), p0.wf_spec(), p1.wf_spec(),
    ensures
        out as int == winding_edge::<V>(q.model@, p0.model@, p1.model@),
        -1 <= out <= 1,
{
    let o = orient2d_exec(p0, p1, q);
    let p0y_le_qy = p0.y.le(&q.y);
    let qy_lt_p1y = q.y.lt(&p1.y);
    let p1y_le_qy = p1.y.le(&q.y);
    let qy_lt_p0y = q.y.lt(&p0.y);

    let zero = o.zero_like();
    let zero_lt_o = zero.lt(&o);
    let o_lt_zero = o.lt(&zero);

    if p0y_le_qy && qy_lt_p1y && zero_lt_o {
        1i64
    } else if p1y_le_qy && qy_lt_p0y && o_lt_zero {
        -1i64
    } else {
        0i64
    }
}

pub fn winding_number_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, polygon: &RuntimePolygon2<R, V>,
) -> (out: i64)
    requires
        q.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
        polygon.vertices@.len() < 0x7FFF_FFFF_FFFF_FFFF,
    ensures
        out as int == winding_number::<V>(q.model@, polygon@),
{
    let n = polygon.len();
    let mut wn: i64 = 0;
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == polygon.vertices@.len(),
            n >= 3,
            n < 0x7FFF_FFFF_FFFF_FFFF,
            q.wf_spec(),
            polygon.wf_spec(),
            wn as int == winding_number_prefix::<V>(q.model@, polygon@, i as int),
            -(i as i64) <= wn <= (i as i64),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0usize };

        proof {
            assert(j as int == polygon_next_index(n as int, i as int));
        }

        let pi = polygon.get(i);
        let pj = polygon.get(j);
        let edge_wn = winding_edge_exec(q, pi, pj);
        wn = wn + edge_wn;

        i = i + 1;
    }

    wn
}

pub fn point_in_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        q.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
        polygon.vertices@.len() < 0x7FFF_FFFF_FFFF_FFFF,
    ensures
        out == point_in_polygon::<V>(q.model@, polygon@),
{
    let wn = winding_number_exec(q, polygon);
    wn != 0
}

} //  verus!
