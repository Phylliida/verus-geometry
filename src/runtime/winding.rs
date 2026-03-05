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

/// Compute the winding edge contribution at runtime.
///
/// Returns +1, -1, or 0 matching winding_edge spec.
fn winding_edge_exec(
    q: &RuntimePoint2, p0: &RuntimePoint2, p1: &RuntimePoint2,
) -> (out: i64)
    requires
        q.wf_spec(),
        p0.wf_spec(),
        p1.wf_spec(),
    ensures
        out as int == winding_edge::<RationalModel>(q@, p0@, p1@),
        -1 <= out <= 1,
{
    let o = orient2d_exec(p0, p1, q);
    let p0y_le_qy = p0.y.le(&q.y);
    let qy_lt_p1y = q.y.lt(&p1.y);
    let p1y_le_qy = p1.y.le(&q.y);
    let qy_lt_p0y = q.y.lt(&p0.y);

    let zero = RuntimeRational::from_int(0);
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

/// Compute the winding number of query point q with respect to polygon.
///
/// Returns an integer: nonzero means inside, zero means outside.
pub fn winding_number_exec(
    q: &RuntimePoint2, polygon: &RuntimePolygon2,
) -> (out: i64)
    requires
        q.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
        polygon.vertices@.len() < 0x7FFF_FFFF_FFFF_FFFF,
    ensures
        out as int == winding_number::<RationalModel>(q@, polygon.model()),
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
            wn as int == winding_number_prefix::<RationalModel>(q@, polygon.model(), i as int),
            // Each edge contributes at most ±1, so |wn| ≤ i
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

/// Test if point is inside polygon (nonzero winding number).
pub fn point_in_polygon_exec(
    q: &RuntimePoint2, polygon: &RuntimePolygon2,
) -> (out: bool)
    requires
        q.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
        polygon.vertices@.len() < 0x7FFF_FFFF_FFFF_FFFF,
    ensures
        out == point_in_polygon::<RationalModel>(q@, polygon.model()),
{
    let wn = winding_number_exec(q, polygon);
    wn != 0
}

} // verus!
