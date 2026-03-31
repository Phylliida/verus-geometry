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
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::triangle_distance::*;
#[cfg(verus_keep_ghost)]
use crate::closest_point::*;
#[cfg(verus_keep_ghost)]
use crate::point2::sub2;
#[cfg(verus_keep_ghost)]
use crate::point3::sub3;

#[cfg(verus_keep_ghost)]
verus! {

pub fn point_in_triangle_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>, c: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out == point_in_triangle_2d::<V>(q.model@, a.model@, b.model@, c.model@),
{
    let o1 = super::orient::orient2d_exec(a, b, q);
    let o2 = super::orient::orient2d_exec(b, c, q);
    let o3 = super::orient::orient2d_exec(c, a, q);
    let zero = o1.zero_like();

    let o1_ge = zero.le(&o1);
    let o2_ge = zero.le(&o2);
    let o3_ge = zero.le(&o3);

    let o1_le = o1.le(&zero);
    let o2_le = o2.le(&zero);
    let o3_le = o3.le(&zero);

    (o1_ge && o2_ge && o3_ge) || (o1_le && o2_le && o3_le)
}

fn min_of_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: R, b: R,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(),
    ensures out.wf_spec(), out@ == min_of::<V>(a@, b@),
{
    if a.le(&b) { a } else { b }
}

fn min_of_three_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: R, b: R, c: R,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out.wf_spec(), out@ == min_of_three::<V>(a@, b@, c@),
{
    min_of_exec(a, min_of_exec(b, c))
}

pub fn squared_distance_point_triangle_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>, c: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        !verus_linalg::vec2::ops::norm_sq(sub2::<V>(b.model@, a.model@)).eqv(V::zero()),
        !verus_linalg::vec2::ops::norm_sq(sub2::<V>(c.model@, b.model@)).eqv(V::zero()),
        !verus_linalg::vec2::ops::norm_sq(sub2::<V>(a.model@, c.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == squared_distance_point_triangle_2d::<V>(q.model@, a.model@, b.model@, c.model@),
{
    if point_in_triangle_2d_exec(q, a, b, c) {
        q.x.zero_like()
    } else {
        let d_ab = super::closest_point::squared_distance_point_segment_2d_exec(q, a, b);
        let d_bc = super::closest_point::squared_distance_point_segment_2d_exec(q, b, c);
        let d_ca = super::closest_point::squared_distance_point_segment_2d_exec(q, c, a);
        min_of_three_exec(d_ab, d_bc, d_ca)
    }
}

pub fn min_edge_squared_distance_3d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    q: &RuntimePoint3<R, V>, a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>, c: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        q.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(),
        !verus_linalg::vec3::ops::norm_sq(sub3::<V>(b.model@, a.model@)).eqv(V::zero()),
        !verus_linalg::vec3::ops::norm_sq(sub3::<V>(c.model@, b.model@)).eqv(V::zero()),
        !verus_linalg::vec3::ops::norm_sq(sub3::<V>(a.model@, c.model@)).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == min_edge_squared_distance_3d::<V>(q.model@, a.model@, b.model@, c.model@),
{
    let d_ab = super::closest_point::squared_distance_point_segment_3d_exec(q, a, b);
    let d_bc = super::closest_point::squared_distance_point_segment_3d_exec(q, b, c);
    let d_ca = super::closest_point::squared_distance_point_segment_3d_exec(q, c, a);
    min_of_three_exec(d_ab, d_bc, d_ca)
}

} //  verus!
