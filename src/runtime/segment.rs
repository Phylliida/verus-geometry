#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use super::point2::{RuntimePoint2, sub2_exec, add_vec2_exec};
#[cfg(verus_keep_ghost)]
use super::orient::orient2d_exec;
#[cfg(verus_keep_ghost)]
use super::classification::orient2d_sign_exec;
#[cfg(verus_keep_ghost)]
use crate::orientation_sign::*;
#[cfg(verus_keep_ghost)]
use crate::orient2d::orient2d;
#[cfg(verus_keep_ghost)]
use crate::segment_intersection::*;

#[cfg(verus_keep_ghost)]
verus! {

pub fn is_zero_sign(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Zero),
{
    match s {
        OrientationSign::Zero => true,
        _ => false,
    }
}

pub fn signs_equal(a: &OrientationSign, b: &OrientationSign) -> (out: bool)
    ensures out == (*a == *b),
{
    match (a, b) {
        (OrientationSign::Positive, OrientationSign::Positive) => true,
        (OrientationSign::Negative, OrientationSign::Negative) => true,
        (OrientationSign::Zero, OrientationSign::Zero) => true,
        _ => false,
    }
}

pub fn point_on_segment_inclusive_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(),
    ensures out == point_on_segment_inclusive_2d::<V>(p.model@, a.model@, b.model@),
{
    let val = orient2d_exec(a, b, p);
    let zero = val.zero_like();
    if !val.eq(&zero) {
        return false;
    }
    let min_x_le_px = if a.x.le(&b.x) { a.x.le(&p.x) } else { b.x.le(&p.x) };
    let px_le_max_x = if a.x.le(&b.x) { p.x.le(&b.x) } else { p.x.le(&a.x) };
    let min_y_le_py = if a.y.le(&b.y) { a.y.le(&p.y) } else { b.y.le(&p.y) };
    let py_le_max_y = if a.y.le(&b.y) { p.y.le(&b.y) } else { p.y.le(&a.y) };
    min_x_le_px && px_le_max_x && min_y_le_py && py_le_max_y
}

pub fn point_on_both_segments_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: bool)
    requires p.wf_spec(), a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == point_on_both_segments_2d::<V>(p.model@, a.model@, b.model@, c.model@, d.model@),
{
    point_on_segment_inclusive_2d_exec(p, a, b) && point_on_segment_inclusive_2d_exec(p, c, d)
}

pub fn collinear_overlap_kind_1d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a1: &R, a2: &R, b1: &R, b2: &R,
) -> (out: i8)
    requires a1.wf_spec(), a2.wf_spec(), b1.wf_spec(), b2.wf_spec(),
    ensures
        (out == -1i8) == (collinear_overlap_kind_1d::<V>(a1.model(), a2.model(), b1.model(), b2.model()) < 0),
        (out == 0i8) == (collinear_overlap_kind_1d::<V>(a1.model(), a2.model(), b1.model(), b2.model()) == 0),
        (out == 1i8) == (collinear_overlap_kind_1d::<V>(a1.model(), a2.model(), b1.model(), b2.model()) > 0),
{
    let a1_le_a2 = a1.le(a2);
    let b1_le_b2 = b1.le(b2);
    let (a_lo, a_hi) = if a1_le_a2 { (a1, a2) } else { (a2, a1) };
    let (b_lo, b_hi) = if b1_le_b2 { (b1, b2) } else { (b2, b1) };
    let a_lo_le_b_lo = a_lo.le(b_lo);
    let lo = if a_lo_le_b_lo { b_lo } else { a_lo };
    let a_hi_le_b_hi = a_hi.le(b_hi);
    let hi = if a_hi_le_b_hi { a_hi } else { b_hi };
    if hi.lt(lo) {
        -1i8
    } else if hi.eq(lo) {
        0i8
    } else {
        1i8
    }
}

pub fn segment_intersection_kind_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: SegmentIntersection2dKind)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out == segment_intersection_kind_2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let o1 = orient2d_sign_exec(a, b, c);
    let o2 = orient2d_sign_exec(a, b, d);
    let o3 = orient2d_sign_exec(c, d, a);
    let o4 = orient2d_sign_exec(c, d, b);

    let touch1 = point_on_both_segments_2d_exec(c, a, b, c, d);
    let touch2 = point_on_both_segments_2d_exec(d, a, b, c, d);
    let touch3 = point_on_both_segments_2d_exec(a, a, b, c, d);
    let touch4 = point_on_both_segments_2d_exec(b, a, b, c, d);

    let o1z = is_zero_sign(&o1);
    let o2z = is_zero_sign(&o2);
    let o3z = is_zero_sign(&o3);
    let o4z = is_zero_sign(&o4);

    if o1z && o2z && o3z && o4z {
        let use_x = !a.x.eq(&b.x) || !c.x.eq(&d.x);
        let overlap_kind = if use_x {
            collinear_overlap_kind_1d_exec(&a.x, &b.x, &c.x, &d.x)
        } else {
            collinear_overlap_kind_1d_exec(&a.y, &b.y, &c.y, &d.y)
        };
        if overlap_kind == -1i8 {
            SegmentIntersection2dKind::Disjoint
        } else if overlap_kind == 0i8 && (touch1 || touch2 || touch3 || touch4) {
            SegmentIntersection2dKind::EndpointTouch
        } else {
            SegmentIntersection2dKind::CollinearOverlap
        }
    } else if !o1z && !o2z && !o3z && !o4z
        && !signs_equal(&o1, &o2) && !signs_equal(&o3, &o4)
    {
        SegmentIntersection2dKind::Proper
    } else if touch1 || touch2 || touch3 || touch4 {
        SegmentIntersection2dKind::EndpointTouch
    } else {
        SegmentIntersection2dKind::Disjoint
    }
}

pub fn segment_intersection_parameter_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        segment_intersection_kind_2d::<V>(a.model@, b.model@, c.model@, d.model@)
            == SegmentIntersection2dKind::Proper,
    ensures
        out.wf_spec(),
        out.model() == segment_intersection_parameter_2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let o3 = orient2d_exec(c, d, a);
    let o4 = orient2d_exec(c, d, b);
    let neg_o4 = o4.neg();
    let denom = o3.add(&neg_o4);
    proof {
        lemma_proper_denominator_nonzero_2d::<V>(a.model@, b.model@, c.model@, d.model@);
    }
    o3.div(&denom)
}

///  Intersection point on AB: a + t * (b - a)
pub fn segment_intersection_point_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        segment_intersection_kind_2d::<V>(a.model@, b.model@, c.model@, d.model@)
            == SegmentIntersection2dKind::Proper,
    ensures
        out.wf_spec(),
        out.model@ == segment_intersection_point_2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let t = segment_intersection_parameter_2d_exec(a, b, c, d);
    let (dx, dy) = sub2_exec(b, a);
    let tx = t.mul(&dx);
    let ty = t.mul(&dy);
    add_vec2_exec(a, &tx, &ty)
}

pub fn segment_intersection_parameter_cd_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: R)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        segment_intersection_kind_2d::<V>(a.model@, b.model@, c.model@, d.model@)
            == SegmentIntersection2dKind::Proper,
    ensures
        out.wf_spec(),
        out.model() == segment_intersection_parameter_cd_2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let o1 = orient2d_exec(a, b, c);
    let o2 = orient2d_exec(a, b, d);
    let neg_o2 = o2.neg();
    let denom = o1.add(&neg_o2);
    proof {
        lemma_proper_cd_denominator_nonzero_2d::<V>(a.model@, b.model@, c.model@, d.model@);
    }
    o1.div(&denom)
}

pub fn segment_intersection_point_cd_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>, b: &RuntimePoint2<R, V>,
    c: &RuntimePoint2<R, V>, d: &RuntimePoint2<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        segment_intersection_kind_2d::<V>(a.model@, b.model@, c.model@, d.model@)
            == SegmentIntersection2dKind::Proper,
    ensures
        out.wf_spec(),
        out.model@ == segment_intersection_point_cd_2d::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let s = segment_intersection_parameter_cd_2d_exec(a, b, c, d);
    let (dx, dy) = sub2_exec(d, c);
    let sx = s.mul(&dx);
    let sy = s.mul(&dy);
    add_vec2_exec(c, &sx, &sy)
}

} //  verus!
