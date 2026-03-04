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
use verus_rational::rational::Rational;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// OrientationSign exec helpers
// ---------------------------------------------------------------------------

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

// (scalar_min_exec / scalar_max_exec not needed — direct comparisons used instead)

// ---------------------------------------------------------------------------
// Point-on-segment predicate
// ---------------------------------------------------------------------------

pub fn point_on_segment_inclusive_2d_exec(
    p: &RuntimePoint2, a: &RuntimePoint2, b: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out == point_on_segment_inclusive_2d::<RationalModel>(p@, a@, b@),
{
    let val = orient2d_exec(a, b, p);
    if !val.is_zero() {
        return false;
    }
    // Check bounding box using direct comparisons
    // scalar_le(scalar_min(a.x, b.x), p.x)
    let min_x_le_px = if a.x.le(&b.x) { a.x.le(&p.x) } else { b.x.le(&p.x) };
    let px_le_max_x = if a.x.le(&b.x) { p.x.le(&b.x) } else { p.x.le(&a.x) };
    let min_y_le_py = if a.y.le(&b.y) { a.y.le(&p.y) } else { b.y.le(&p.y) };
    let py_le_max_y = if a.y.le(&b.y) { p.y.le(&b.y) } else { p.y.le(&a.y) };
    min_x_le_px && px_le_max_x && min_y_le_py && py_le_max_y
}

pub fn point_on_both_segments_2d_exec(
    p: &RuntimePoint2,
    a: &RuntimePoint2, b: &RuntimePoint2,
    c: &RuntimePoint2, d: &RuntimePoint2,
) -> (out: bool)
    requires
        p.wf_spec(),
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == point_on_both_segments_2d::<RationalModel>(p@, a@, b@, c@, d@),
{
    point_on_segment_inclusive_2d_exec(p, a, b) && point_on_segment_inclusive_2d_exec(p, c, d)
}

// ---------------------------------------------------------------------------
// 1D interval overlap for collinear case
// ---------------------------------------------------------------------------

pub fn collinear_overlap_kind_1d_exec(
    a1: &RuntimeRational, a2: &RuntimeRational,
    b1: &RuntimeRational, b2: &RuntimeRational,
) -> (out: i8)
    requires
        a1.wf_spec(),
        a2.wf_spec(),
        b1.wf_spec(),
        b2.wf_spec(),
    ensures
        (out == -1i8) == (collinear_overlap_kind_1d::<RationalModel>(a1@, a2@, b1@, b2@) < 0),
        (out == 0i8) == (collinear_overlap_kind_1d::<RationalModel>(a1@, a2@, b1@, b2@) == 0),
        (out == 1i8) == (collinear_overlap_kind_1d::<RationalModel>(a1@, a2@, b1@, b2@) > 0),
{
    // a_lo = min(a1, a2), a_hi = max(a1, a2)
    let a1_le_a2 = a1.le(a2);
    // b_lo = min(b1, b2), b_hi = max(b1, b2)
    let b1_le_b2 = b1.le(b2);
    // lo = max(a_lo, b_lo), hi = min(a_hi, b_hi)
    // lo = max(min(a1,a2), min(b1,b2))
    // hi = min(max(a1,a2), max(b1,b2))

    // Instead of materializing min/max RuntimeRationals, compare directly:
    // lo = max(a_lo, b_lo): if a_lo ≤ b_lo then b_lo else a_lo
    // hi = min(a_hi, b_hi): if a_hi ≤ b_hi then a_hi else b_hi
    // We need: if hi < lo → -1, if hi ≡ lo → 0, else 1

    // Get references to a_lo, a_hi, b_lo, b_hi
    let (a_lo, a_hi) = if a1_le_a2 { (a1, a2) } else { (a2, a1) };
    let (b_lo, b_hi) = if b1_le_b2 { (b1, b2) } else { (b2, b1) };

    // lo = max(a_lo, b_lo)
    let a_lo_le_b_lo = a_lo.le(b_lo);
    let lo = if a_lo_le_b_lo { b_lo } else { a_lo };

    // hi = min(a_hi, b_hi)
    let a_hi_le_b_hi = a_hi.le(b_hi);
    let hi = if a_hi_le_b_hi { a_hi } else { b_hi };

    // Compare hi vs lo
    if hi.lt(lo) {
        -1i8
    } else if hi.eq(lo) {
        0i8
    } else {
        1i8
    }
}

// ---------------------------------------------------------------------------
// Main classification exec
// ---------------------------------------------------------------------------

pub fn segment_intersection_kind_2d_exec(
    a: &RuntimePoint2, b: &RuntimePoint2,
    c: &RuntimePoint2, d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out == segment_intersection_kind_2d::<RationalModel>(a@, b@, c@, d@),
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
        // All collinear — check 1D overlap
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

} // verus!
