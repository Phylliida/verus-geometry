use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_linalg::vec2::Vec2;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;

verus! {

// =========================================================================
// Segment intersection classification enum
// =========================================================================

/// Coarse intersection relation for two closed 2D segments [ab] and [cd].
#[derive(PartialEq, Eq)]
pub enum SegmentIntersection2dKind {
    Disjoint,
    Proper,
    EndpointTouch,
    CollinearOverlap,
}

// =========================================================================
// Scalar ordering helpers (generic over OrderedRing)
// =========================================================================

/// min(a, b) using total order
pub open spec fn scalar_min<T: OrderedRing>(a: T, b: T) -> T {
    if a.le(b) { a } else { b }
}

/// max(a, b) using total order
pub open spec fn scalar_max<T: OrderedRing>(a: T, b: T) -> T {
    if a.le(b) { b } else { a }
}

/// a ≤ b in the ordered ring
pub open spec fn scalar_le<T: OrderedRing>(a: T, b: T) -> bool {
    a.le(b)
}

// =========================================================================
// Point-on-segment predicates
// =========================================================================

/// Point p lies on the closed segment [a, b]: collinear with a, b
/// and within the axis-aligned bounding box.
pub open spec fn point_on_segment_inclusive_2d<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    &&& orient2d(a, b, p).eqv(T::zero())
    &&& scalar_le(scalar_min(a.x, b.x), p.x)
    &&& scalar_le(p.x, scalar_max(a.x, b.x))
    &&& scalar_le(scalar_min(a.y, b.y), p.y)
    &&& scalar_le(p.y, scalar_max(a.y, b.y))
}

/// Point p lies on both segments [a, b] and [c, d].
pub open spec fn point_on_both_segments_2d<T: OrderedRing>(
    p: Point2<T>,
    a: Point2<T>, b: Point2<T>,
    c: Point2<T>, d: Point2<T>,
) -> bool {
    point_on_segment_inclusive_2d(p, a, b) && point_on_segment_inclusive_2d(p, c, d)
}

// =========================================================================
// 1D interval overlap for collinear case
// =========================================================================

/// Classify 1D interval overlap between [a1, a2] and [b1, b2].
/// Returns: -1 disjoint, 0 single point, 1 interval overlap.
pub open spec fn collinear_overlap_kind_1d<T: OrderedRing>(
    a1: T, a2: T, b1: T, b2: T,
) -> int {
    let a_lo = scalar_min(a1, a2);
    let a_hi = scalar_max(a1, a2);
    let b_lo = scalar_min(b1, b2);
    let b_hi = scalar_max(b1, b2);
    let lo = scalar_max(a_lo, b_lo);
    let hi = scalar_min(a_hi, b_hi);
    if hi.lt(lo) {
        -1int
    } else if hi.eqv(lo) {
        0int
    } else {
        1int
    }
}

// =========================================================================
// Main classification spec
// =========================================================================

/// Classify the intersection of closed segments [a,b] and [c,d].
///
/// Algorithm: compute 4 orientation signs, then branch:
/// - All zero → collinear, check 1D overlap
/// - All nonzero with opposite-sign pairs → Proper
/// - Some endpoint on other segment → EndpointTouch
/// - Otherwise → Disjoint
pub open spec fn segment_intersection_kind_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> SegmentIntersection2dKind {
    let o1 = orient2d_sign(a, b, c);
    let o2 = orient2d_sign(a, b, d);
    let o3 = orient2d_sign(c, d, a);
    let o4 = orient2d_sign(c, d, b);
    let touch1 = point_on_both_segments_2d(c, a, b, c, d);
    let touch2 = point_on_both_segments_2d(d, a, b, c, d);
    let touch3 = point_on_both_segments_2d(a, a, b, c, d);
    let touch4 = point_on_both_segments_2d(b, a, b, c, d);
    if o1 == OrientationSign::Zero && o2 == OrientationSign::Zero
        && o3 == OrientationSign::Zero && o4 == OrientationSign::Zero
    {
        // All collinear — check 1D overlap
        // Use x-axis unless segments are vertical, then y-axis
        let use_x = !a.x.eqv(b.x) || !c.x.eqv(d.x);
        let overlap_kind = if use_x {
            collinear_overlap_kind_1d(a.x, b.x, c.x, d.x)
        } else {
            collinear_overlap_kind_1d(a.y, b.y, c.y, d.y)
        };
        if overlap_kind < 0 {
            SegmentIntersection2dKind::Disjoint
        } else if overlap_kind == 0 && (touch1 || touch2 || touch3 || touch4) {
            SegmentIntersection2dKind::EndpointTouch
        } else {
            SegmentIntersection2dKind::CollinearOverlap
        }
    } else if o1 != OrientationSign::Zero && o2 != OrientationSign::Zero
        && o3 != OrientationSign::Zero && o4 != OrientationSign::Zero
        && o1 != o2 && o3 != o4
    {
        SegmentIntersection2dKind::Proper
    } else if touch1 || touch2 || touch3 || touch4 {
        SegmentIntersection2dKind::EndpointTouch
    } else {
        SegmentIntersection2dKind::Disjoint
    }
}

// =========================================================================
// Lemmas
// =========================================================================

/// Proper intersection implies all 4 orientation signs are nonzero
/// and segments straddle each other.
pub proof fn lemma_proper_implies_straddling<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        orient2d_sign(a, b, c) != OrientationSign::Zero,
        orient2d_sign(a, b, d) != OrientationSign::Zero,
        orient2d_sign(c, d, a) != OrientationSign::Zero,
        orient2d_sign(c, d, b) != OrientationSign::Zero,
        orient2d_sign(a, b, c) != orient2d_sign(a, b, d),
        orient2d_sign(c, d, a) != orient2d_sign(c, d, b),
{
    // Direct from the definition: the Proper branch requires
    // all nonzero and opposite-sign pairs.
}

/// Proper intersection implies c and d are on opposite sides of line(a, b).
pub proof fn lemma_proper_implies_cd_opposite_sides<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        (orient2d_positive(a, b, c) && orient2d_negative(a, b, d))
        || (orient2d_negative(a, b, c) && orient2d_positive(a, b, d)),
{
    lemma_proper_implies_straddling::<T>(a, b, c, d);
    lemma_orient2d_sign_matches::<T>(a, b, c);
    lemma_orient2d_sign_matches::<T>(a, b, d);
    lemma_orient2d_trichotomy::<T>(a, b, c);
    lemma_orient2d_trichotomy::<T>(a, b, d);
}

/// Proper intersection implies a and b are on opposite sides of line(c, d).
pub proof fn lemma_proper_implies_ab_opposite_sides<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        (orient2d_positive(c, d, a) && orient2d_negative(c, d, b))
        || (orient2d_negative(c, d, a) && orient2d_positive(c, d, b)),
{
    lemma_proper_implies_straddling::<T>(a, b, c, d);
    lemma_orient2d_sign_matches::<T>(c, d, a);
    lemma_orient2d_sign_matches::<T>(c, d, b);
    lemma_orient2d_trichotomy::<T>(c, d, a);
    lemma_orient2d_trichotomy::<T>(c, d, b);
}

/// The classification returns exactly one of the four kinds (exhaustive + pairwise disjoint).
pub proof fn lemma_classification_exhaustive<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures ({
        let k = segment_intersection_kind_2d(a, b, c, d);
        &&& (k == SegmentIntersection2dKind::Disjoint
             || k == SegmentIntersection2dKind::Proper
             || k == SegmentIntersection2dKind::EndpointTouch
             || k == SegmentIntersection2dKind::CollinearOverlap)
        // Pairwise disjoint
        &&& !(k == SegmentIntersection2dKind::Disjoint && k == SegmentIntersection2dKind::Proper)
        &&& !(k == SegmentIntersection2dKind::Disjoint && k == SegmentIntersection2dKind::EndpointTouch)
        &&& !(k == SegmentIntersection2dKind::Disjoint && k == SegmentIntersection2dKind::CollinearOverlap)
        &&& !(k == SegmentIntersection2dKind::Proper && k == SegmentIntersection2dKind::EndpointTouch)
        &&& !(k == SegmentIntersection2dKind::Proper && k == SegmentIntersection2dKind::CollinearOverlap)
        &&& !(k == SegmentIntersection2dKind::EndpointTouch && k == SegmentIntersection2dKind::CollinearOverlap)
    }),
{
    // The spec function returns exactly one enum variant via if/else branching.
    // Pairwise disjointness follows from enum equality.
}

/// CollinearOverlap implies all four points are collinear.
pub proof fn lemma_collinear_overlap_implies_collinear<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::CollinearOverlap,
    ensures
        orient2d_zero(a, b, c),
        orient2d_zero(a, b, d),
        orient2d_zero(c, d, a),
        orient2d_zero(c, d, b),
{
    lemma_orient2d_sign_matches::<T>(a, b, c);
    lemma_orient2d_sign_matches::<T>(a, b, d);
    lemma_orient2d_sign_matches::<T>(c, d, a);
    lemma_orient2d_sign_matches::<T>(c, d, b);
}

// =========================================================================
// Denominator nonzero for Proper intersection (2D)
// =========================================================================

/// The denominator orient2d(c,d,a) - orient2d(c,d,b) is nonzero
/// when the segment intersection is Proper.
///
/// This follows the same pattern as the 3D `lemma_crossing_denominator_nonzero`.
/// From Proper: orient2d_sign(c,d,a) and orient2d_sign(c,d,b) are both nonzero
/// and have opposite signs, so their difference cannot be zero.
pub proof fn lemma_proper_denominator_nonzero_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let o3 = orient2d(c, d, a);
        let o4 = orient2d(c, d, b);
        !o3.add(o4.neg()).eqv(T::zero())
    }),
{
    let o3 = orient2d(c, d, a);
    let o4 = orient2d(c, d, b);
    let denom = o3.add(o4.neg());

    // From Proper: o3 and o4 are both nonzero with opposite signs.
    lemma_proper_implies_ab_opposite_sides::<T>(a, b, c, d);

    // Contradiction proof: if denom ≡ 0 then o3 ≡ o4, but they have opposite signs.
    if denom.eqv(T::zero()) {
        // o3 + (-o4) ≡ 0 implies (-o4) ≡ -(o3)
        additive_group_lemmas::lemma_neg_unique::<T>(o3, o4.neg());
        // neg both sides: o4 ≡ o3
        T::axiom_neg_congruence(o4.neg(), o3.neg());
        additive_group_lemmas::lemma_neg_involution::<T>(o4);
        additive_group_lemmas::lemma_neg_involution::<T>(o3);
        T::axiom_eqv_symmetric(o4.neg().neg(), o4);
        T::axiom_eqv_transitive(o4, o4.neg().neg(), o3.neg().neg());
        T::axiom_eqv_transitive(o4, o3.neg().neg(), o3);

        if orient2d_positive(c, d, a) && orient2d_negative(c, d, b) {
            // o3 > 0 and o4 < 0, but o4 ≡ o3 → 0 < o4 (from 0 < o3 + congruence)
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o3);
            T::axiom_eqv_symmetric(o4, o3);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o3, o4);
            // 0 ≤ o4, but o4 < 0 → o4 ≤ 0, contradiction with antisymmetric
            T::axiom_lt_iff_le_and_not_eqv(o4, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o4);
            T::axiom_eqv_symmetric(T::zero(), o4);
        } else {
            // o3 < 0 and o4 > 0, but o4 ≡ o3 → o4 < 0 (from o3 < 0 + congruence)
            T::axiom_eqv_symmetric(o4, o3);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o4);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o4, o3);
            T::axiom_lt_iff_le_and_not_eqv(o3, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o3);
            T::axiom_eqv_symmetric(T::zero(), o3);
        }
    }
}

} // verus!
