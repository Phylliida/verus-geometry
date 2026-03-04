use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::scale as scale2;
use crate::point2::*;
use crate::orient2d::*;
use crate::orientation_sign::*;
use crate::intersection3d::{
    lemma_neg_of_neg_is_pos, lemma_neg_of_pos_is_neg,
    lemma_lt_congruence_both, lemma_lt_transfer_eqv,
    lemma_positive_ratio_bounds, lemma_sum_of_negatives_is_negative,
};

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

// =========================================================================
// 2D Segment intersection point spec
// =========================================================================

/// Intersection parameter t for segments [a,b] and [c,d] (2D).
///
/// t = orient2d(c,d,a) / (orient2d(c,d,a) - orient2d(c,d,b))
///
/// Parallel to the 3D `segment_plane_intersection_parameter`.
pub open spec fn segment_intersection_parameter_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> T {
    let o3 = orient2d(c, d, a);
    let o4 = orient2d(c, d, b);
    o3.div(o3.add(o4.neg()))
}

/// The intersection point: a + t * (b - a).
pub open spec fn segment_intersection_point_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> Point2<T> {
    let t = segment_intersection_parameter_2d(a, b, c, d);
    let dir = sub2(b, a);
    add_vec2(a, scale2(t, dir))
}

// =========================================================================
// On-line proof: intersection point lies on line(a, b)
// =========================================================================

/// sub2(add_vec2(a, v), a) ≡ v
pub proof fn lemma_sub2_add_vec2_cancel<T: Ring>(a: Point2<T>, v: Vec2<T>)
    ensures
        sub2(add_vec2(a, v), a).eqv(v),
{
    // Component x: (a.x + v.x) - a.x ≡ v.x
    T::axiom_add_commutative(a.x, v.x);
    T::axiom_eqv_reflexive(a.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.add(v.x), v.x.add(a.x), a.x, a.x,
    );
    additive_group_lemmas::lemma_add_then_sub_cancel::<T>(v.x, a.x);
    T::axiom_eqv_transitive(
        a.x.add(v.x).sub(a.x), v.x.add(a.x).sub(a.x), v.x,
    );

    // Component y: same
    T::axiom_add_commutative(a.y, v.y);
    T::axiom_eqv_reflexive(a.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.add(v.y), v.y.add(a.y), a.y, a.y,
    );
    additive_group_lemmas::lemma_add_then_sub_cancel::<T>(v.y, a.y);
    T::axiom_eqv_transitive(
        a.y.add(v.y).sub(a.y), v.y.add(a.y).sub(a.y), v.y,
    );
}

/// The intersection point lies on line(a, b): orient2d(a, b, p) ≡ 0.
///
/// Proof: p = a + t*(b-a), so p-a = t*(b-a).
/// orient2d(a,b,p) = det2d(b-a, p-a) = det2d(b-a, t*(b-a))
///                 = t * det2d(b-a, b-a) = t * 0 = 0.
pub proof fn lemma_intersection_point_on_line_ab_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures ({
        let p = segment_intersection_point_2d(a, b, c, d);
        orient2d(a, b, p).eqv(T::zero())
    }),
{
    let t = segment_intersection_parameter_2d(a, b, c, d);
    let dir = sub2(b, a);
    let w = scale2(t, dir);
    let p = add_vec2(a, w);

    // Step 1: sub2(p, a) ≡ w = scale2(t, dir)
    lemma_sub2_add_vec2_cancel::<T>(a, w);

    // Step 2: det2d congruence: det2d(dir, sub2(p, a)) ≡ det2d(dir, w)
    Vec2::<T>::axiom_eqv_reflexive(dir);
    lemma_det2d_congruence::<T>(dir, dir, sub2(p, a), w);

    // Step 3: w = scale2(t, dir), so det2d(dir, w) = det2d(dir, scale(t, dir))
    //         ≡ t * det2d(dir, dir)  [scale_right]
    lemma_det2d_scale_right::<T>(t, dir, dir);

    // Step 4: det2d(dir, dir) ≡ 0  [self_zero]
    lemma_det2d_self_zero::<T>(dir);

    // Step 5: t * det2d(dir, dir) ≡ t * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(t, det2d(dir, dir), T::zero());
    T::axiom_mul_zero_right(t);
    T::axiom_eqv_transitive(
        t.mul(det2d(dir, dir)), t.mul(T::zero()), T::zero(),
    );

    // Chain: orient2d(a,b,p) = det2d(dir, sub2(p,a))
    //        ≡ det2d(dir, w)               [Step 2]
    //        ≡ t * det2d(dir, dir)          [Step 3]
    //        ≡ 0                            [Steps 4-5]
    T::axiom_eqv_transitive(
        det2d(dir, sub2(p, a)),
        det2d(dir, w),
        t.mul(det2d(dir, dir)),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, p),
        t.mul(det2d(dir, dir)),
        T::zero(),
    );
}

// =========================================================================
// On-line proof: intersection point lies on line(c, d)
// =========================================================================

/// sub2(add_vec2(a, v), c) componentwise:
/// Vec2 { x: (a.x - c.x) + v.x, y: (a.y - c.y) + v.y }
///
/// i.e. sub2(add_vec2(a, v), c) ≡ Vec2 { x: sub2(a,c).x + v.x, y: sub2(a,c).y + v.y }
pub proof fn lemma_sub2_add_vec2_decompose<T: Ring>(a: Point2<T>, v: Vec2<T>, c: Point2<T>)
    ensures
        sub2(add_vec2(a, v), c).eqv(
            Vec2 { x: sub2(a, c).x.add(v.x), y: sub2(a, c).y.add(v.y) }
        ),
{
    // x component: (a.x + v.x) - c.x ≡ (a.x - c.x) + v.x
    // Expand: (a.x + v.x) - c.x = (a.x + v.x) + (-c.x)
    T::axiom_sub_is_add_neg(a.x.add(v.x), c.x);
    // (a.x + v.x) + (-c.x): rearrange via associativity
    // = a.x + (v.x + (-c.x))  [assoc]
    T::axiom_add_associative(a.x, v.x, c.x.neg());
    T::axiom_eqv_transitive(
        a.x.add(v.x).sub(c.x),
        a.x.add(v.x).add(c.x.neg()),
        a.x.add(v.x.add(c.x.neg())),
    );
    // v.x + (-c.x) = (-c.x) + v.x  [comm]
    T::axiom_add_commutative(v.x, c.x.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.x, v.x.add(c.x.neg()), c.x.neg().add(v.x));
    T::axiom_eqv_transitive(
        a.x.add(v.x).sub(c.x),
        a.x.add(v.x.add(c.x.neg())),
        a.x.add(c.x.neg().add(v.x)),
    );
    // a.x + ((-c.x) + v.x) = (a.x + (-c.x)) + v.x  [assoc backwards]
    T::axiom_add_associative(a.x, c.x.neg(), v.x);
    T::axiom_eqv_symmetric(a.x.add(c.x.neg()).add(v.x), a.x.add(c.x.neg().add(v.x)));
    T::axiom_eqv_transitive(
        a.x.add(v.x).sub(c.x),
        a.x.add(c.x.neg().add(v.x)),
        a.x.add(c.x.neg()).add(v.x),
    );
    // a.x + (-c.x) ≡ a.x - c.x  [sub_is_add_neg backwards]
    T::axiom_sub_is_add_neg(a.x, c.x);
    T::axiom_eqv_symmetric(a.x.sub(c.x), a.x.add(c.x.neg()));
    T::axiom_add_congruence_left(a.x.add(c.x.neg()), a.x.sub(c.x), v.x);
    T::axiom_eqv_transitive(
        a.x.add(v.x).sub(c.x),
        a.x.add(c.x.neg()).add(v.x),
        a.x.sub(c.x).add(v.x),
    );

    // y component: same
    T::axiom_sub_is_add_neg(a.y.add(v.y), c.y);
    T::axiom_add_associative(a.y, v.y, c.y.neg());
    T::axiom_eqv_transitive(
        a.y.add(v.y).sub(c.y),
        a.y.add(v.y).add(c.y.neg()),
        a.y.add(v.y.add(c.y.neg())),
    );
    T::axiom_add_commutative(v.y, c.y.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.y, v.y.add(c.y.neg()), c.y.neg().add(v.y));
    T::axiom_eqv_transitive(
        a.y.add(v.y).sub(c.y),
        a.y.add(v.y.add(c.y.neg())),
        a.y.add(c.y.neg().add(v.y)),
    );
    T::axiom_add_associative(a.y, c.y.neg(), v.y);
    T::axiom_eqv_symmetric(a.y.add(c.y.neg()).add(v.y), a.y.add(c.y.neg().add(v.y)));
    T::axiom_eqv_transitive(
        a.y.add(v.y).sub(c.y),
        a.y.add(c.y.neg().add(v.y)),
        a.y.add(c.y.neg()).add(v.y),
    );
    T::axiom_sub_is_add_neg(a.y, c.y);
    T::axiom_eqv_symmetric(a.y.sub(c.y), a.y.add(c.y.neg()));
    T::axiom_add_congruence_left(a.y.add(c.y.neg()), a.y.sub(c.y), v.y);
    T::axiom_eqv_transitive(
        a.y.add(v.y).sub(c.y),
        a.y.add(c.y.neg()).add(v.y),
        a.y.sub(c.y).add(v.y),
    );
}

/// The intersection point lies on line(c, d): orient2d(c, d, p) ≡ 0.
///
/// Proof outline:
///   p = a + t*(b-a) where t = o3/(o3-o4).
///   p - c = (a - c) + t*(b - a).
///   orient2d(c,d,p) = det2d(d-c, p-c)
///     = det2d(d-c, a-c) + det2d(d-c, t*(b-a))       [add_right]
///     = o3 + t * det2d(d-c, b-a)                     [scale_right]
///     = o3 + t * (o4 - o3)                           [sub_right: b-a = (b-c)-(a-c)]
///     = o3 + [o3/den] * (-den)                       [den = o3-o4, o4-o3 = -den]
///     = o3 + (-o3) = 0
pub proof fn lemma_intersection_point_on_line_cd_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let p = segment_intersection_point_2d(a, b, c, d);
        orient2d(c, d, p).eqv(T::zero())
    }),
{
    let o3 = orient2d(c, d, a);
    let o4 = orient2d(c, d, b);
    let den = o3.sub(o4); // o3 - o4

    // den is nonzero
    lemma_proper_denominator_nonzero_2d::<T>(a, b, c, d);
    // The denominator in the spec is o3 + (-o4) = o3 - o4
    // Need: o3.add(o4.neg()) ≡ o3.sub(o4)
    T::axiom_sub_is_add_neg(o3, o4);
    T::axiom_eqv_symmetric(o3.sub(o4), o3.add(o4.neg()));
    // So !den.eqv(T::zero())

    let t = segment_intersection_parameter_2d(a, b, c, d);
    let dir = sub2(b, a);
    let w = scale2(t, dir);
    let p = add_vec2(a, w);
    let dc = sub2(d, c);
    let ac = sub2(a, c);

    // ---------------------------------------------------------------
    // Step 1: sub2(p, c) ≡ Vec2 { x: ac.x + w.x, y: ac.y + w.y }
    // ---------------------------------------------------------------
    lemma_sub2_add_vec2_decompose::<T>(a, w, c);
    let pc_decomposed = Vec2 { x: ac.x.add(w.x), y: ac.y.add(w.y) };

    // ---------------------------------------------------------------
    // Step 2: det2d(dc, sub2(p,c)) ≡ det2d(dc, pc_decomposed)
    // ---------------------------------------------------------------
    Vec2::<T>::axiom_eqv_reflexive(dc);
    lemma_det2d_congruence::<T>(dc, dc, sub2(p, c), pc_decomposed);

    // ---------------------------------------------------------------
    // Step 3: det2d(dc, pc_decomposed) = det2d(dc, ac + w)
    //         ≡ det2d(dc, ac) + det2d(dc, w)  [add_right]
    // ---------------------------------------------------------------
    lemma_det2d_add_right::<T>(dc, ac, w);

    T::axiom_eqv_transitive(
        orient2d(c, d, p),  // = det2d(dc, sub2(p,c))
        det2d(dc, pc_decomposed),
        det2d(dc, ac).add(det2d(dc, w)),
    );

    // det2d(dc, ac) = orient2d(c, d, a) = o3
    // (this is definitional — orient2d(c,d,a) = det2d(sub2(d,c), sub2(a,c)) = det2d(dc, ac))

    // ---------------------------------------------------------------
    // Step 4: det2d(dc, w) = det2d(dc, scale(t, dir))
    //         ≡ t * det2d(dc, dir)  [scale_right]
    // ---------------------------------------------------------------
    lemma_det2d_scale_right::<T>(t, dc, dir);

    // o3 + det2d(dc, w) ≡ o3 + t * det2d(dc, dir)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o3, det2d(dc, w), t.mul(det2d(dc, dir)),
    );
    T::axiom_eqv_transitive(
        orient2d(c, d, p),
        o3.add(det2d(dc, w)),
        o3.add(t.mul(det2d(dc, dir))),
    );

    // ---------------------------------------------------------------
    // Step 5: det2d(dc, dir) = det2d(dc, b-a)
    //         dir = b - a = (b - c) - (a - c) at component level
    //         det2d(dc, (b-c) - (a-c)) ≡ det2d(dc, b-c) - det2d(dc, a-c)
    //         = o4 - o3
    // ---------------------------------------------------------------
    // Need: dir = sub2(b,a) componentwise = sub2(b,c) - sub2(a,c)
    // b.x - a.x = (b.x - c.x) - (a.x - c.x): via sub_add_sub
    let bc = sub2(b, c);

    // Show dir ≡ Vec2 { x: bc.x - ac.x, y: bc.y - ac.y } = bc_minus_ac
    let bc_minus_ac = Vec2 { x: bc.x.sub(ac.x), y: bc.y.sub(ac.y) };

    // x: b.x-a.x ≡ (b.x-c.x)-(a.x-c.x)
    // sub_add_sub: p.sub(q).add(q.sub(r)) ≡ p.sub(r)
    // With p=b.x, q=c.x, r=a.x: (b.x-c.x)+(c.x-a.x) ≡ b.x-a.x
    // But we want (b.x-c.x)-(a.x-c.x).
    // (a.x-c.x) = -(c.x-a.x) via sub_antisymmetric,
    // so -(a.x-c.x) = c.x-a.x
    // (b.x-c.x) - (a.x-c.x) = (b.x-c.x) + (-(a.x-c.x)) = (b.x-c.x) + (c.x-a.x) ≡ b.x-a.x
    T::axiom_sub_is_add_neg(bc.x, ac.x);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(ac.x, c.x.sub(a.x));
    // ac.x = a.x - c.x, and sub_antisymmetric: a.sub(b) ≡ b.sub(a).neg()
    // Actually we need -(a.x-c.x) ≡ c.x-a.x
    // sub_neg_both from additive_group_lemmas gives: -(a-b) ≡ b-a
    additive_group_lemmas::lemma_sub_neg_both::<T>(a.x, c.x);
    // -(a.x - c.x) ≡ c.x - a.x ... wait, lemma_sub_neg_both is (-a)-(-b) ≡ b-a
    // Actually I need lemma that -(a.x - c.x) ≡ c.x - a.x. Let me check.
    // sub_antisymmetric: a.sub(b) ≡ b.sub(a).neg()
    // So: a.x.sub(c.x) ≡ c.x.sub(a.x).neg()
    // neg both sides: a.x.sub(c.x).neg() ≡ c.x.sub(a.x).neg().neg() ≡ c.x.sub(a.x)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.x, c.x);
    // a.x-c.x ≡ -(c.x-a.x)
    T::axiom_neg_congruence(a.x.sub(c.x), c.x.sub(a.x).neg());
    // -(a.x-c.x) ≡ -(-(c.x-a.x))
    additive_group_lemmas::lemma_neg_involution::<T>(c.x.sub(a.x));
    // -(-(c.x-a.x)) ≡ c.x-a.x
    T::axiom_eqv_transitive(
        ac.x.neg(), c.x.sub(a.x).neg().neg(), c.x.sub(a.x),
    );

    // (b.x-c.x) + (-(a.x-c.x)) ≡ (b.x-c.x) + (c.x-a.x)
    additive_group_lemmas::lemma_add_congruence_right::<T>(bc.x, ac.x.neg(), c.x.sub(a.x));
    // bc.x - ac.x ≡ bc.x + (-(ac.x)) ≡ bc.x + (c.x - a.x) ≡ b.x - a.x
    T::axiom_eqv_transitive(
        bc.x.sub(ac.x), bc.x.add(ac.x.neg()), bc.x.add(c.x.sub(a.x)),
    );
    // (b.x-c.x) + (c.x-a.x) ≡ b.x-a.x via sub_add_sub
    additive_group_lemmas::lemma_sub_add_sub::<T>(b.x, c.x, a.x);
    T::axiom_eqv_transitive(
        bc.x.sub(ac.x), bc.x.add(c.x.sub(a.x)), b.x.sub(a.x),
    );

    // y: same
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.y, c.y);
    T::axiom_neg_congruence(a.y.sub(c.y), c.y.sub(a.y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(c.y.sub(a.y));
    T::axiom_eqv_transitive(
        ac.y.neg(), c.y.sub(a.y).neg().neg(), c.y.sub(a.y),
    );
    T::axiom_sub_is_add_neg(bc.y, ac.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(bc.y, ac.y.neg(), c.y.sub(a.y));
    T::axiom_eqv_transitive(
        bc.y.sub(ac.y), bc.y.add(ac.y.neg()), bc.y.add(c.y.sub(a.y)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(b.y, c.y, a.y);
    T::axiom_eqv_transitive(
        bc.y.sub(ac.y), bc.y.add(c.y.sub(a.y)), b.y.sub(a.y),
    );

    // So bc_minus_ac ≡ dir (swap direction)
    T::axiom_eqv_symmetric(bc.x.sub(ac.x), dir.x);
    T::axiom_eqv_symmetric(bc.y.sub(ac.y), dir.y);

    // det2d(dc, dir) ≡ det2d(dc, bc_minus_ac) via congruence
    lemma_det2d_congruence::<T>(dc, dc, dir, bc_minus_ac);

    // det2d(dc, bc_minus_ac) ≡ det2d(dc, bc) - det2d(dc, ac)  [sub_right]
    lemma_det2d_sub_right::<T>(dc, bc, ac);

    // det2d(dc, dir) ≡ det2d(dc, bc) - det2d(dc, ac) = o4 - o3
    T::axiom_eqv_transitive(
        det2d(dc, dir),
        det2d(dc, bc_minus_ac),
        det2d(dc, bc).sub(det2d(dc, ac)),
    );
    // det2d(dc, bc) = orient2d(c,d,b) = o4, det2d(dc, ac) = orient2d(c,d,a) = o3
    // So det2d(dc, dir) ≡ o4 - o3

    // ---------------------------------------------------------------
    // Step 6: t * det2d(dc, dir) ≡ t * (o4 - o3)
    // ---------------------------------------------------------------
    ring_lemmas::lemma_mul_congruence_right::<T>(t, det2d(dc, dir), o4.sub(o3));
    // o3 + t * det2d(dc, dir) ≡ o3 + t * (o4 - o3)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o3, t.mul(det2d(dc, dir)), t.mul(o4.sub(o3)),
    );
    T::axiom_eqv_transitive(
        orient2d(c, d, p),
        o3.add(t.mul(det2d(dc, dir))),
        o3.add(t.mul(o4.sub(o3))),
    );

    // ---------------------------------------------------------------
    // Step 7: t * (o4 - o3) where t = o3 / (o3 - o4)
    //   o4 - o3 = -(o3 - o4) = -den
    //   t * (o4 - o3) = t * (-den) = [o3 * recip(den)] * (-den)
    //                 = o3 * [recip(den) * (-den)]
    //                 = o3 * [-(recip(den) * den)]
    //                 = o3 * (-1) = -o3
    // ---------------------------------------------------------------

    // o4 - o3 ≡ -(o3 - o4) = -den
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(o4, o3);
    // o4 - o3 ≡ -(o3 - o4)

    // t * (o4-o3) ≡ t * (-(o3-o4)) = t * (-den)
    ring_lemmas::lemma_mul_congruence_right::<T>(t, o4.sub(o3), o3.sub(o4).neg());

    // t = o3.div(o3.add(o4.neg()))
    // o3.add(o4.neg()) ≡ o3.sub(o4) = den (already shown above)
    // So t ≡ o3.div(den) via div congruence? Actually t IS o3.div(o3.add(o4.neg())).
    // We need: t ≡ o3.mul(den.recip())
    // axiom_div_is_mul_recip: a.div(b) ≡ a.mul(b.recip())
    T::axiom_div_is_mul_recip(o3, o3.add(o4.neg()));
    // t = o3.div(o3.add(o4.neg())) ≡ o3.mul(o3.add(o4.neg()).recip())

    // o3.add(o4.neg()).recip() ≡ den.recip() via recip_congruence
    // First show !o3.add(o4.neg()).eqv(T::zero()) — already from denominator nonzero
    T::axiom_recip_congruence(o3.add(o4.neg()), den);
    // o3.add(o4.neg()).recip() ≡ den.recip()

    // t ≡ o3.mul(o3.add(o4.neg()).recip()) ≡ o3.mul(den.recip())
    ring_lemmas::lemma_mul_congruence_right::<T>(
        o3, o3.add(o4.neg()).recip(), den.recip(),
    );
    T::axiom_eqv_transitive(
        t, o3.mul(o3.add(o4.neg()).recip()), o3.mul(den.recip()),
    );

    // t * (-den) ≡ o3.mul(den.recip()) * (-den)
    T::axiom_mul_congruence_left(t, o3.mul(den.recip()), den.neg());
    T::axiom_eqv_transitive(
        t.mul(o4.sub(o3)),
        t.mul(den.neg()),
        o3.mul(den.recip()).mul(den.neg()),
    );

    // o3 * recip(den) * (-den) = o3 * (recip(den) * (-den))  [assoc]
    T::axiom_mul_associative(o3, den.recip(), den.neg());

    // recip(den) * (-den) ≡ -(recip(den) * den)  [mul_neg_right]
    ring_lemmas::lemma_mul_neg_right::<T>(den.recip(), den);

    // recip(den) * den: use axiom_mul_recip_right in reverse
    // axiom_mul_recip_right: a * a.recip() ≡ 1 (for a ≠ 0)
    // We need recip(den) * den ≡ 1
    // den * recip(den) ≡ 1 [axiom], recip(den) * den ≡ den * recip(den) [comm] ≡ 1
    // But !den.eqv(T::zero()) — need to establish this
    // We have !o3.add(o4.neg()).eqv(T::zero()), and den = o3.sub(o4) ≡ o3.add(o4.neg())
    // So if den.eqv(T::zero()), then o3.add(o4.neg()).eqv(T::zero()) via transitivity — contradiction
    // Actually let's just use den directly. We need !den.eqv(T::zero()).
    // den = o3.sub(o4), o3.add(o4.neg()) ≡ den. If den ≡ 0 then o3.add(o4.neg()) ≡ 0 — contradiction.
    if den.eqv(T::zero()) {
        T::axiom_eqv_symmetric(o3.sub(o4), o3.add(o4.neg()));
        T::axiom_eqv_transitive(o3.add(o4.neg()), den, T::zero());
        // contradiction with !o3.add(o4.neg()).eqv(T::zero())
    }

    T::axiom_mul_recip_right(den);
    // den * recip(den) ≡ 1
    T::axiom_mul_commutative(den.recip(), den);
    // recip(den) * den ≡ den * recip(den)
    T::axiom_eqv_transitive(den.recip().mul(den), den.mul(den.recip()), T::one());

    // -(recip(den) * den) ≡ -(1) = -1... actually we don't need -1,
    // we need o3 * (-(recip(den)*den)) ≡ o3 * (-1) ≡ -o3
    T::axiom_neg_congruence(den.recip().mul(den), T::one());
    // -(recip(den)*den) ≡ -(1)

    // recip(den) * (-den) ≡ -(recip(den) * den) ≡ -(1)
    T::axiom_eqv_transitive(
        den.recip().mul(den.neg()),
        den.recip().mul(den).neg(),
        T::one().neg(),
    );

    // o3 * (recip(den) * (-den)) ≡ o3 * (-1)
    ring_lemmas::lemma_mul_congruence_right::<T>(o3, den.recip().mul(den.neg()), T::one().neg());

    // o3 * recip(den) * (-den) ≡ o3 * (recip(den) * (-den))  [assoc, already proved]
    // chain: o3*recip(den)*(-den) ≡ o3*(recip(den)*(-den)) ≡ o3*(-1)
    T::axiom_eqv_transitive(
        o3.mul(den.recip()).mul(den.neg()),
        o3.mul(den.recip().mul(den.neg())),
        o3.mul(T::one().neg()),
    );

    // o3 * (-1) ≡ -(o3 * 1) ≡ -(o3) = -o3  [mul_neg_right, mul_one]
    ring_lemmas::lemma_mul_neg_right::<T>(o3, T::one());
    // o3 * (-1) ≡ -(o3 * 1)
    T::axiom_mul_one_right(o3);
    // o3 * 1 ≡ o3
    T::axiom_neg_congruence(o3.mul(T::one()), o3);
    // -(o3*1) ≡ -o3
    T::axiom_eqv_transitive(
        o3.mul(T::one().neg()),
        o3.mul(T::one()).neg(),
        o3.neg(),
    );

    // Chain: t*(o4-o3) ≡ o3*recip(den)*(-den) ≡ o3*(-1) ≡ -o3
    T::axiom_eqv_transitive(
        t.mul(o4.sub(o3)),
        o3.mul(den.recip()).mul(den.neg()),
        o3.mul(T::one().neg()),
    );
    T::axiom_eqv_transitive(
        t.mul(o4.sub(o3)),
        o3.mul(T::one().neg()),
        o3.neg(),
    );

    // ---------------------------------------------------------------
    // Step 8: o3 + t*(o4-o3) ≡ o3 + (-o3) ≡ 0
    // ---------------------------------------------------------------
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o3, t.mul(o4.sub(o3)), o3.neg(),
    );
    // o3 + t*(o4-o3) ≡ o3 + (-o3)
    T::axiom_add_inverse_right(o3);
    // o3 + (-o3) ≡ 0

    // Combine steps 6 and 8:
    // orient2d(c,d,p) ≡ o3 + t*(o4-o3) ≡ o3 + (-o3) ≡ 0
    T::axiom_eqv_transitive(
        o3.add(t.mul(o4.sub(o3))),
        o3.add(o3.neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        orient2d(c, d, p),
        o3.add(t.mul(o4.sub(o3))),
        o3.add(o3.neg()),
    );
    T::axiom_eqv_transitive(
        orient2d(c, d, p),
        o3.add(o3.neg()),
        T::zero(),
    );
}

// =========================================================================
// Parameter bounds: 0 < t < 1 for Proper 2D intersection
// =========================================================================

/// For Proper 2D intersection, 0 < t and t < 1.
///
/// Proof: o3 and o4 have opposite signs (from Proper).
/// Case 1: o3 > 0, o4 < 0 → denom > 0, 0 < o3 < denom → 0 < t < 1.
/// Case 2: o3 < 0, o4 > 0 → denom < 0 → negate both → 0 < t < 1.
pub proof fn lemma_proper_parameter_bounds_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let t = segment_intersection_parameter_2d(a, b, c, d);
        T::zero().lt(t) && t.lt(T::one())
    }),
{
    let o3 = orient2d(c, d, a);
    let o4 = orient2d(c, d, b);
    let denom = o3.add(o4.neg());
    let t = o3.div(denom);

    lemma_proper_denominator_nonzero_2d::<T>(a, b, c, d);
    lemma_proper_implies_ab_opposite_sides::<T>(a, b, c, d);

    if orient2d_positive(c, d, a) && orient2d_negative(c, d, b) {
        // Case 1: o3 > 0, o4 < 0
        // Show 0 < -o4
        lemma_neg_of_neg_is_pos::<T>(o4);

        // Show o3 < denom: 0 < -o4 → o3 + 0 < o3 + (-o4) = denom
        // lt_add_compatible(0, -o4, o3): 0 < -o4 → 0+o3 < (-o4)+o3
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(T::zero(), o4.neg(), o3);
        // 0+o3 ≡ o3
        additive_group_lemmas::lemma_add_zero_left::<T>(o3);
        // (-o4)+o3 ≡ o3+(-o4) = denom
        T::axiom_add_commutative(o4.neg(), o3);
        // Transfer: 0+o3 < (-o4)+o3 → o3 < denom
        lemma_lt_congruence_both::<T>(
            T::zero().add(o3), o3,
            o4.neg().add(o3), o3.add(o4.neg()),
        );

        // Apply positive ratio bounds
        lemma_positive_ratio_bounds::<T>(o3, denom);
    } else {
        // Case 2: o3 < 0, o4 > 0
        // Show -o4 < 0
        lemma_neg_of_pos_is_neg::<T>(o4);
        // Show denom < 0: o3 < 0, -o4 < 0 → denom = o3 + (-o4) < 0
        lemma_sum_of_negatives_is_negative::<T>(o3, o4.neg());

        // Show o3.neg() > 0, denom.neg() > 0
        lemma_neg_of_neg_is_pos::<T>(o3);
        lemma_neg_of_neg_is_pos::<T>(denom);

        // Show denom < o3 (so o3.neg() < denom.neg()):
        // -o4 < 0 → (-o4)+o3 < 0+o3 → denom < o3
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(o4.neg(), T::zero(), o3);
        additive_group_lemmas::lemma_add_zero_left::<T>(o3);
        T::axiom_add_commutative(o4.neg(), o3);
        lemma_lt_congruence_both::<T>(
            o4.neg().add(o3), o3.add(o4.neg()),
            T::zero().add(o3), o3,
        );
        // denom < o3 → o3.neg() < denom.neg()
        ordered_ring_lemmas::lemma_lt_neg_flip::<T>(denom, o3);

        // Apply positive ratio bounds to o3.neg()/denom.neg()
        lemma_positive_ratio_bounds::<T>(o3.neg(), denom.neg());
        // 0 < o3.neg()/denom.neg() < 1

        // Show t ≡ o3.neg()/denom.neg()
        // div_neg_denominator(o3.neg(), denom): o3.neg()/denom.neg() ≡ (o3.neg()/denom).neg()
        field_lemmas::lemma_div_neg_denominator::<T>(o3.neg(), denom);
        // div_neg_numerator(o3, denom): o3.neg()/denom ≡ (o3/denom).neg()
        field_lemmas::lemma_div_neg_numerator::<T>(o3, denom);
        // (o3.neg()/denom).neg() ≡ ((o3/denom).neg()).neg()
        T::axiom_neg_congruence(o3.neg().div(denom), o3.div(denom).neg());
        // Chain: o3.neg()/denom.neg() ≡ (o3.neg()/denom).neg() ≡ (o3/denom).neg().neg()
        T::axiom_eqv_transitive(
            o3.neg().div(denom.neg()),
            o3.neg().div(denom).neg(),
            o3.div(denom).neg().neg(),
        );
        // neg_involution: (o3/denom).neg().neg() ≡ o3/denom = t
        additive_group_lemmas::lemma_neg_involution::<T>(o3.div(denom));
        T::axiom_eqv_transitive(
            o3.neg().div(denom.neg()),
            o3.div(denom).neg().neg(),
            o3.div(denom),
        );
        // o3.neg()/denom.neg() ≡ t

        // Transfer 0 < t from 0 < o3.neg()/denom.neg()
        lemma_lt_transfer_eqv::<T>(o3.neg().div(denom.neg()), o3.div(denom));

        // For t < 1: o3.neg()/denom.neg() < 1 and o3.neg()/denom.neg() ≡ t → t < 1
        T::axiom_lt_iff_le_and_not_eqv(o3.neg().div(denom.neg()), T::one());
        T::axiom_eqv_symmetric(o3.neg().div(denom.neg()), o3.div(denom));
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            o3.neg().div(denom.neg()), o3.div(denom), T::one(),
        );
        // t ≤ 1. For strict: ¬(t ≡ 1)
        if o3.div(denom).eqv(T::one()) {
            T::axiom_eqv_transitive(o3.neg().div(denom.neg()), o3.div(denom), T::one());
            // o3.neg()/denom.neg() ≡ 1, contradicts o3.neg()/denom.neg() < 1
        }
        T::axiom_lt_iff_le_and_not_eqv(o3.div(denom), T::one());
    }
}

// =========================================================================
// Helper: a ≤ b implies 0 ≤ b - a
// =========================================================================

pub proof fn lemma_le_implies_sub_nonneg<T: OrderedRing>(a: T, b: T)
    requires
        a.le(b),
    ensures
        T::zero().le(b.sub(a)),
{
    // a ≤ b → a+(-a) ≤ b+(-a)
    T::axiom_le_add_monotone(a, b, a.neg());
    // a+(-a) ≡ 0
    T::axiom_add_inverse_right(a);
    // b+(-a) ≡ b-a
    T::axiom_sub_is_add_neg(b, a);
    T::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
    // Transfer: 0 ≤ b-a
    T::axiom_le_congruence(a.add(a.neg()), T::zero(), b.add(a.neg()), b.sub(a));
}

// =========================================================================
// Helper: weighted average bounds
// 0 ≤ t ≤ 1 implies min(a,b) ≤ a + t*(b-a) ≤ max(a,b)
// =========================================================================

pub proof fn lemma_weighted_average_bounds<T: OrderedRing>(a: T, b: T, t: T)
    requires
        T::zero().le(t),
        t.le(T::one()),
    ensures
        scalar_min(a, b).le(a.add(t.mul(b.sub(a)))),
        a.add(t.mul(b.sub(a))).le(scalar_max(a, b)),
{
    let val = a.add(t.mul(b.sub(a)));
    T::axiom_le_total(a, b);

    if a.le(b) {
        // scalar_min = a, scalar_max = b

        // --- Lower bound: a ≤ val ---
        // 0 ≤ b-a
        lemma_le_implies_sub_nonneg::<T>(a, b);
        // 0*(b-a) ≤ t*(b-a)
        T::axiom_le_mul_nonneg_monotone(T::zero(), t, b.sub(a));
        // 0*(b-a) ≡ 0
        ring_lemmas::lemma_mul_zero_left::<T>(b.sub(a));
        // t*(b-a) ≡ t*(b-a) [refl]
        T::axiom_eqv_reflexive(t.mul(b.sub(a)));
        // Transfer: 0 ≤ t*(b-a)
        T::axiom_le_congruence(
            T::zero().mul(b.sub(a)), T::zero(),
            t.mul(b.sub(a)), t.mul(b.sub(a)),
        );
        // 0+a ≤ t*(b-a)+a
        T::axiom_le_add_monotone(T::zero(), t.mul(b.sub(a)), a);
        // 0+a ≡ a
        additive_group_lemmas::lemma_add_zero_left::<T>(a);
        // t*(b-a)+a ≡ a+t*(b-a) = val
        T::axiom_add_commutative(t.mul(b.sub(a)), a);
        // Transfer: a ≤ val
        T::axiom_le_congruence(
            T::zero().add(a), a,
            t.mul(b.sub(a)).add(a), val,
        );

        // --- Upper bound: val ≤ b ---
        // t*(b-a) ≤ 1*(b-a)
        T::axiom_le_mul_nonneg_monotone(t, T::one(), b.sub(a));
        // 1*(b-a) ≡ b-a
        ring_lemmas::lemma_mul_one_left::<T>(b.sub(a));
        // t*(b-a) ≡ t*(b-a) [refl]
        T::axiom_eqv_reflexive(t.mul(b.sub(a)));
        // Transfer: t*(b-a) ≤ b-a
        T::axiom_le_congruence(
            t.mul(b.sub(a)), t.mul(b.sub(a)),
            T::one().mul(b.sub(a)), b.sub(a),
        );
        // t*(b-a)+a ≤ (b-a)+a
        T::axiom_le_add_monotone(t.mul(b.sub(a)), b.sub(a), a);
        // t*(b-a)+a ≡ val [comm]
        T::axiom_add_commutative(t.mul(b.sub(a)), a);
        // (b-a)+a ≡ b [sub_then_add_cancel]
        additive_group_lemmas::lemma_sub_then_add_cancel::<T>(b, a);
        // Transfer: val ≤ b
        T::axiom_le_congruence(
            t.mul(b.sub(a)).add(a), val,
            b.sub(a).add(a), b,
        );
    } else {
        // b ≤ a: scalar_min = b, scalar_max = a

        // --- Upper bound: val ≤ a ---
        // b ≤ a → b+(-a) ≤ a+(-a) → b-a ≤ 0
        T::axiom_le_add_monotone(b, a, a.neg());
        T::axiom_add_inverse_right(a);
        T::axiom_sub_is_add_neg(b, a);
        T::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
        T::axiom_le_congruence(
            b.add(a.neg()), b.sub(a),
            a.add(a.neg()), T::zero(),
        );
        // b-a ≤ 0, 0 ≤ t → (b-a)*t ≤ 0*t
        T::axiom_le_mul_nonneg_monotone(b.sub(a), T::zero(), t);
        // 0*t ≡ 0
        ring_lemmas::lemma_mul_zero_left::<T>(t);
        // (b-a)*t ≡ t*(b-a)
        T::axiom_mul_commutative(b.sub(a), t);
        // Transfer: t*(b-a) ≤ 0
        T::axiom_le_congruence(
            b.sub(a).mul(t), t.mul(b.sub(a)),
            T::zero().mul(t), T::zero(),
        );
        // t*(b-a)+a ≤ 0+a
        T::axiom_le_add_monotone(t.mul(b.sub(a)), T::zero(), a);
        // 0+a ≡ a
        additive_group_lemmas::lemma_add_zero_left::<T>(a);
        // t*(b-a)+a ≡ val
        T::axiom_add_commutative(t.mul(b.sub(a)), a);
        // Transfer: val ≤ a
        T::axiom_le_congruence(
            t.mul(b.sub(a)).add(a), val,
            T::zero().add(a), a,
        );

        // --- Lower bound: b ≤ val ---
        // b ≤ a → 0 ≤ a-b
        lemma_le_implies_sub_nonneg::<T>(b, a);
        // t ≤ 1, 0 ≤ a-b → t*(a-b) ≤ 1*(a-b)
        T::axiom_le_mul_nonneg_monotone(t, T::one(), a.sub(b));
        // 1*(a-b) ≡ a-b
        ring_lemmas::lemma_mul_one_left::<T>(a.sub(b));
        T::axiom_eqv_reflexive(t.mul(a.sub(b)));
        // Transfer: t*(a-b) ≤ a-b
        T::axiom_le_congruence(
            t.mul(a.sub(b)), t.mul(a.sub(b)),
            T::one().mul(a.sub(b)), a.sub(b),
        );
        // Negate: -(a-b) ≤ -(t*(a-b))
        ordered_ring_lemmas::lemma_le_neg_flip::<T>(t.mul(a.sub(b)), a.sub(b));
        // -(a-b) ≡ b-a
        additive_group_lemmas::lemma_sub_antisymmetric::<T>(a, b);
        T::axiom_neg_congruence(a.sub(b), b.sub(a).neg());
        additive_group_lemmas::lemma_neg_involution::<T>(b.sub(a));
        T::axiom_eqv_transitive(
            a.sub(b).neg(), b.sub(a).neg().neg(), b.sub(a),
        );
        // -(t*(a-b)) ≡ t*(b-a)
        ring_lemmas::lemma_mul_neg_right::<T>(t, a.sub(b));
        T::axiom_eqv_symmetric(t.mul(a.sub(b).neg()), t.mul(a.sub(b)).neg());
        ring_lemmas::lemma_mul_congruence_right::<T>(t, a.sub(b).neg(), b.sub(a));
        T::axiom_eqv_transitive(
            t.mul(a.sub(b)).neg(), t.mul(a.sub(b).neg()), t.mul(b.sub(a)),
        );
        // Transfer: b-a ≤ t*(b-a)
        T::axiom_le_congruence(
            a.sub(b).neg(), b.sub(a),
            t.mul(a.sub(b)).neg(), t.mul(b.sub(a)),
        );
        // (b-a)+a ≤ t*(b-a)+a
        T::axiom_le_add_monotone(b.sub(a), t.mul(b.sub(a)), a);
        // (b-a)+a ≡ b
        additive_group_lemmas::lemma_sub_then_add_cancel::<T>(b, a);
        // t*(b-a)+a ≡ val
        T::axiom_add_commutative(t.mul(b.sub(a)), a);
        // Transfer: b ≤ val
        T::axiom_le_congruence(
            b.sub(a).add(a), b,
            t.mul(b.sub(a)).add(a), val,
        );
    }
}

// =========================================================================
// Batch 1c: Endpoints are on their own segment
// =========================================================================

/// Endpoint a lies on the closed segment [a, b].
pub proof fn lemma_endpoint_a_on_segment<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>,
)
    ensures
        point_on_segment_inclusive_2d(a, a, b),
{
    // Collinearity: orient2d(a, b, a) ≡ orient2d(b, a, a) ≡ 0
    lemma_orient2d_cyclic::<T>(a, b, a);
    lemma_orient2d_degenerate_bc::<T>(b, a);
    T::axiom_eqv_transitive(orient2d(a, b, a), orient2d(b, a, a), T::zero());

    // Bounding box: scalar_min/max with a itself
    T::axiom_le_total(a.x, b.x);
    T::axiom_le_reflexive(a.x);
    T::axiom_le_total(a.y, b.y);
    T::axiom_le_reflexive(a.y);
}

/// Endpoint b lies on the closed segment [a, b].
pub proof fn lemma_endpoint_b_on_segment<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>,
)
    ensures
        point_on_segment_inclusive_2d(b, a, b),
{
    // Collinearity: orient2d(a, b, b) ≡ 0
    lemma_orient2d_degenerate_bc::<T>(a, b);

    // Bounding box
    T::axiom_le_total(a.x, b.x);
    T::axiom_le_reflexive(b.x);
    T::axiom_le_total(a.y, b.y);
    T::axiom_le_reflexive(b.y);
}

// =========================================================================
// Batch 1b: Affine combination lies on segment
// =========================================================================

/// Any point of the form a + t*(b-a) lies on line(a,b).
/// orient2d(a, b, a + t*(b-a)) ≡ 0.
pub proof fn lemma_affine_point_on_line<T: Ring>(a: Point2<T>, b: Point2<T>, t: T)
    ensures ({
        let p = add_vec2(a, scale2(t, sub2(b, a)));
        orient2d(a, b, p).eqv(T::zero())
    }),
{
    let dir = sub2(b, a);
    let w = scale2(t, dir);
    let p = add_vec2(a, w);

    // sub2(p, a) ≡ w
    lemma_sub2_add_vec2_cancel::<T>(a, w);
    // det2d(dir, sub2(p,a)) ≡ det2d(dir, w)
    Vec2::<T>::axiom_eqv_reflexive(dir);
    lemma_det2d_congruence::<T>(dir, dir, sub2(p, a), w);
    // det2d(dir, w) = det2d(dir, scale(t, dir)) ≡ t * det2d(dir, dir)
    lemma_det2d_scale_right::<T>(t, dir, dir);
    // det2d(dir, dir) ≡ 0
    lemma_det2d_self_zero::<T>(dir);
    // t * det2d(dir, dir) ≡ t * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(t, det2d(dir, dir), T::zero());
    T::axiom_mul_zero_right(t);
    T::axiom_eqv_transitive(
        t.mul(det2d(dir, dir)), t.mul(T::zero()), T::zero(),
    );
    // Chain: orient2d(a,b,p) ≡ det2d(dir, sub2(p,a)) ≡ det2d(dir, w)
    //        ≡ t*det2d(dir,dir) ≡ 0
    T::axiom_eqv_transitive(
        det2d(dir, sub2(p, a)), det2d(dir, w), t.mul(det2d(dir, dir)),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, p), t.mul(det2d(dir, dir)), T::zero(),
    );
}

/// If 0 ≤ t ≤ 1, then a + t*(b-a) lies on the closed segment [a, b].
pub proof fn lemma_affine_combination_on_segment<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, t: T,
)
    requires
        T::zero().le(t),
        t.le(T::one()),
    ensures
        point_on_segment_inclusive_2d(add_vec2(a, scale2(t, sub2(b, a))), a, b),
{
    let p = add_vec2(a, scale2(t, sub2(b, a)));

    // Collinearity
    lemma_affine_point_on_line::<T>(a, b, t);

    // Bounding box: p.x = a.x + t*(b.x - a.x), p.y = a.y + t*(b.y - a.y)
    lemma_weighted_average_bounds::<T>(a.x, b.x, t);
    lemma_weighted_average_bounds::<T>(a.y, b.y, t);
}

// =========================================================================
// Batch 1d: Proper intersection point lies on segment [a, b]
// =========================================================================

/// For a Proper 2D intersection, the intersection point lies on segment [a, b].
pub proof fn lemma_proper_intersection_on_segment_ab<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        point_on_segment_inclusive_2d(segment_intersection_point_2d(a, b, c, d), a, b),
{
    let t = segment_intersection_parameter_2d(a, b, c, d);
    // 0 < t < 1
    lemma_proper_parameter_bounds_2d::<T>(a, b, c, d);
    // 0 < t → 0 ≤ t
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), t);
    // t < 1 → t ≤ 1
    T::axiom_lt_iff_le_and_not_eqv(t, T::one());
    // Apply affine combination lemma
    lemma_affine_combination_on_segment::<T>(a, b, t);
}

// =========================================================================
// CD-side parameter spec
// =========================================================================

/// Intersection parameter s on segment [c,d] for segments [a,b] and [c,d] (2D).
///
/// s = orient2d(a,b,c) / (orient2d(a,b,c) - orient2d(a,b,d))
///
/// Symmetric to `segment_intersection_parameter_2d` with the roles of AB and CD swapped.
pub open spec fn segment_intersection_parameter_cd_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> T {
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);
    o1.div(o1.add(o2.neg()))
}

/// The CD-parameterized intersection point: c + s * (d - c).
pub open spec fn segment_intersection_point_cd_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> Point2<T> {
    let s = segment_intersection_parameter_cd_2d(a, b, c, d);
    let dir = sub2(d, c);
    add_vec2(c, scale2(s, dir))
}

// =========================================================================
// CD denominator nonzero for Proper intersection
// =========================================================================

/// The denominator orient2d(a,b,c) - orient2d(a,b,d) is nonzero
/// when the segment intersection is Proper.
///
/// Symmetric to `lemma_proper_denominator_nonzero_2d`.
pub proof fn lemma_proper_cd_denominator_nonzero_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let o1 = orient2d(a, b, c);
        let o2 = orient2d(a, b, d);
        !o1.add(o2.neg()).eqv(T::zero())
    }),
{
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);
    let denom = o1.add(o2.neg());

    // From Proper: o1 and o2 are both nonzero with opposite signs.
    lemma_proper_implies_cd_opposite_sides::<T>(a, b, c, d);

    // Contradiction proof: if denom ≡ 0 then o1 ≡ o2, but they have opposite signs.
    if denom.eqv(T::zero()) {
        // o1 + (-o2) ≡ 0 implies (-o2) ≡ -(o1)
        additive_group_lemmas::lemma_neg_unique::<T>(o1, o2.neg());
        // neg both sides: o2 ≡ o1
        T::axiom_neg_congruence(o2.neg(), o1.neg());
        additive_group_lemmas::lemma_neg_involution::<T>(o2);
        additive_group_lemmas::lemma_neg_involution::<T>(o1);
        T::axiom_eqv_symmetric(o2.neg().neg(), o2);
        T::axiom_eqv_transitive(o2, o2.neg().neg(), o1.neg().neg());
        T::axiom_eqv_transitive(o2, o1.neg().neg(), o1);

        if orient2d_positive(a, b, c) && orient2d_negative(a, b, d) {
            // o1 > 0 and o2 < 0, but o2 ≡ o1 → 0 < o2
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o1);
            T::axiom_eqv_symmetric(o2, o1);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o1, o2);
            // 0 ≤ o2, but o2 < 0 → contradiction
            T::axiom_lt_iff_le_and_not_eqv(o2, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o2);
            T::axiom_eqv_symmetric(T::zero(), o2);
        } else {
            // o1 < 0 and o2 > 0, but o2 ≡ o1 → o2 < 0
            T::axiom_eqv_symmetric(o2, o1);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o2);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o2, o1);
            T::axiom_lt_iff_le_and_not_eqv(o1, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o1);
            T::axiom_eqv_symmetric(T::zero(), o1);
        }
    }
}

// =========================================================================
// CD parameter bounds: 0 < s < 1 for Proper 2D intersection
// =========================================================================

/// For Proper 2D intersection, 0 < s and s < 1 where s is the CD parameter.
///
/// Symmetric to `lemma_proper_parameter_bounds_2d`.
pub proof fn lemma_proper_cd_parameter_bounds_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let s = segment_intersection_parameter_cd_2d(a, b, c, d);
        T::zero().lt(s) && s.lt(T::one())
    }),
{
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);
    let denom = o1.add(o2.neg());
    let s = o1.div(denom);

    lemma_proper_cd_denominator_nonzero_2d::<T>(a, b, c, d);
    lemma_proper_implies_cd_opposite_sides::<T>(a, b, c, d);

    if orient2d_positive(a, b, c) && orient2d_negative(a, b, d) {
        // Case 1: o1 > 0, o2 < 0
        // Show 0 < -o2
        lemma_neg_of_neg_is_pos::<T>(o2);

        // Show o1 < denom: 0 < -o2 → o1 + 0 < o1 + (-o2) = denom
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(T::zero(), o2.neg(), o1);
        additive_group_lemmas::lemma_add_zero_left::<T>(o1);
        T::axiom_add_commutative(o2.neg(), o1);
        lemma_lt_congruence_both::<T>(
            T::zero().add(o1), o1,
            o2.neg().add(o1), o1.add(o2.neg()),
        );

        // Apply positive ratio bounds
        lemma_positive_ratio_bounds::<T>(o1, denom);
    } else {
        // Case 2: o1 < 0, o2 > 0
        lemma_neg_of_pos_is_neg::<T>(o2);
        lemma_sum_of_negatives_is_negative::<T>(o1, o2.neg());

        lemma_neg_of_neg_is_pos::<T>(o1);
        lemma_neg_of_neg_is_pos::<T>(denom);

        // Show denom < o1 (so o1.neg() < denom.neg()):
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(o2.neg(), T::zero(), o1);
        additive_group_lemmas::lemma_add_zero_left::<T>(o1);
        T::axiom_add_commutative(o2.neg(), o1);
        lemma_lt_congruence_both::<T>(
            o2.neg().add(o1), o1.add(o2.neg()),
            T::zero().add(o1), o1,
        );
        // denom < o1 → o1.neg() < denom.neg()
        ordered_ring_lemmas::lemma_lt_neg_flip::<T>(denom, o1);

        // Apply positive ratio bounds to o1.neg()/denom.neg()
        lemma_positive_ratio_bounds::<T>(o1.neg(), denom.neg());

        // Show s ≡ o1.neg()/denom.neg()
        field_lemmas::lemma_div_neg_denominator::<T>(o1.neg(), denom);
        field_lemmas::lemma_div_neg_numerator::<T>(o1, denom);
        T::axiom_neg_congruence(o1.neg().div(denom), o1.div(denom).neg());
        T::axiom_eqv_transitive(
            o1.neg().div(denom.neg()),
            o1.neg().div(denom).neg(),
            o1.div(denom).neg().neg(),
        );
        additive_group_lemmas::lemma_neg_involution::<T>(o1.div(denom));
        T::axiom_eqv_transitive(
            o1.neg().div(denom.neg()),
            o1.div(denom).neg().neg(),
            o1.div(denom),
        );

        // Transfer 0 < s from 0 < o1.neg()/denom.neg()
        lemma_lt_transfer_eqv::<T>(o1.neg().div(denom.neg()), o1.div(denom));

        // For s < 1: o1.neg()/denom.neg() < 1 and ≡ s → s < 1
        T::axiom_lt_iff_le_and_not_eqv(o1.neg().div(denom.neg()), T::one());
        T::axiom_eqv_symmetric(o1.neg().div(denom.neg()), o1.div(denom));
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            o1.neg().div(denom.neg()), o1.div(denom), T::one(),
        );
        if o1.div(denom).eqv(T::one()) {
            T::axiom_eqv_transitive(o1.neg().div(denom.neg()), o1.div(denom), T::one());
        }
        T::axiom_lt_iff_le_and_not_eqv(o1.div(denom), T::one());
    }
}

// =========================================================================
// On-line proof: CD-parameterized point lies on line(a, b)
// =========================================================================

/// The CD-parameterized intersection point c + s*(d-c) lies on line(a, b):
/// orient2d(a, b, c + s*(d-c)) ≡ 0.
///
/// Proof outline (symmetric to lemma_intersection_point_on_line_cd_2d):
///   q = c + s*(d-c), so q-a = (c-a) + s*(d-c).
///   orient2d(a,b,q) = det2d(b-a, q-a)
///     = det2d(b-a, c-a) + det2d(b-a, s*(d-c))       [add_right]
///     = o1 + s * det2d(b-a, d-c)                     [scale_right]
///     = o1 + s * (o2 - o1)                           [sub_right]
///     = o1 + [o1/den] * (-den)                       [den = o1-o2, o2-o1 = -den]
///     = o1 + (-o1) = 0
pub proof fn lemma_cd_point_on_line_ab_2d<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures ({
        let q = segment_intersection_point_cd_2d(a, b, c, d);
        orient2d(a, b, q).eqv(T::zero())
    }),
{
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);
    let den = o1.sub(o2); // o1 - o2

    // den is nonzero
    lemma_proper_cd_denominator_nonzero_2d::<T>(a, b, c, d);
    T::axiom_sub_is_add_neg(o1, o2);
    T::axiom_eqv_symmetric(o1.sub(o2), o1.add(o2.neg()));

    let s = segment_intersection_parameter_cd_2d(a, b, c, d);
    let dir_cd = sub2(d, c);
    let w = scale2(s, dir_cd);
    let q = add_vec2(c, w);
    let ba = sub2(b, a);
    let ca = sub2(c, a);

    // ---------------------------------------------------------------
    // Step 1: sub2(q, a) ≡ Vec2 { x: ca.x + w.x, y: ca.y + w.y }
    // ---------------------------------------------------------------
    lemma_sub2_add_vec2_decompose::<T>(c, w, a);
    let qa_decomposed = Vec2 { x: ca.x.add(w.x), y: ca.y.add(w.y) };

    // ---------------------------------------------------------------
    // Step 2: det2d(ba, sub2(q,a)) ≡ det2d(ba, qa_decomposed)
    // ---------------------------------------------------------------
    Vec2::<T>::axiom_eqv_reflexive(ba);
    lemma_det2d_congruence::<T>(ba, ba, sub2(q, a), qa_decomposed);

    // ---------------------------------------------------------------
    // Step 3: det2d(ba, qa_decomposed) ≡ det2d(ba, ca) + det2d(ba, w)
    // ---------------------------------------------------------------
    lemma_det2d_add_right::<T>(ba, ca, w);

    T::axiom_eqv_transitive(
        orient2d(a, b, q),
        det2d(ba, qa_decomposed),
        det2d(ba, ca).add(det2d(ba, w)),
    );
    // det2d(ba, ca) = orient2d(a, b, c) = o1

    // ---------------------------------------------------------------
    // Step 4: det2d(ba, w) = det2d(ba, scale(s, dir_cd))
    //         ≡ s * det2d(ba, dir_cd)
    // ---------------------------------------------------------------
    lemma_det2d_scale_right::<T>(s, ba, dir_cd);

    // o1 + det2d(ba, w) ≡ o1 + s * det2d(ba, dir_cd)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o1, det2d(ba, w), s.mul(det2d(ba, dir_cd)),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, q),
        o1.add(det2d(ba, w)),
        o1.add(s.mul(det2d(ba, dir_cd))),
    );

    // ---------------------------------------------------------------
    // Step 5: det2d(ba, dir_cd) = det2d(ba, d-c)
    //         dir_cd = d-c = (d-a)-(c-a) componentwise
    //         det2d(ba, (d-a)-(c-a)) ≡ det2d(ba, d-a) - det2d(ba, c-a) = o2 - o1
    // ---------------------------------------------------------------
    let da = sub2(d, a);
    let da_minus_ca = Vec2 { x: da.x.sub(ca.x), y: da.y.sub(ca.y) };

    // Show dir_cd ≡ da_minus_ca componentwise:
    // x: d.x-c.x ≡ (d.x-a.x)-(c.x-a.x)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.x, a.x);
    T::axiom_neg_congruence(c.x.sub(a.x), a.x.sub(c.x).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(a.x.sub(c.x));
    T::axiom_eqv_transitive(
        ca.x.neg(), a.x.sub(c.x).neg().neg(), a.x.sub(c.x),
    );
    T::axiom_sub_is_add_neg(da.x, ca.x);
    additive_group_lemmas::lemma_add_congruence_right::<T>(da.x, ca.x.neg(), a.x.sub(c.x));
    T::axiom_eqv_transitive(
        da.x.sub(ca.x), da.x.add(ca.x.neg()), da.x.add(a.x.sub(c.x)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(d.x, a.x, c.x);
    T::axiom_eqv_transitive(
        da.x.sub(ca.x), da.x.add(a.x.sub(c.x)), d.x.sub(c.x),
    );

    // y: same
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.y, a.y);
    T::axiom_neg_congruence(c.y.sub(a.y), a.y.sub(c.y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(a.y.sub(c.y));
    T::axiom_eqv_transitive(
        ca.y.neg(), a.y.sub(c.y).neg().neg(), a.y.sub(c.y),
    );
    T::axiom_sub_is_add_neg(da.y, ca.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(da.y, ca.y.neg(), a.y.sub(c.y));
    T::axiom_eqv_transitive(
        da.y.sub(ca.y), da.y.add(ca.y.neg()), da.y.add(a.y.sub(c.y)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(d.y, a.y, c.y);
    T::axiom_eqv_transitive(
        da.y.sub(ca.y), da.y.add(a.y.sub(c.y)), d.y.sub(c.y),
    );

    // dir_cd ≡ da_minus_ca (swap direction)
    T::axiom_eqv_symmetric(da.x.sub(ca.x), dir_cd.x);
    T::axiom_eqv_symmetric(da.y.sub(ca.y), dir_cd.y);

    // det2d(ba, dir_cd) ≡ det2d(ba, da_minus_ca) via congruence
    lemma_det2d_congruence::<T>(ba, ba, dir_cd, da_minus_ca);

    // det2d(ba, da_minus_ca) ≡ det2d(ba, da) - det2d(ba, ca) = o2 - o1
    lemma_det2d_sub_right::<T>(ba, da, ca);

    T::axiom_eqv_transitive(
        det2d(ba, dir_cd),
        det2d(ba, da_minus_ca),
        det2d(ba, da).sub(det2d(ba, ca)),
    );
    // det2d(ba, da) = orient2d(a,b,d) = o2, det2d(ba, ca) = orient2d(a,b,c) = o1

    // ---------------------------------------------------------------
    // Step 6: s * det2d(ba, dir_cd) ≡ s * (o2 - o1)
    // ---------------------------------------------------------------
    ring_lemmas::lemma_mul_congruence_right::<T>(s, det2d(ba, dir_cd), o2.sub(o1));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o1, s.mul(det2d(ba, dir_cd)), s.mul(o2.sub(o1)),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, q),
        o1.add(s.mul(det2d(ba, dir_cd))),
        o1.add(s.mul(o2.sub(o1))),
    );

    // ---------------------------------------------------------------
    // Step 7: s * (o2 - o1) where s = o1 / (o1 - o2)
    //   o2 - o1 = -(o1 - o2) = -den
    //   s * (-den) = [o1/den] * (-den) = -o1
    // ---------------------------------------------------------------
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(o2, o1);

    ring_lemmas::lemma_mul_congruence_right::<T>(s, o2.sub(o1), o1.sub(o2).neg());

    // s ≡ o1.mul(den.recip()) via div_is_mul_recip
    T::axiom_div_is_mul_recip(o1, o1.add(o2.neg()));

    // o1.add(o2.neg()).recip() ≡ den.recip()
    T::axiom_recip_congruence(o1.add(o2.neg()), den);

    // s ≡ o1.mul(den.recip())
    ring_lemmas::lemma_mul_congruence_right::<T>(
        o1, o1.add(o2.neg()).recip(), den.recip(),
    );
    T::axiom_eqv_transitive(
        s, o1.mul(o1.add(o2.neg()).recip()), o1.mul(den.recip()),
    );

    // s * (-den) ≡ o1.mul(den.recip()) * (-den)
    T::axiom_mul_congruence_left(s, o1.mul(den.recip()), den.neg());
    T::axiom_eqv_transitive(
        s.mul(o2.sub(o1)),
        s.mul(den.neg()),
        o1.mul(den.recip()).mul(den.neg()),
    );

    // o1 * recip(den) * (-den) = o1 * (recip(den) * (-den))
    T::axiom_mul_associative(o1, den.recip(), den.neg());

    // recip(den) * (-den) ≡ -(recip(den) * den)
    ring_lemmas::lemma_mul_neg_right::<T>(den.recip(), den);

    // recip(den) * den ≡ 1
    if den.eqv(T::zero()) {
        T::axiom_eqv_symmetric(o1.sub(o2), o1.add(o2.neg()));
        T::axiom_eqv_transitive(o1.add(o2.neg()), den, T::zero());
    }
    T::axiom_mul_recip_right(den);
    T::axiom_mul_commutative(den.recip(), den);
    T::axiom_eqv_transitive(den.recip().mul(den), den.mul(den.recip()), T::one());

    // -(recip(den)*den) ≡ -(1)
    T::axiom_neg_congruence(den.recip().mul(den), T::one());

    // recip(den) * (-den) ≡ -(1)
    T::axiom_eqv_transitive(
        den.recip().mul(den.neg()),
        den.recip().mul(den).neg(),
        T::one().neg(),
    );

    // o1 * (recip(den) * (-den)) ≡ o1 * (-1)
    ring_lemmas::lemma_mul_congruence_right::<T>(o1, den.recip().mul(den.neg()), T::one().neg());

    // chain: o1*recip(den)*(-den) ≡ o1*(recip(den)*(-den)) ≡ o1*(-1)
    T::axiom_eqv_transitive(
        o1.mul(den.recip()).mul(den.neg()),
        o1.mul(den.recip().mul(den.neg())),
        o1.mul(T::one().neg()),
    );

    // o1 * (-1) ≡ -(o1 * 1) ≡ -o1
    ring_lemmas::lemma_mul_neg_right::<T>(o1, T::one());
    T::axiom_mul_one_right(o1);
    T::axiom_neg_congruence(o1.mul(T::one()), o1);
    T::axiom_eqv_transitive(
        o1.mul(T::one().neg()),
        o1.mul(T::one()).neg(),
        o1.neg(),
    );

    // Chain: s*(o2-o1) ≡ o1*recip(den)*(-den) ≡ o1*(-1) ≡ -o1
    T::axiom_eqv_transitive(
        s.mul(o2.sub(o1)),
        o1.mul(den.recip()).mul(den.neg()),
        o1.mul(T::one().neg()),
    );
    T::axiom_eqv_transitive(
        s.mul(o2.sub(o1)),
        o1.mul(T::one().neg()),
        o1.neg(),
    );

    // ---------------------------------------------------------------
    // Step 8: o1 + s*(o2-o1) ≡ o1 + (-o1) ≡ 0
    // ---------------------------------------------------------------
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o1, s.mul(o2.sub(o1)), o1.neg(),
    );
    T::axiom_add_inverse_right(o1);

    T::axiom_eqv_transitive(
        o1.add(s.mul(o2.sub(o1))),
        o1.add(o1.neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, q),
        o1.add(s.mul(o2.sub(o1))),
        o1.add(o1.neg()),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, q),
        o1.add(o1.neg()),
        T::zero(),
    );
}

// =========================================================================
// Helper: a - b ≡ 0 implies a ≡ b
// =========================================================================

pub proof fn lemma_sub_zero_implies_eqv<T: Ring>(a: T, b: T)
    requires
        a.sub(b).eqv(T::zero()),
    ensures
        a.eqv(b),
{
    // (a-b)+b ≡ a  [sub_then_add_cancel]
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(a, b);
    // (a-b) ≡ 0, so (a-b)+b ≡ 0+b  [add_congruence_left]
    T::axiom_add_congruence_left(a.sub(b), T::zero(), b);
    // 0+b ≡ b
    T::axiom_add_commutative(T::zero(), b);
    T::axiom_add_zero_right(b);
    T::axiom_eqv_transitive(T::zero().add(b), b.add(T::zero()), b);
    // Chain: a ≡ (a-b)+b ≡ 0+b ≡ b
    T::axiom_eqv_symmetric(a.sub(b).add(b), a);
    T::axiom_eqv_transitive(a, a.sub(b).add(b), T::zero().add(b));
    T::axiom_eqv_transitive(a, T::zero().add(b), b);
}

// =========================================================================
// Core uniqueness: det2d(u,w) ≡ 0 and det2d(v,w) ≡ 0 and det2d(u,v) ≢ 0
// implies w ≡ zero.
// =========================================================================

/// If a vector w has zero determinant with two non-parallel directions u and v,
/// then w is the zero vector. This is the 2D uniqueness of line intersection.
///
/// Proof: Cross-multiply the determinant conditions and use field cancellation
/// (contradiction) to show each component of w must be zero.
pub proof fn lemma_det2d_zero_both_implies_zero<T: OrderedField>(
    u: Vec2<T>, v: Vec2<T>, w: Vec2<T>,
)
    requires
        det2d(u, w).eqv(T::zero()),
        det2d(v, w).eqv(T::zero()),
        !det2d(u, v).eqv(T::zero()),
    ensures
        w.x.eqv(T::zero()),
        w.y.eqv(T::zero()),
{
    // Extract: u.x*w.y ≡ u.y*w.x from det2d(u, w) = u.x*w.y - u.y*w.x ≡ 0
    lemma_sub_zero_implies_eqv::<T>(u.x.mul(w.y), u.y.mul(w.x));
    // Extract: v.x*w.y ≡ v.y*w.x from det2d(v, w) ≡ 0
    lemma_sub_zero_implies_eqv::<T>(v.x.mul(w.y), v.y.mul(w.x));

    // === Prove w.x ≡ 0 by contradiction ===

    // Multiply eq1 by v.x: v.x*(u.x*w.y) ≡ v.x*(u.y*w.x)
    ring_lemmas::lemma_mul_congruence_right::<T>(v.x, u.x.mul(w.y), u.y.mul(w.x));
    // Reverse assoc: (v.x*u.x)*w.y ≡ v.x*(u.x*w.y)
    T::axiom_mul_associative(v.x, u.x, w.y);
    T::axiom_eqv_transitive(
        v.x.mul(u.x).mul(w.y), v.x.mul(u.x.mul(w.y)), v.x.mul(u.y.mul(w.x)),
    );
    // Reverse assoc: v.x*(u.y*w.x) ≡ (v.x*u.y)*w.x
    T::axiom_mul_associative(v.x, u.y, w.x);
    T::axiom_eqv_symmetric(v.x.mul(u.y).mul(w.x), v.x.mul(u.y.mul(w.x)));
    // Chain: (v.x*u.x)*w.y ≡ (v.x*u.y)*w.x
    T::axiom_eqv_transitive(
        v.x.mul(u.x).mul(w.y), v.x.mul(u.y.mul(w.x)), v.x.mul(u.y).mul(w.x),
    );

    // Multiply eq2 by u.x: u.x*(v.x*w.y) ≡ u.x*(v.y*w.x)
    ring_lemmas::lemma_mul_congruence_right::<T>(u.x, v.x.mul(w.y), v.y.mul(w.x));
    T::axiom_mul_associative(u.x, v.x, w.y);
    T::axiom_eqv_transitive(
        u.x.mul(v.x).mul(w.y), u.x.mul(v.x.mul(w.y)), u.x.mul(v.y.mul(w.x)),
    );
    T::axiom_mul_associative(u.x, v.y, w.x);
    T::axiom_eqv_symmetric(u.x.mul(v.y).mul(w.x), u.x.mul(v.y.mul(w.x)));
    // Chain: (u.x*v.x)*w.y ≡ (u.x*v.y)*w.x
    T::axiom_eqv_transitive(
        u.x.mul(v.x).mul(w.y), u.x.mul(v.y.mul(w.x)), u.x.mul(v.y).mul(w.x),
    );

    // Commutativity: (v.x*u.x)*w.y ≡ (u.x*v.x)*w.y
    T::axiom_mul_commutative(v.x, u.x);
    T::axiom_mul_congruence_left(v.x.mul(u.x), u.x.mul(v.x), w.y);

    // Full chain: (v.x*u.y)*w.x ≡ (v.x*u.x)*w.y ≡ (u.x*v.x)*w.y ≡ (u.x*v.y)*w.x
    T::axiom_eqv_symmetric(v.x.mul(u.x).mul(w.y), v.x.mul(u.y).mul(w.x));
    T::axiom_eqv_transitive(
        v.x.mul(u.y).mul(w.x), v.x.mul(u.x).mul(w.y), u.x.mul(v.x).mul(w.y),
    );
    T::axiom_eqv_transitive(
        v.x.mul(u.y).mul(w.x), u.x.mul(v.x).mul(w.y), u.x.mul(v.y).mul(w.x),
    );

    // Contradiction: if w.x ≢ 0, cancel to get det2d(u,v) ≡ 0
    if !w.x.eqv(T::zero()) {
        field_lemmas::lemma_mul_cancel_right::<T>(v.x.mul(u.y), u.x.mul(v.y), w.x);
        // v.x*u.y ≡ u.x*v.y → u.y*v.x ≡ u.x*v.y
        T::axiom_mul_commutative(v.x, u.y);
        T::axiom_eqv_symmetric(v.x.mul(u.y), u.y.mul(v.x));
        T::axiom_eqv_transitive(u.y.mul(v.x), v.x.mul(u.y), u.x.mul(v.y));
        // det2d(u,v) = u.x*v.y - u.y*v.x ≡ u.x*v.y - u.x*v.y ≡ 0
        T::axiom_eqv_reflexive(u.x.mul(v.y));
        additive_group_lemmas::lemma_sub_congruence::<T>(
            u.x.mul(v.y), u.x.mul(v.y), u.y.mul(v.x), u.x.mul(v.y),
        );
        additive_group_lemmas::lemma_sub_self::<T>(u.x.mul(v.y));
        T::axiom_eqv_transitive(det2d(u, v), u.x.mul(v.y).sub(u.x.mul(v.y)), T::zero());
        // Contradiction with !det2d(u,v).eqv(T::zero())
    }

    // === Prove w.y ≡ 0 by contradiction (same structure with v.y, u.y multipliers) ===

    // Multiply eq1 by v.y: (v.y*u.x)*w.y ≡ (v.y*u.y)*w.x
    ring_lemmas::lemma_mul_congruence_right::<T>(v.y, u.x.mul(w.y), u.y.mul(w.x));
    T::axiom_mul_associative(v.y, u.x, w.y);
    T::axiom_eqv_transitive(
        v.y.mul(u.x).mul(w.y), v.y.mul(u.x.mul(w.y)), v.y.mul(u.y.mul(w.x)),
    );
    T::axiom_mul_associative(v.y, u.y, w.x);
    T::axiom_eqv_symmetric(v.y.mul(u.y).mul(w.x), v.y.mul(u.y.mul(w.x)));
    T::axiom_eqv_transitive(
        v.y.mul(u.x).mul(w.y), v.y.mul(u.y.mul(w.x)), v.y.mul(u.y).mul(w.x),
    );

    // Multiply eq2 by u.y: (u.y*v.x)*w.y ≡ (u.y*v.y)*w.x
    ring_lemmas::lemma_mul_congruence_right::<T>(u.y, v.x.mul(w.y), v.y.mul(w.x));
    T::axiom_mul_associative(u.y, v.x, w.y);
    T::axiom_eqv_transitive(
        u.y.mul(v.x).mul(w.y), u.y.mul(v.x.mul(w.y)), u.y.mul(v.y.mul(w.x)),
    );
    T::axiom_mul_associative(u.y, v.y, w.x);
    T::axiom_eqv_symmetric(u.y.mul(v.y).mul(w.x), u.y.mul(v.y.mul(w.x)));
    T::axiom_eqv_transitive(
        u.y.mul(v.x).mul(w.y), u.y.mul(v.y.mul(w.x)), u.y.mul(v.y).mul(w.x),
    );

    // Commutativity: (v.y*u.y)*w.x ≡ (u.y*v.y)*w.x
    T::axiom_mul_commutative(v.y, u.y);
    T::axiom_mul_congruence_left(v.y.mul(u.y), u.y.mul(v.y), w.x);

    // Full chain: (v.y*u.x)*w.y ≡ (v.y*u.y)*w.x ≡ (u.y*v.y)*w.x ≡ (u.y*v.x)*w.y
    T::axiom_eqv_symmetric(u.y.mul(v.x).mul(w.y), u.y.mul(v.y).mul(w.x));
    T::axiom_eqv_transitive(
        v.y.mul(u.x).mul(w.y), v.y.mul(u.y).mul(w.x), u.y.mul(v.y).mul(w.x),
    );
    T::axiom_eqv_transitive(
        v.y.mul(u.x).mul(w.y), u.y.mul(v.y).mul(w.x), u.y.mul(v.x).mul(w.y),
    );

    // Contradiction: if w.y ≢ 0, cancel to get det2d(u,v) ≡ 0
    if !w.y.eqv(T::zero()) {
        field_lemmas::lemma_mul_cancel_right::<T>(v.y.mul(u.x), u.y.mul(v.x), w.y);
        // v.y*u.x ≡ u.y*v.x → u.x*v.y ≡ u.y*v.x
        T::axiom_mul_commutative(v.y, u.x);
        T::axiom_eqv_symmetric(v.y.mul(u.x), u.x.mul(v.y));
        T::axiom_eqv_transitive(u.x.mul(v.y), v.y.mul(u.x), u.y.mul(v.x));
        // det2d(u,v) = u.x*v.y - u.y*v.x ≡ u.y*v.x - u.y*v.x ≡ 0
        T::axiom_eqv_reflexive(u.y.mul(v.x));
        additive_group_lemmas::lemma_sub_congruence::<T>(
            u.x.mul(v.y), u.y.mul(v.x), u.y.mul(v.x), u.y.mul(v.x),
        );
        additive_group_lemmas::lemma_sub_self::<T>(u.y.mul(v.x));
        T::axiom_eqv_transitive(det2d(u, v), u.y.mul(v.x).sub(u.y.mul(v.x)), T::zero());
    }
}

// =========================================================================
// Non-parallel lines for Proper intersection
// =========================================================================

/// For Proper intersection, det2d(b-a, d-c) ≢ 0 (lines are not parallel).
///
/// Proof: det2d(b-a, d-c) ≡ orient2d(a,b,d) - orient2d(a,b,c).
/// If this were 0, then o1 ≡ o2, contradicting opposite signs.
pub proof fn lemma_lines_not_parallel_for_proper<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        !det2d(sub2(b, a), sub2(d, c)).eqv(T::zero()),
{
    let ba = sub2(b, a);
    let dc = sub2(d, c);
    let da = sub2(d, a);
    let ca = sub2(c, a);
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);

    // Show det2d(ba, dc) ≡ o2 - o1.
    // dc = (d-a)-(c-a) componentwise. Show dc ≡ da_minus_ca.
    let da_minus_ca = Vec2 { x: da.x.sub(ca.x), y: da.y.sub(ca.y) };

    // x: (d.x-a.x)-(c.x-a.x) ≡ d.x-c.x
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.x, a.x);
    T::axiom_neg_congruence(c.x.sub(a.x), a.x.sub(c.x).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(a.x.sub(c.x));
    T::axiom_eqv_transitive(
        ca.x.neg(), a.x.sub(c.x).neg().neg(), a.x.sub(c.x),
    );
    T::axiom_sub_is_add_neg(da.x, ca.x);
    additive_group_lemmas::lemma_add_congruence_right::<T>(da.x, ca.x.neg(), a.x.sub(c.x));
    T::axiom_eqv_transitive(
        da.x.sub(ca.x), da.x.add(ca.x.neg()), da.x.add(a.x.sub(c.x)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(d.x, a.x, c.x);
    T::axiom_eqv_transitive(
        da.x.sub(ca.x), da.x.add(a.x.sub(c.x)), d.x.sub(c.x),
    );

    // y: same
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.y, a.y);
    T::axiom_neg_congruence(c.y.sub(a.y), a.y.sub(c.y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(a.y.sub(c.y));
    T::axiom_eqv_transitive(
        ca.y.neg(), a.y.sub(c.y).neg().neg(), a.y.sub(c.y),
    );
    T::axiom_sub_is_add_neg(da.y, ca.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(da.y, ca.y.neg(), a.y.sub(c.y));
    T::axiom_eqv_transitive(
        da.y.sub(ca.y), da.y.add(ca.y.neg()), da.y.add(a.y.sub(c.y)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(d.y, a.y, c.y);
    T::axiom_eqv_transitive(
        da.y.sub(ca.y), da.y.add(a.y.sub(c.y)), d.y.sub(c.y),
    );

    // dc ≡ da_minus_ca
    T::axiom_eqv_symmetric(da.x.sub(ca.x), dc.x);
    T::axiom_eqv_symmetric(da.y.sub(ca.y), dc.y);

    // det2d(ba, dc) ≡ det2d(ba, da_minus_ca)
    Vec2::<T>::axiom_eqv_reflexive(ba);
    lemma_det2d_congruence::<T>(ba, ba, dc, da_minus_ca);

    // det2d(ba, da_minus_ca) ≡ det2d(ba, da) - det2d(ba, ca) = o2 - o1
    lemma_det2d_sub_right::<T>(ba, da, ca);

    T::axiom_eqv_transitive(
        det2d(ba, dc),
        det2d(ba, da_minus_ca),
        det2d(ba, da).sub(det2d(ba, ca)),
    );
    // det2d(ba, dc) ≡ o2 - o1

    // If det2d(ba, dc) ≡ 0, then o2 - o1 ≡ 0 → o1 ≡ o2.
    // But Proper requires o1 and o2 have opposite signs → contradiction.
    if det2d(ba, dc).eqv(T::zero()) {
        // det2d(ba, dc) ≡ o2 - o1 [from chain above], symmetric: o2 - o1 ≡ det2d(ba, dc)
        T::axiom_eqv_symmetric(det2d(ba, dc), o2.sub(o1));
        // o2 - o1 ≡ det2d(ba, dc) ≡ 0
        T::axiom_eqv_transitive(o2.sub(o1), det2d(ba, dc), T::zero());
        // o2 - o1 ≡ 0 → o2 ≡ o1
        lemma_sub_zero_implies_eqv::<T>(o2, o1);
        // o1 and o2 have opposite signs → contradiction
        lemma_proper_implies_cd_opposite_sides::<T>(a, b, c, d);
        if orient2d_positive(a, b, c) && orient2d_negative(a, b, d) {
            // o1 > 0, o2 < 0, o2 ≡ o1 → o2 > 0, contradiction
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o1);
            T::axiom_eqv_symmetric(o2, o1);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o1, o2);
            T::axiom_lt_iff_le_and_not_eqv(o2, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o2);
            T::axiom_eqv_symmetric(T::zero(), o2);
        } else {
            T::axiom_eqv_symmetric(o2, o1);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), o2);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), o2, o1);
            T::axiom_lt_iff_le_and_not_eqv(o1, T::zero());
            T::axiom_le_antisymmetric(T::zero(), o1);
            T::axiom_eqv_symmetric(T::zero(), o1);
        }
    }
}

// =========================================================================
// Helper: (a - c) - (b - c) ≡ a - b
// =========================================================================

pub proof fn lemma_sub_cancel_common<T: Ring>(a: T, b: T, c: T)
    ensures
        a.sub(c).sub(b.sub(c)).eqv(a.sub(b)),
{
    // (a-c) - (b-c) ≡ (a-c) + (-(b-c))
    T::axiom_sub_is_add_neg(a.sub(c), b.sub(c));
    // -(b-c) ≡ c-b
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(b, c);
    T::axiom_neg_congruence(b.sub(c), c.sub(b).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(c.sub(b));
    T::axiom_eqv_transitive(b.sub(c).neg(), c.sub(b).neg().neg(), c.sub(b));
    // (a-c) + (-(b-c)) ≡ (a-c) + (c-b)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.sub(c), b.sub(c).neg(), c.sub(b),
    );
    T::axiom_eqv_transitive(
        a.sub(c).sub(b.sub(c)),
        a.sub(c).add(b.sub(c).neg()),
        a.sub(c).add(c.sub(b)),
    );
    // (a-c) + (c-b) ≡ a-b
    additive_group_lemmas::lemma_sub_add_sub::<T>(a, c, b);
    T::axiom_eqv_transitive(
        a.sub(c).sub(b.sub(c)),
        a.sub(c).add(c.sub(b)),
        a.sub(b),
    );
}

// =========================================================================
// Batch 1e-v: Proper intersection point lies on segment [c, d]
// =========================================================================

/// For a Proper 2D intersection, the intersection point lies on segment [c, d].
///
/// Proof:
///   1. Construct the CD-parameterized point q = c + s*(d-c) with 0 < s < 1.
///   2. Show q lies on segment [c, d] via affine_combination_on_segment.
///   3. Show p and q both lie on both lines (a,b) and (c,d).
///   4. Lines are non-parallel for Proper, so by uniqueness p ≡ q.
///   5. Transfer the bounding box from q to p.
pub proof fn lemma_proper_intersection_on_segment_cd<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        segment_intersection_kind_2d(a, b, c, d) == SegmentIntersection2dKind::Proper,
    ensures
        point_on_segment_inclusive_2d(segment_intersection_point_2d(a, b, c, d), c, d),
{
    let p = segment_intersection_point_2d(a, b, c, d);
    let s = segment_intersection_parameter_cd_2d(a, b, c, d);
    let q = segment_intersection_point_cd_2d(a, b, c, d);
    let ba = sub2(b, a);
    let dc = sub2(d, c);
    let qp = sub2(q, p);

    // === Step 1: q lies on segment [c, d] ===
    lemma_proper_cd_parameter_bounds_2d::<T>(a, b, c, d);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), s);
    T::axiom_lt_iff_le_and_not_eqv(s, T::one());
    lemma_affine_combination_on_segment::<T>(c, d, s);

    // === Step 2: Collinearity of p on line(c,d) ===
    lemma_intersection_point_on_line_cd_2d::<T>(a, b, c, d);

    // === Step 3: Both p and q on line(a,b) ===
    lemma_intersection_point_on_line_ab_2d::<T>(a, b, c, d);
    lemma_cd_point_on_line_ab_2d::<T>(a, b, c, d);

    // === Step 4: q on line(c,d) ===
    lemma_affine_point_on_line::<T>(c, d, s);

    // === Step 5: det2d(ba, qp) ≡ 0 ===
    // Component identity: (q.x-a.x)-(p.x-a.x) ≡ q.x-p.x
    lemma_sub_cancel_common::<T>(q.x, p.x, a.x);
    lemma_sub_cancel_common::<T>(q.y, p.y, a.y);
    let qa = sub2(q, a);
    let pa = sub2(p, a);
    let diff_a = Vec2 { x: qa.x.sub(pa.x), y: qa.y.sub(pa.y) };
    // det2d(ba, diff_a) ≡ orient2d(a,b,q) - orient2d(a,b,p)
    lemma_det2d_sub_right::<T>(ba, qa, pa);
    // orient2d(a,b,q) - orient2d(a,b,p) ≡ 0 - 0 ≡ 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        orient2d(a, b, q), T::zero(), orient2d(a, b, p), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        det2d(ba, diff_a),
        orient2d(a, b, q).sub(orient2d(a, b, p)),
        T::zero().sub(T::zero()),
    );
    T::axiom_eqv_transitive(det2d(ba, diff_a), T::zero().sub(T::zero()), T::zero());
    // diff_a ≡ qp → det2d(ba, qp) ≡ det2d(ba, diff_a)
    T::axiom_eqv_symmetric(diff_a.x, qp.x);
    T::axiom_eqv_symmetric(diff_a.y, qp.y);
    Vec2::<T>::axiom_eqv_reflexive(ba);
    lemma_det2d_congruence::<T>(ba, ba, qp, diff_a);
    T::axiom_eqv_transitive(det2d(ba, qp), det2d(ba, diff_a), T::zero());

    // === Step 6: det2d(dc, qp) ≡ 0 ===
    lemma_sub_cancel_common::<T>(q.x, p.x, c.x);
    lemma_sub_cancel_common::<T>(q.y, p.y, c.y);
    let qc = sub2(q, c);
    let pc = sub2(p, c);
    let diff_c = Vec2 { x: qc.x.sub(pc.x), y: qc.y.sub(pc.y) };
    lemma_det2d_sub_right::<T>(dc, qc, pc);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        orient2d(c, d, q), T::zero(), orient2d(c, d, p), T::zero(),
    );
    T::axiom_eqv_transitive(
        det2d(dc, diff_c),
        orient2d(c, d, q).sub(orient2d(c, d, p)),
        T::zero().sub(T::zero()),
    );
    T::axiom_eqv_transitive(det2d(dc, diff_c), T::zero().sub(T::zero()), T::zero());
    T::axiom_eqv_symmetric(diff_c.x, qp.x);
    T::axiom_eqv_symmetric(diff_c.y, qp.y);
    Vec2::<T>::axiom_eqv_reflexive(dc);
    lemma_det2d_congruence::<T>(dc, dc, qp, diff_c);
    T::axiom_eqv_transitive(det2d(dc, qp), det2d(dc, diff_c), T::zero());

    // === Step 7: Lines not parallel ===
    lemma_lines_not_parallel_for_proper::<T>(a, b, c, d);

    // === Step 8: Apply uniqueness → qp ≡ 0 ===
    lemma_det2d_zero_both_implies_zero::<T>(ba, dc, qp);

    // === Step 9: q ≡ p componentwise ===
    lemma_sub_zero_implies_eqv::<T>(q.x, p.x);
    lemma_sub_zero_implies_eqv::<T>(q.y, p.y);

    // === Step 10: Transfer bounding box from q to p ===
    T::axiom_eqv_reflexive(scalar_min(c.x, d.x));
    T::axiom_le_congruence(
        scalar_min(c.x, d.x), scalar_min(c.x, d.x), q.x, p.x,
    );
    T::axiom_eqv_reflexive(scalar_max(c.x, d.x));
    T::axiom_le_congruence(q.x, p.x, scalar_max(c.x, d.x), scalar_max(c.x, d.x));

    T::axiom_eqv_reflexive(scalar_min(c.y, d.y));
    T::axiom_le_congruence(
        scalar_min(c.y, d.y), scalar_min(c.y, d.y), q.y, p.y,
    );
    T::axiom_eqv_reflexive(scalar_max(c.y, d.y));
    T::axiom_le_congruence(q.y, p.y, scalar_max(c.y, d.y), scalar_max(c.y, d.y));
}

// =========================================================================
// Batch 7: Disjoint-implies-no-shared-point
// =========================================================================

// ---- Piece 1: scalar_max/min helper lemmas ----

/// If a ≤ x and b ≤ x, then max(a, b) ≤ x.
pub proof fn lemma_le_scalar_max<T: OrderedRing>(a: T, b: T, x: T)
    requires
        a.le(x),
        b.le(x),
    ensures
        scalar_max(a, b).le(x),
{
    T::axiom_le_total(a, b);
    // If a ≤ b: scalar_max = b, need b ≤ x — given.
    // If ¬(a ≤ b): scalar_max = a, need a ≤ x — given.
}

/// If x ≤ a and x ≤ b, then x ≤ min(a, b).
pub proof fn lemma_scalar_min_le<T: OrderedRing>(x: T, a: T, b: T)
    requires
        x.le(a),
        x.le(b),
    ensures
        x.le(scalar_min(a, b)),
{
    T::axiom_le_total(a, b);
    // If a ≤ b: scalar_min = a, need x ≤ a — given.
    // If ¬(a ≤ b): scalar_min = b, need x ≤ b — given.
}

// ---- Piece 2: Collinear interval overlap contradiction ----

/// If x lies in both 1D intervals [a1,a2] and [b1,b2], then
/// collinear_overlap_kind_1d(a1, a2, b1, b2) >= 0.
pub proof fn lemma_shared_point_implies_overlap_1d<T: OrderedRing>(
    x: T, a1: T, a2: T, b1: T, b2: T,
)
    requires
        scalar_min(a1, a2).le(x),
        x.le(scalar_max(a1, a2)),
        scalar_min(b1, b2).le(x),
        x.le(scalar_max(b1, b2)),
    ensures
        collinear_overlap_kind_1d(a1, a2, b1, b2) >= 0,
{
    let a_lo = scalar_min(a1, a2);
    let a_hi = scalar_max(a1, a2);
    let b_lo = scalar_min(b1, b2);
    let b_hi = scalar_max(b1, b2);
    let lo = scalar_max(a_lo, b_lo);
    let hi = scalar_min(a_hi, b_hi);

    // a_lo ≤ x and b_lo ≤ x → max(a_lo, b_lo) = lo ≤ x
    lemma_le_scalar_max::<T>(a_lo, b_lo, x);

    // x ≤ a_hi and x ≤ b_hi → x ≤ min(a_hi, b_hi) = hi
    lemma_scalar_min_le::<T>(x, a_hi, b_hi);

    // lo ≤ x ≤ hi → lo ≤ hi
    T::axiom_le_transitive(lo, x, hi);

    // lo ≤ hi → ¬(hi < lo)
    // hi.lt(lo) ↔ hi ≤ lo ∧ ¬hi ≡ lo
    T::axiom_lt_iff_le_and_not_eqv(hi, lo);
    if hi.le(lo) && !hi.eqv(lo) {
        // hi ≤ lo and lo ≤ hi → lo ≡ hi
        T::axiom_le_antisymmetric(lo, hi);
        // lo ≡ hi → hi ≡ lo
        T::axiom_eqv_symmetric(lo, hi);
        // contradiction with !hi.eqv(lo)
    }
}

// ---- Piece 3: Two-points-on-line uniqueness ----

/// If c and p are both on line(a,b), and p is on line(c,d), and d is NOT on
/// line(a,b), then p ≡ c (componentwise).
///
/// Proof: p-c lies in the kernel of both det2d(ba, ·) and det2d(dc, ·).
/// Since det2d(ba, dc) ≢ 0 (d not on line(a,b)), uniqueness gives p-c = 0.
pub proof fn lemma_zero_orient_and_shared_point_implies_eqv<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>, p: Point2<T>,
)
    requires
        orient2d(a, b, c).eqv(T::zero()),
        orient2d(a, b, p).eqv(T::zero()),
        orient2d(c, d, p).eqv(T::zero()),
        !orient2d(a, b, d).eqv(T::zero()),
    ensures
        p.x.eqv(c.x),
        p.y.eqv(c.y),
{
    let ba = sub2(b, a);
    let dc = sub2(d, c);
    let pc = sub2(p, c);
    let ca = sub2(c, a);
    let pa = sub2(p, a);
    let da = sub2(d, a);

    // Step 1: det2d(ba, pc) ≡ 0
    // orient2d(a,b,p) = det2d(ba, pa) ≡ 0
    // orient2d(a,b,c) = det2d(ba, ca) ≡ 0
    // det2d(ba, pa-ca) = det2d(ba,pa) - det2d(ba,ca) ≡ 0 - 0 ≡ 0
    let pa_minus_ca = Vec2 { x: pa.x.sub(ca.x), y: pa.y.sub(ca.y) };
    lemma_det2d_sub_right::<T>(ba, pa, ca);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        orient2d(a, b, p), T::zero(), orient2d(a, b, c), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        det2d(ba, pa_minus_ca),
        orient2d(a, b, p).sub(orient2d(a, b, c)),
        T::zero().sub(T::zero()),
    );
    T::axiom_eqv_transitive(det2d(ba, pa_minus_ca), T::zero().sub(T::zero()), T::zero());

    // pa_minus_ca ≡ pc componentwise: (p.x-a.x)-(c.x-a.x) ≡ p.x-c.x
    lemma_sub_cancel_common::<T>(p.x, c.x, a.x);
    lemma_sub_cancel_common::<T>(p.y, c.y, a.y);
    // Swap direction
    T::axiom_eqv_symmetric(pa.x.sub(ca.x), pc.x);
    T::axiom_eqv_symmetric(pa.y.sub(ca.y), pc.y);
    // det2d(ba, pc) ≡ det2d(ba, pa_minus_ca)
    Vec2::<T>::axiom_eqv_reflexive(ba);
    lemma_det2d_congruence::<T>(ba, ba, pc, pa_minus_ca);
    T::axiom_eqv_transitive(det2d(ba, pc), det2d(ba, pa_minus_ca), T::zero());

    // Step 2: det2d(dc, pc) ≡ 0
    // orient2d(c, d, p) = det2d(dc, pc) ≡ 0

    // Step 3: det2d(ba, dc) ≢ 0
    // Show det2d(ba, dc) ≡ o2 - o1 where o2 = orient2d(a,b,d), o1 = orient2d(a,b,c)
    let da_minus_ca = Vec2 { x: da.x.sub(ca.x), y: da.y.sub(ca.y) };

    // dc ≡ da_minus_ca componentwise: (d.x-c.x) ≡ (d.x-a.x)-(c.x-a.x)
    lemma_sub_cancel_common::<T>(d.x, c.x, a.x);
    lemma_sub_cancel_common::<T>(d.y, c.y, a.y);
    T::axiom_eqv_symmetric(da.x.sub(ca.x), dc.x);
    T::axiom_eqv_symmetric(da.y.sub(ca.y), dc.y);

    lemma_det2d_congruence::<T>(ba, ba, dc, da_minus_ca);
    lemma_det2d_sub_right::<T>(ba, da, ca);
    T::axiom_eqv_transitive(
        det2d(ba, dc), det2d(ba, da_minus_ca), orient2d(a, b, d).sub(orient2d(a, b, c)),
    );
    // o2 - o1 ≡ o2 - 0 ≡ o2
    T::axiom_eqv_reflexive(orient2d(a, b, d));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        orient2d(a, b, d), orient2d(a, b, d), orient2d(a, b, c), T::zero(),
    );
    // o2 - 0: use sub_is_add_neg, neg_zero, add_zero_right
    T::axiom_sub_is_add_neg(orient2d(a, b, d), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        orient2d(a, b, d), T::zero().neg(), T::zero(),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, d).sub(T::zero()),
        orient2d(a, b, d).add(T::zero().neg()),
        orient2d(a, b, d).add(T::zero()),
    );
    T::axiom_add_zero_right(orient2d(a, b, d));
    T::axiom_eqv_transitive(
        orient2d(a, b, d).sub(T::zero()),
        orient2d(a, b, d).add(T::zero()),
        orient2d(a, b, d),
    );
    // Chain: det2d(ba, dc) ≡ o2 - o1 ≡ o2 - 0 ≡ o2
    T::axiom_eqv_transitive(
        det2d(ba, dc),
        orient2d(a, b, d).sub(orient2d(a, b, c)),
        orient2d(a, b, d).sub(T::zero()),
    );
    T::axiom_eqv_transitive(
        det2d(ba, dc),
        orient2d(a, b, d).sub(T::zero()),
        orient2d(a, b, d),
    );

    // If det2d(ba, dc) ≡ 0 then o2 ≡ 0, contradiction
    if det2d(ba, dc).eqv(T::zero()) {
        T::axiom_eqv_symmetric(det2d(ba, dc), orient2d(a, b, d));
        T::axiom_eqv_transitive(orient2d(a, b, d), det2d(ba, dc), T::zero());
    }

    // Step 4: Apply uniqueness
    lemma_det2d_zero_both_implies_zero::<T>(ba, dc, pc);
    // pc.x ≡ 0 and pc.y ≡ 0

    // Step 5: p.x - c.x ≡ 0 → p.x ≡ c.x
    lemma_sub_zero_implies_eqv::<T>(p.x, c.x);
    lemma_sub_zero_implies_eqv::<T>(p.y, c.y);
}

// ---- Piece 4: Affine parameter on segment ----

/// Parameter s such that p = c + s*(d - c), choosing x-axis if c.x ≢ d.x.
pub open spec fn segment_parameter_of_point<T: OrderedField>(
    p: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> T {
    if !c.x.eqv(d.x) {
        p.x.sub(c.x).div(d.x.sub(c.x))
    } else {
        p.y.sub(c.y).div(d.y.sub(c.y))
    }
}

/// If p is on segment [c, d] and c ≢ d, then 0 ≤ s ≤ 1 where s is the parameter.
pub proof fn lemma_segment_parameter_bounds<T: OrderedField>(
    p: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        point_on_segment_inclusive_2d(p, c, d),
        !c.x.eqv(d.x) || !c.y.eqv(d.y),
    ensures
        T::zero().le(segment_parameter_of_point(p, c, d)),
        segment_parameter_of_point(p, c, d).le(T::one()),
{
    if !c.x.eqv(d.x) {
        // s = (p.x - c.x) / (d.x - c.x)
        let num = p.x.sub(c.x);
        let den = d.x.sub(c.x);

        // den ≢ 0: c.x ≢ d.x → d.x-c.x ≢ 0
        if den.eqv(T::zero()) {
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.x, c.x);
            T::axiom_eqv_symmetric(d.x, c.x);
        }

        // From bbox: scalar_min(c.x, d.x) ≤ p.x ≤ scalar_max(c.x, d.x)
        T::axiom_le_total(c.x, d.x);

        if c.x.le(d.x) {
            // c.x ≤ d.x, so scalar_min = c.x, scalar_max = d.x
            // But c.x ≢ d.x, so c.x < d.x → den > 0

            // c.x ≤ p.x → 0 ≤ p.x - c.x = num
            lemma_le_implies_sub_nonneg::<T>(c.x, p.x);
            // p.x ≤ d.x → 0 ≤ d.x - p.x, equivalently num ≤ den
            lemma_le_implies_sub_nonneg::<T>(p.x, d.x);
            ordered_ring_lemmas::lemma_le_sub_monotone::<T>(p.x, d.x, c.x);
            // p.x - c.x ≤ d.x - c.x, i.e. num ≤ den

            // 0 < den
            lemma_le_implies_sub_nonneg::<T>(c.x, d.x);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), den);
            // Need !0 ≡ den. If 0 ≡ den then den ≡ 0 contradiction
            if T::zero().eqv(den) {
                T::axiom_eqv_symmetric(T::zero(), den);
            }

            // 0 ≤ num, 0 < den → 0/den ≤ num/den i.e. 0 ≤ s
            ordered_field_lemmas::lemma_le_div_monotone::<T>(T::zero(), num, den);
            // 0/den ≡ 0
            field_lemmas::lemma_div_one::<T>(T::zero());
            ring_lemmas::lemma_mul_zero_left::<T>(den.recip());
            T::axiom_div_is_mul_recip(T::zero(), den);
            T::axiom_eqv_transitive(
                T::zero().div(den), T::zero().mul(den.recip()), T::zero(),
            );
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().div(den), T::zero(), num.div(den),
            );

            // num ≤ den, 0 < den → num/den ≤ den/den = 1
            ordered_field_lemmas::lemma_le_div_monotone::<T>(num, den, den);
            field_lemmas::lemma_div_self::<T>(den);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                num.div(den), den.div(den), T::one(),
            );
        } else {
            // d.x < c.x (¬(c.x ≤ d.x)), scalar_min = d.x, scalar_max = c.x
            // den = d.x - c.x < 0

            // d.x ≤ p.x and p.x ≤ c.x (from bbox with swapped min/max)
            // p.x ≤ c.x → c.x - p.x ≥ 0, i.e. -(p.x - c.x) ≥ 0, i.e. num ≤ 0
            // d.x ≤ p.x → p.x - c.x ≥ d.x - c.x, i.e. num ≥ den

            // Show num ≤ 0: p.x ≤ c.x → 0 ≤ c.x - p.x → -(p.x - c.x) ≥ 0
            lemma_le_implies_sub_nonneg::<T>(p.x, c.x);
            // 0 ≤ c.x - p.x, negate: p.x - c.x ≤ 0
            additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.x, p.x);
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(T::zero(), c.x.sub(p.x));
            // -(c.x-p.x) ≤ -0 ≡ 0
            additive_group_lemmas::lemma_neg_zero::<T>();
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                c.x.sub(p.x).neg(), T::zero().neg(), T::zero(),
            );
            // c.x.sub(p.x).neg() ≡ p.x.sub(c.x): -(c.x-p.x) ≡ p.x-c.x
            T::axiom_neg_congruence(c.x.sub(p.x), p.x.sub(c.x).neg());
            additive_group_lemmas::lemma_neg_involution::<T>(p.x.sub(c.x));
            T::axiom_eqv_transitive(c.x.sub(p.x).neg(), p.x.sub(c.x).neg().neg(), p.x.sub(c.x));
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                c.x.sub(p.x).neg(), num, T::zero(),
            );
            // num ≤ 0

            // Show den ≤ num: d.x ≤ p.x → d.x - c.x ≤ p.x - c.x
            ordered_ring_lemmas::lemma_le_sub_monotone::<T>(d.x, p.x, c.x);

            // Show den < 0: d.x < c.x → d.x - c.x < 0
            // ¬(c.x ≤ d.x) and le_total → d.x ≤ c.x; with !c.x.eqv(d.x) → d.x < c.x
            if d.x.eqv(c.x) { T::axiom_eqv_symmetric(d.x, c.x); }
            T::axiom_lt_iff_le_and_not_eqv(d.x, c.x);
            // d.x < c.x → d.x - c.x < c.x - c.x
            ordered_ring_lemmas::lemma_lt_sub_monotone::<T>(d.x, c.x, c.x);
            // c.x - c.x ≡ 0
            additive_group_lemmas::lemma_sub_self::<T>(c.x);
            // den < c.x-c.x and c.x-c.x ≡ 0 → den < 0
            T::axiom_lt_iff_le_and_not_eqv(den, c.x.sub(c.x));
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                den, c.x.sub(c.x), T::zero(),
            );
            if den.eqv(T::zero()) {
                T::axiom_eqv_symmetric(c.x.sub(c.x), T::zero());
                T::axiom_eqv_transitive(den, T::zero(), c.x.sub(c.x));
            }
            T::axiom_lt_iff_le_and_not_eqv(den, T::zero());
            // den < 0

            // Negate: num ≤ 0 → 0 ≤ -num
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(num, T::zero());
            additive_group_lemmas::lemma_neg_zero::<T>();
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().neg(), T::zero(), num.neg(),
            );

            // den ≤ num → -num ≤ -den
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(den, num);

            // 0 < -den (from den < 0), and -den ≢ 0
            lemma_neg_of_neg_is_pos::<T>(den);
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), den.neg());
            if den.neg().eqv(T::zero()) {
                T::axiom_eqv_symmetric(den.neg(), T::zero());
            }

            // 0 ≤ (-num) / (-den)
            ordered_field_lemmas::lemma_le_div_monotone::<T>(T::zero(), num.neg(), den.neg());
            ring_lemmas::lemma_mul_zero_left::<T>(den.neg().recip());
            T::axiom_div_is_mul_recip(T::zero(), den.neg());
            T::axiom_eqv_transitive(
                T::zero().div(den.neg()), T::zero().mul(den.neg().recip()), T::zero(),
            );
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().div(den.neg()), T::zero(), num.neg().div(den.neg()),
            );

            // (-num)/(-den) ≤ (-den)/(-den) = 1
            ordered_field_lemmas::lemma_le_div_monotone::<T>(num.neg(), den.neg(), den.neg());
            field_lemmas::lemma_div_self::<T>(den.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                num.neg().div(den.neg()), den.neg().div(den.neg()), T::one(),
            );

            // (-num)/(-den) ≡ num/den = s
            field_lemmas::lemma_div_neg_numerator::<T>(num, den.neg());
            field_lemmas::lemma_div_neg_denominator::<T>(num, den);
            // num/(-den) ≡ -(num/den)
            T::axiom_neg_congruence(num.div(den.neg()), num.div(den).neg());
            additive_group_lemmas::lemma_neg_involution::<T>(num.div(den));
            T::axiom_eqv_transitive(
                num.div(den.neg()).neg(), num.div(den).neg().neg(), num.div(den),
            );
            T::axiom_eqv_transitive(
                num.neg().div(den.neg()), num.div(den.neg()).neg(), num.div(den),
            );

            // Transfer: 0 ≤ (-num)/(-den) and (-num)/(-den) ≡ s → 0 ≤ s
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                T::zero(), num.neg().div(den.neg()), num.div(den),
            );
            // Transfer: (-num)/(-den) ≤ 1 and (-num)/(-den) ≡ s → s ≤ 1
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                num.neg().div(den.neg()), num.div(den), T::one(),
            );
        }
    } else {
        // Use y-axis: s = (p.y - c.y) / (d.y - c.y)
        // c.x ≡ d.x, so !c.y ≡ d.y
        let num = p.y.sub(c.y);
        let den = d.y.sub(c.y);

        // den ≢ 0
        if den.eqv(T::zero()) {
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.y, c.y);
            T::axiom_eqv_symmetric(d.y, c.y);
        }

        T::axiom_le_total(c.y, d.y);

        if c.y.le(d.y) {
            // Same logic as x-axis case with c.y ≤ d.y
            lemma_le_implies_sub_nonneg::<T>(c.y, p.y);
            ordered_ring_lemmas::lemma_le_sub_monotone::<T>(p.y, d.y, c.y);
            lemma_le_implies_sub_nonneg::<T>(c.y, d.y);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), den);
            if T::zero().eqv(den) { T::axiom_eqv_symmetric(T::zero(), den); }

            ordered_field_lemmas::lemma_le_div_monotone::<T>(T::zero(), num, den);
            ring_lemmas::lemma_mul_zero_left::<T>(den.recip());
            T::axiom_div_is_mul_recip(T::zero(), den);
            T::axiom_eqv_transitive(
                T::zero().div(den), T::zero().mul(den.recip()), T::zero(),
            );
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().div(den), T::zero(), num.div(den),
            );

            ordered_field_lemmas::lemma_le_div_monotone::<T>(num, den, den);
            field_lemmas::lemma_div_self::<T>(den);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                num.div(den), den.div(den), T::one(),
            );
        } else {
            // d.y < c.y case — mirror of x-axis negative denominator case
            // num ≤ 0, den < 0, den ≤ num
            lemma_le_implies_sub_nonneg::<T>(p.y, c.y);
            additive_group_lemmas::lemma_sub_antisymmetric::<T>(c.y, p.y);
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(T::zero(), c.y.sub(p.y));
            additive_group_lemmas::lemma_neg_zero::<T>();
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                c.y.sub(p.y).neg(), T::zero().neg(), T::zero(),
            );
            T::axiom_neg_congruence(c.y.sub(p.y), p.y.sub(c.y).neg());
            additive_group_lemmas::lemma_neg_involution::<T>(p.y.sub(c.y));
            T::axiom_eqv_transitive(c.y.sub(p.y).neg(), p.y.sub(c.y).neg().neg(), p.y.sub(c.y));
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                c.y.sub(p.y).neg(), num, T::zero(),
            );

            ordered_ring_lemmas::lemma_le_sub_monotone::<T>(d.y, p.y, c.y);

            if d.y.eqv(c.y) { T::axiom_eqv_symmetric(d.y, c.y); }
            T::axiom_lt_iff_le_and_not_eqv(d.y, c.y);
            ordered_ring_lemmas::lemma_lt_sub_monotone::<T>(d.y, c.y, c.y);
            additive_group_lemmas::lemma_sub_self::<T>(c.y);
            T::axiom_lt_iff_le_and_not_eqv(den, c.y.sub(c.y));
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                den, c.y.sub(c.y), T::zero(),
            );
            if den.eqv(T::zero()) {
                T::axiom_eqv_symmetric(c.y.sub(c.y), T::zero());
                T::axiom_eqv_transitive(den, T::zero(), c.y.sub(c.y));
            }
            T::axiom_lt_iff_le_and_not_eqv(den, T::zero());

            // Negate: 0 ≤ -num, 0 < -den, -num ≤ -den
            // num ≤ 0 → 0.neg() ≤ num.neg()
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(num, T::zero());
            // 0.neg() ≡ 0
            additive_group_lemmas::lemma_neg_zero::<T>();
            // Transfer: 0 ≤ -num
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().neg(), T::zero(), num.neg(),
            );
            // den ≤ num → -num ≤ -den
            ordered_ring_lemmas::lemma_le_neg_flip::<T>(den, num);
            lemma_neg_of_neg_is_pos::<T>(den);
            // -den ≢ 0
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), den.neg());
            if den.neg().eqv(T::zero()) {
                T::axiom_eqv_symmetric(den.neg(), T::zero());
            }

            // 0 ≤ (-num)/(-den)
            ordered_field_lemmas::lemma_le_div_monotone::<T>(T::zero(), num.neg(), den.neg());
            ring_lemmas::lemma_mul_zero_left::<T>(den.neg().recip());
            T::axiom_div_is_mul_recip(T::zero(), den.neg());
            T::axiom_eqv_transitive(
                T::zero().div(den.neg()), T::zero().mul(den.neg().recip()), T::zero(),
            );
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().div(den.neg()), T::zero(), num.neg().div(den.neg()),
            );

            // (-num)/(-den) ≤ 1
            ordered_field_lemmas::lemma_le_div_monotone::<T>(num.neg(), den.neg(), den.neg());
            field_lemmas::lemma_div_self::<T>(den.neg());
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                num.neg().div(den.neg()), den.neg().div(den.neg()), T::one(),
            );

            // (-num)/(-den) ≡ num/den
            field_lemmas::lemma_div_neg_numerator::<T>(num, den.neg());
            field_lemmas::lemma_div_neg_denominator::<T>(num, den);
            T::axiom_neg_congruence(num.div(den.neg()), num.div(den).neg());
            additive_group_lemmas::lemma_neg_involution::<T>(num.div(den));
            T::axiom_eqv_transitive(
                num.div(den.neg()).neg(), num.div(den).neg().neg(), num.div(den),
            );
            T::axiom_eqv_transitive(
                num.neg().div(den.neg()), num.div(den.neg()).neg(), num.div(den),
            );

            // Transfer bounds
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                T::zero(), num.neg().div(den.neg()), num.div(den),
            );
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                num.neg().div(den.neg()), num.div(den), T::one(),
            );
        }
    }
}

// ---- Piece 5: p - c ≡ s*(d - c) componentwise ----

/// If p is on segment [c, d] (non-degenerate), then p-c ≡ s*(d-c)
/// where s = segment_parameter_of_point(p, c, d).
pub proof fn lemma_point_is_affine_combination<T: OrderedField>(
    p: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        point_on_segment_inclusive_2d(p, c, d),
        !c.x.eqv(d.x) || !c.y.eqv(d.y),
    ensures ({
        let s = segment_parameter_of_point(p, c, d);
        let pc = sub2(p, c);
        let dc = sub2(d, c);
        pc.x.eqv(s.mul(dc.x)) && pc.y.eqv(s.mul(dc.y))
    }),
{
    let s = segment_parameter_of_point(p, c, d);
    let pc = sub2(p, c);
    let dc = sub2(d, c);

    if !c.x.eqv(d.x) {
        // s = (p.x-c.x) / (d.x-c.x) = pc.x / dc.x
        // x-component: pc.x ≡ s * dc.x by div_mul_cancel
        // dc.x = d.x - c.x ≢ 0
        if dc.x.eqv(T::zero()) {
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.x, c.x);
            T::axiom_eqv_symmetric(d.x, c.x);
        }
        field_lemmas::lemma_div_mul_cancel::<T>(pc.x, dc.x);
        // pc.x.div(dc.x).mul(dc.x) ≡ pc.x
        // s = pc.x / dc.x, so s * dc.x ≡ pc.x
        T::axiom_eqv_symmetric(pc.x.div(dc.x).mul(dc.x), pc.x);

        // y-component: from collinearity det2d(dc, pc) ≡ 0
        // dc.x * pc.y - dc.y * pc.x ≡ 0
        // → dc.x * pc.y ≡ dc.y * pc.x
        // → pc.y ≡ dc.y * pc.x / dc.x = dc.y * s = s * dc.y
        // orient2d(c, d, p) ≡ 0
        // orient2d(c, d, p) = det2d(dc, pc) = dc.x*pc.y - dc.y*pc.x
        lemma_sub_zero_implies_eqv::<T>(dc.x.mul(pc.y), dc.y.mul(pc.x));
        // dc.x * pc.y ≡ dc.y * pc.x

        // dc.y * pc.x ≡ dc.y * (s * dc.x) [congruence with pc.x ≡ s*dc.x]
        T::axiom_eqv_symmetric(s.mul(dc.x), pc.x);
        ring_lemmas::lemma_mul_congruence_right::<T>(dc.y, pc.x, s.mul(dc.x));
        // dc.y * (s * dc.x) ≡ (dc.y * s) * dc.x [assoc]
        T::axiom_mul_associative(dc.y, s, dc.x);
        T::axiom_eqv_symmetric(dc.y.mul(s).mul(dc.x), dc.y.mul(s.mul(dc.x)));
        T::axiom_eqv_transitive(
            dc.y.mul(pc.x), dc.y.mul(s.mul(dc.x)), dc.y.mul(s).mul(dc.x),
        );
        // Chain: dc.x * pc.y ≡ dc.y * pc.x ≡ (dc.y * s) * dc.x
        T::axiom_eqv_transitive(dc.x.mul(pc.y), dc.y.mul(pc.x), dc.y.mul(s).mul(dc.x));

        // dc.x * pc.y also ≡ (dc.x * pc.y) [trivially]
        // Want to show: pc.y ≡ dc.y * s = s * dc.y
        // From dc.x * pc.y ≡ (dc.y * s) * dc.x, cancel dc.x
        // (dc.y * s) * dc.x ≡ dc.x * (dc.y * s) [commutativity]
        T::axiom_mul_commutative(dc.y.mul(s), dc.x);
        T::axiom_eqv_transitive(
            dc.x.mul(pc.y), dc.y.mul(s).mul(dc.x), dc.x.mul(dc.y.mul(s)),
        );
        // dc.x * pc.y ≡ dc.x * (dc.y * s) → cancel dc.x
        field_lemmas::lemma_mul_cancel_left::<T>(pc.y, dc.y.mul(s), dc.x);
        // pc.y ≡ dc.y * s
        T::axiom_mul_commutative(dc.y, s);
        T::axiom_eqv_transitive(pc.y, dc.y.mul(s), s.mul(dc.y));
    } else {
        // c.x ≡ d.x, so !c.y ≡ d.y
        // s = (p.y-c.y) / (d.y-c.y) = pc.y / dc.y
        if dc.y.eqv(T::zero()) {
            additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.y, c.y);
            T::axiom_eqv_symmetric(d.y, c.y);
        }

        // y-component: pc.y ≡ s * dc.y by div_mul_cancel
        field_lemmas::lemma_div_mul_cancel::<T>(pc.y, dc.y);
        T::axiom_eqv_symmetric(pc.y.div(dc.y).mul(dc.y), pc.y);

        // x-component: dc.x ≡ 0 (from c.x ≡ d.x)
        // c.x ≡ d.x → d.x ≡ c.x → d.x - c.x ≡ 0
        T::axiom_eqv_symmetric(c.x, d.x);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(d.x, c.x);

        // From collinearity: dc.x*pc.y ≡ dc.y*pc.x
        lemma_sub_zero_implies_eqv::<T>(dc.x.mul(pc.y), dc.y.mul(pc.x));

        // dc.x * pc.y ≡ 0 * pc.y ≡ 0
        T::axiom_eqv_reflexive(pc.y);
        ring_lemmas::lemma_mul_congruence::<T>(dc.x, T::zero(), pc.y, pc.y);
        ring_lemmas::lemma_mul_zero_left::<T>(pc.y);
        T::axiom_eqv_transitive(dc.x.mul(pc.y), T::zero().mul(pc.y), T::zero());

        // dc.y * pc.x ≡ dc.x * pc.y ≡ 0
        T::axiom_eqv_symmetric(dc.x.mul(pc.y), dc.y.mul(pc.x));
        T::axiom_eqv_transitive(dc.y.mul(pc.x), dc.x.mul(pc.y), T::zero());
        // dc.y * pc.x ≡ 0 ≡ dc.y * 0, cancel dc.y → pc.x ≡ 0
        T::axiom_mul_zero_right(dc.y);
        T::axiom_eqv_symmetric(dc.y.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(dc.y.mul(pc.x), T::zero(), dc.y.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(pc.x, T::zero(), dc.y);

        // s * dc.x ≡ s * 0 ≡ 0
        ring_lemmas::lemma_mul_congruence_right::<T>(s, dc.x, T::zero());
        T::axiom_mul_zero_right(s);
        T::axiom_eqv_transitive(s.mul(dc.x), s.mul(T::zero()), T::zero());

        // pc.x ≡ 0 ≡ s * dc.x
        T::axiom_eqv_symmetric(s.mul(dc.x), T::zero());
        T::axiom_eqv_transitive(pc.x, T::zero(), s.mul(dc.x));
    }
}

// ---- Piece 6: Orient2d interpolation on segment ----

/// For p on segment [c, d] (non-degenerate):
///   orient2d(a, b, p) ≡ o1 + s*(o2 - o1)
/// where o1 = orient2d(a,b,c), o2 = orient2d(a,b,d), s = parameter.
pub proof fn lemma_orient2d_interpolation_on_segment<T: OrderedField>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>, p: Point2<T>,
)
    requires
        point_on_segment_inclusive_2d(p, c, d),
        !c.x.eqv(d.x) || !c.y.eqv(d.y),
    ensures ({
        let s = segment_parameter_of_point(p, c, d);
        let o1 = orient2d(a, b, c);
        let o2 = orient2d(a, b, d);
        orient2d(a, b, p).eqv(o1.add(s.mul(o2.sub(o1))))
    }),
{
    let s = segment_parameter_of_point(p, c, d);
    let o1 = orient2d(a, b, c);
    let o2 = orient2d(a, b, d);
    let ba = sub2(b, a);
    let ca = sub2(c, a);
    let da = sub2(d, a);
    let pa = sub2(p, a);
    let pc = sub2(p, c);
    let dc = sub2(d, c);

    // Piece 5: pc ≡ s * dc componentwise
    lemma_point_is_affine_combination::<T>(p, c, d);

    // Step 1: sub2(p, a) decomposed as ca + pc
    // pa.x = p.x - a.x = (p.x - c.x) + (c.x - a.x) = pc.x + ca.x
    additive_group_lemmas::lemma_sub_add_sub::<T>(p.x, c.x, a.x);
    T::axiom_eqv_symmetric(pc.x.add(ca.x), pa.x);
    T::axiom_add_commutative(pc.x, ca.x);
    T::axiom_eqv_transitive(pa.x, pc.x.add(ca.x), ca.x.add(pc.x));
    // Same for y
    additive_group_lemmas::lemma_sub_add_sub::<T>(p.y, c.y, a.y);
    T::axiom_eqv_symmetric(pc.y.add(ca.y), pa.y);
    T::axiom_add_commutative(pc.y, ca.y);
    T::axiom_eqv_transitive(pa.y, pc.y.add(ca.y), ca.y.add(pc.y));

    // det2d(ba, pa) ≡ det2d(ba, ca+pc)
    let ca_plus_pc = Vec2 { x: ca.x.add(pc.x), y: ca.y.add(pc.y) };
    Vec2::<T>::axiom_eqv_reflexive(ba);
    lemma_det2d_congruence::<T>(ba, ba, pa, ca_plus_pc);

    // Step 2: det2d(ba, ca+pc) ≡ det2d(ba, ca) + det2d(ba, pc) = o1 + det2d(ba, pc)
    lemma_det2d_add_right::<T>(ba, ca, pc);
    T::axiom_eqv_transitive(
        orient2d(a, b, p),
        det2d(ba, ca_plus_pc),
        det2d(ba, ca).add(det2d(ba, pc)),
    );

    // Step 3: pc ≡ scale(s, dc) componentwise, so det2d(ba, pc) ≡ det2d(ba, scale(s, dc))
    let s_dc = Vec2 { x: s.mul(dc.x), y: s.mul(dc.y) };
    lemma_det2d_congruence::<T>(ba, ba, pc, s_dc);

    // det2d(ba, scale(s, dc)) ≡ s * det2d(ba, dc)
    lemma_det2d_scale_right::<T>(s, ba, dc);
    T::axiom_eqv_transitive(det2d(ba, pc), det2d(ba, s_dc), s.mul(det2d(ba, dc)));

    // Step 4: det2d(ba, dc) ≡ o2 - o1
    // dc = d-c = (d-a)-(c-a) componentwise
    let da_minus_ca = Vec2 { x: da.x.sub(ca.x), y: da.y.sub(ca.y) };
    lemma_sub_cancel_common::<T>(d.x, c.x, a.x);
    lemma_sub_cancel_common::<T>(d.y, c.y, a.y);
    T::axiom_eqv_symmetric(da.x.sub(ca.x), dc.x);
    T::axiom_eqv_symmetric(da.y.sub(ca.y), dc.y);
    lemma_det2d_congruence::<T>(ba, ba, dc, da_minus_ca);
    lemma_det2d_sub_right::<T>(ba, da, ca);
    T::axiom_eqv_transitive(
        det2d(ba, dc), det2d(ba, da_minus_ca), o2.sub(o1),
    );

    // s * det2d(ba, dc) ≡ s * (o2 - o1)
    ring_lemmas::lemma_mul_congruence_right::<T>(s, det2d(ba, dc), o2.sub(o1));
    T::axiom_eqv_transitive(det2d(ba, pc), s.mul(det2d(ba, dc)), s.mul(o2.sub(o1)));

    // Step 5: o1 + det2d(ba, pc) ≡ o1 + s*(o2 - o1)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o1, det2d(ba, pc), s.mul(o2.sub(o1)),
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, p),
        o1.add(det2d(ba, pc)),
        o1.add(s.mul(o2.sub(o1))),
    );
}

// ---- Piece 7b: Parallelism is transitive (when reference vector is nonzero) ----

/// If det2d(u,v) ≡ 0, det2d(u,w) ≡ 0, and u is nonzero, then det2d(v,w) ≡ 0.
pub proof fn lemma_det2d_parallel_transitive<T: OrderedField>(
    u: Vec2<T>, v: Vec2<T>, w: Vec2<T>,
)
    requires
        det2d(u, v).eqv(T::zero()),
        det2d(u, w).eqv(T::zero()),
        !u.x.eqv(T::zero()) || !u.y.eqv(T::zero()),
    ensures
        det2d(v, w).eqv(T::zero()),
{
    // Unpack: u.x*v.y ≡ u.y*v.x and u.x*w.y ≡ u.y*w.x
    additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(
        u.x.mul(v.y), u.y.mul(v.x),
    ); // (*)
    additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(
        u.x.mul(w.y), u.y.mul(w.x),
    ); // (**)

    if !u.x.eqv(T::zero()) {
        // Show u.x*(v.x*w.y) ≡ u.x*(v.y*w.x), then cancel u.x.

        // --- LHS: u.x*(v.x*w.y) ≡ u.y*(v.x*w.x) ---
        // u.x*(v.x*w.y) → comm inner → u.x*(w.y*v.x)
        T::axiom_mul_commutative(v.x, w.y);
        ring_lemmas::lemma_mul_congruence_right::<T>(u.x, v.x.mul(w.y), w.y.mul(v.x));
        // → assoc → (u.x*w.y)*v.x
        T::axiom_mul_associative(u.x, w.y, v.x);
        T::axiom_eqv_symmetric(u.x.mul(w.y).mul(v.x), u.x.mul(w.y.mul(v.x)));
        T::axiom_eqv_transitive(
            u.x.mul(v.x.mul(w.y)), u.x.mul(w.y.mul(v.x)), u.x.mul(w.y).mul(v.x),
        );
        // → by (**): (u.y*w.x)*v.x
        T::axiom_mul_congruence_left(u.x.mul(w.y), u.y.mul(w.x), v.x);
        T::axiom_eqv_transitive(
            u.x.mul(v.x.mul(w.y)), u.x.mul(w.y).mul(v.x), u.y.mul(w.x).mul(v.x),
        );
        // → assoc → u.y*(w.x*v.x) → comm inner → u.y*(v.x*w.x)
        T::axiom_mul_associative(u.y, w.x, v.x);
        T::axiom_mul_commutative(w.x, v.x);
        ring_lemmas::lemma_mul_congruence_right::<T>(u.y, w.x.mul(v.x), v.x.mul(w.x));
        T::axiom_eqv_transitive(
            u.y.mul(w.x).mul(v.x), u.y.mul(w.x.mul(v.x)), u.y.mul(v.x.mul(w.x)),
        );
        T::axiom_eqv_transitive(
            u.x.mul(v.x.mul(w.y)), u.y.mul(w.x).mul(v.x), u.y.mul(v.x.mul(w.x)),
        );

        // --- RHS: u.x*(v.y*w.x) ≡ u.y*(v.x*w.x) ---
        // → assoc → (u.x*v.y)*w.x
        T::axiom_mul_associative(u.x, v.y, w.x);
        T::axiom_eqv_symmetric(u.x.mul(v.y).mul(w.x), u.x.mul(v.y.mul(w.x)));
        // → by (*): (u.y*v.x)*w.x
        T::axiom_mul_congruence_left(u.x.mul(v.y), u.y.mul(v.x), w.x);
        T::axiom_eqv_transitive(
            u.x.mul(v.y.mul(w.x)), u.x.mul(v.y).mul(w.x), u.y.mul(v.x).mul(w.x),
        );
        // → assoc → u.y*(v.x*w.x)
        T::axiom_mul_associative(u.y, v.x, w.x);
        T::axiom_eqv_transitive(
            u.x.mul(v.y.mul(w.x)), u.y.mul(v.x).mul(w.x), u.y.mul(v.x.mul(w.x)),
        );

        // LHS ≡ RHS: u.x*(v.x*w.y) ≡ u.y*(v.x*w.x) ≡ u.x*(v.y*w.x)
        T::axiom_eqv_symmetric(u.x.mul(v.y.mul(w.x)), u.y.mul(v.x.mul(w.x)));
        T::axiom_eqv_transitive(
            u.x.mul(v.x.mul(w.y)), u.y.mul(v.x.mul(w.x)), u.x.mul(v.y.mul(w.x)),
        );

        // Cancel u.x: v.x*w.y ≡ v.y*w.x
        field_lemmas::lemma_mul_cancel_left::<T>(v.x.mul(w.y), v.y.mul(w.x), u.x);

        // v.x*w.y - v.y*w.x ≡ 0
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(
            v.x.mul(w.y), v.y.mul(w.x),
        );
    } else {
        // u.x ≡ 0, u.y ≢ 0
        // From (*) and u.x ≡ 0: 0*v.y ≡ u.y*v.x → 0 ≡ u.y*v.x → v.x ≡ 0
        T::axiom_mul_congruence_left(u.x, T::zero(), v.y);
        ring_lemmas::lemma_mul_zero_left::<T>(v.y);
        T::axiom_eqv_transitive(u.x.mul(v.y), T::zero().mul(v.y), T::zero());
        T::axiom_eqv_symmetric(u.x.mul(v.y), u.y.mul(v.x));
        T::axiom_eqv_transitive(u.y.mul(v.x), u.x.mul(v.y), T::zero());
        T::axiom_mul_zero_right(u.y);
        T::axiom_eqv_symmetric(u.y.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(u.y.mul(v.x), T::zero(), u.y.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(v.x, T::zero(), u.y);

        // Similarly: w.x ≡ 0
        T::axiom_mul_congruence_left(u.x, T::zero(), w.y);
        ring_lemmas::lemma_mul_zero_left::<T>(w.y);
        T::axiom_eqv_transitive(u.x.mul(w.y), T::zero().mul(w.y), T::zero());
        T::axiom_eqv_symmetric(u.x.mul(w.y), u.y.mul(w.x));
        T::axiom_eqv_transitive(u.y.mul(w.x), u.x.mul(w.y), T::zero());
        T::axiom_mul_zero_right(u.y);
        T::axiom_eqv_symmetric(u.y.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(u.y.mul(w.x), T::zero(), u.y.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(w.x, T::zero(), u.y);

        // det2d(v,w) = v.x*w.y - v.y*w.x ≡ 0*w.y - v.y*0 ≡ 0 - 0 ≡ 0
        ring_lemmas::lemma_mul_zero_left::<T>(w.y);
        T::axiom_eqv_symmetric(T::zero().mul(w.y), T::zero());
        T::axiom_mul_congruence_left(v.x, T::zero(), w.y);
        T::axiom_eqv_transitive(v.x.mul(w.y), T::zero().mul(w.y), T::zero());

        T::axiom_mul_zero_right(v.y);
        ring_lemmas::lemma_mul_congruence_right::<T>(v.y, w.x, T::zero());
        T::axiom_eqv_transitive(v.y.mul(w.x), v.y.mul(T::zero()), T::zero());

        // 0 - 0 ≡ 0
        additive_group_lemmas::lemma_sub_self::<T>(T::zero());
        additive_group_lemmas::lemma_sub_congruence::<T>(
            v.x.mul(w.y), T::zero(), v.y.mul(w.x), T::zero(),
        );
        T::axiom_eqv_transitive(
            v.x.mul(w.y).sub(v.y.mul(w.x)),
            T::zero().sub(T::zero()),
            T::zero(),
        );
    }
}

// ---- Piece 7a: Helper — convex combination of same-sign values is nonzero ----

/// If 0 < o1, 0 < o2, 0 ≤ s ≤ 1, then o1 + s*(o2-o1) is not zero.
/// Uses weighted_average_bounds: min(o1,o2) ≤ val ≤ max(o1,o2).
/// Since both > 0, min > 0, hence val > 0 ≢ 0.
pub proof fn lemma_convex_combination_positive<T: OrderedField>(
    o1: T, o2: T, s: T,
)
    requires
        T::zero().lt(o1),
        T::zero().lt(o2),
        T::zero().le(s),
        s.le(T::one()),
    ensures
        !o1.add(s.mul(o2.sub(o1))).eqv(T::zero()),
{
    let val = o1.add(s.mul(o2.sub(o1)));

    // scalar_min(o1,o2) ≤ val
    lemma_weighted_average_bounds::<T>(o1, o2, s);

    // Determine which branch scalar_min takes
    T::axiom_le_total(o1, o2);
    // If o1.le(o2): scalar_min = o1, 0 < o1
    // If !o1.le(o2): scalar_min = o2, 0 < o2
    // Either way: 0 < scalar_min(o1,o2)
    let min_val = scalar_min(o1, o2);

    // 0 < min → 0 ≤ min and !0 ≡ min
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), min_val);

    // 0 ≤ min ≤ val → 0 ≤ val
    T::axiom_le_transitive(T::zero(), min_val, val);

    // If val ≡ 0: min ≤ val ≡ 0, so min ≤ 0.
    // Combined with 0 ≤ min → min ≡ 0, contradicts !0.eqv(min).
    if val.eqv(T::zero()) {
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(min_val, val, T::zero());
        T::axiom_le_antisymmetric(T::zero(), min_val);
        T::axiom_eqv_symmetric(T::zero(), min_val);
        // min_val.eqv(T::zero()) but !T::zero().eqv(min_val) — contradiction
    }
}

/// Same as above but for negative o1, o2.
/// Uses weighted_average_bounds: val ≤ max(o1,o2).
/// Since both < 0, max < 0, hence val < 0 ≢ 0.
pub proof fn lemma_convex_combination_negative<T: OrderedField>(
    o1: T, o2: T, s: T,
)
    requires
        o1.lt(T::zero()),
        o2.lt(T::zero()),
        T::zero().le(s),
        s.le(T::one()),
    ensures
        !o1.add(s.mul(o2.sub(o1))).eqv(T::zero()),
{
    let val = o1.add(s.mul(o2.sub(o1)));

    // val ≤ scalar_max(o1,o2)
    lemma_weighted_average_bounds::<T>(o1, o2, s);

    // Determine which branch scalar_max takes
    T::axiom_le_total(o1, o2);
    // If o1.le(o2): scalar_max = o2, o2 < 0
    // If !o1.le(o2): scalar_max = o1, o1 < 0
    // Either way: scalar_max(o1,o2) < 0
    let max_val = scalar_max(o1, o2);

    // max < 0 → max ≤ 0 and !max ≡ 0
    T::axiom_lt_iff_le_and_not_eqv(max_val, T::zero());

    // val ≤ max ≤ 0 → val ≤ 0
    T::axiom_le_transitive(val, max_val, T::zero());

    // If val ≡ 0: 0 ≡ val ≤ max, so 0 ≤ max.
    // Combined with max ≤ 0 → max ≡ 0, contradicts !max.eqv(0).
    if val.eqv(T::zero()) {
        T::axiom_eqv_symmetric(val, T::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(val, T::zero(), max_val);
        T::axiom_le_antisymmetric(max_val, T::zero());
        // max_val.eqv(T::zero()) but !max_val.eqv(T::zero()) — contradiction
    }
}

// ---- Piece 7d: Helper — endpoint is on its own segment ----

/// c is always on segment [c, d].
pub proof fn lemma_endpoint_on_own_segment<T: OrderedRing>(
    c: Point2<T>, d: Point2<T>,
)
    ensures
        point_on_segment_inclusive_2d(c, c, d),
{
    // orient2d(c,d,c) ≡ 0 via cyclic + degenerate_bc
    lemma_orient2d_cyclic::<T>(c, d, c);
    lemma_orient2d_degenerate_bc::<T>(d, c);
    T::axiom_eqv_transitive(orient2d(c, d, c), orient2d(d, c, c), T::zero());

    // bbox: scalar_min(c.x,d.x) ≤ c.x ≤ scalar_max(c.x,d.x)
    T::axiom_le_total(c.x, d.x);
    T::axiom_le_reflexive(c.x);
    T::axiom_le_total(c.y, d.y);
    T::axiom_le_reflexive(c.y);
}

// ---- Piece 7e: Helper — segment membership transfers via point equivalence ----

/// If p is on segment [a,b] and q ≡ p componentwise, then q is on [a,b].
pub proof fn lemma_segment_membership_congruence<T: OrderedRing>(
    p: Point2<T>, q: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    requires
        point_on_segment_inclusive_2d(p, a, b),
        p.x.eqv(q.x),
        p.y.eqv(q.y),
    ensures
        point_on_segment_inclusive_2d(q, a, b),
{
    // orient2d(a,b,q) ≡ 0: transfer via det2d congruence
    let ba = sub2(b, a);
    let pa = sub2(p, a);
    let qa = sub2(q, a);
    T::axiom_eqv_reflexive(a.x);
    T::axiom_eqv_reflexive(a.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(p.x, q.x, a.x, a.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(p.y, q.y, a.y, a.y);
    T::axiom_eqv_reflexive(ba.x);
    T::axiom_eqv_reflexive(ba.y);
    lemma_det2d_congruence::<T>(ba, ba, pa, qa);
    T::axiom_eqv_symmetric(orient2d(a, b, p), T::zero());
    T::axiom_eqv_transitive(T::zero(), orient2d(a, b, p), orient2d(a, b, q));
    T::axiom_eqv_symmetric(T::zero(), orient2d(a, b, q));

    // bbox transfer: 4 le_congruence calls
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        scalar_min(a.x, b.x), p.x, q.x,
    );
    ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        p.x, q.x, scalar_max(a.x, b.x),
    );
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        scalar_min(a.y, b.y), p.y, q.y,
    );
    ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        p.y, q.y, scalar_max(a.y, b.y),
    );
}

// ---- Piece 7f: Helper — derive orient2d with swapped first pair ----

/// orient2d(c,d,p) ≡ 0 implies orient2d(d,c,p) ≡ 0.
pub proof fn lemma_orient2d_swap_ab_zero<T: Ring>(
    c: Point2<T>, d: Point2<T>, p: Point2<T>,
)
    requires orient2d(c, d, p).eqv(T::zero()),
    ensures orient2d(d, c, p).eqv(T::zero()),
{
    lemma_orient2d_cyclic::<T>(d, c, p);
    // orient2d(d,c,p) ≡ orient2d(c,p,d)
    lemma_orient2d_swap_bc::<T>(c, d, p);
    // orient2d(c,p,d) ≡ -orient2d(c,d,p)
    T::axiom_neg_congruence(orient2d(c, d, p), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(orient2d(c, d, p).neg(), T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(orient2d(c, p, d), orient2d(c, d, p).neg(), T::zero());
    T::axiom_eqv_transitive(orient2d(d, c, p), orient2d(c, p, d), T::zero());
}

// ---- Piece 7: Final assembly ----

/// If a shared point p lies on both segments [a,b] and [c,d], the classification
/// is NOT Disjoint.
pub proof fn lemma_shared_point_implies_not_disjoint<T: OrderedField>(
    p: Point2<T>,
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        point_on_segment_inclusive_2d(p, a, b),
        point_on_segment_inclusive_2d(p, c, d),
    ensures
        segment_intersection_kind_2d(a, b, c, d) != SegmentIntersection2dKind::Disjoint,
{
    // ---- Ensure collinear branch never returns Disjoint ----
    // p is on both segments, so p's coordinates are in both intervals.
    // This makes overlap_kind ≥ 0 regardless of axis choice.
    let use_x = !a.x.eqv(b.x) || !c.x.eqv(d.x);
    if use_x {
        lemma_shared_point_implies_overlap_1d::<T>(p.x, a.x, b.x, c.x, d.x);
    } else {
        lemma_shared_point_implies_overlap_1d::<T>(p.y, a.y, b.y, c.y, d.y);
    }

    // Establish orientation sign meanings
    lemma_orient2d_sign_matches::<T>(a, b, c);
    lemma_orient2d_sign_matches::<T>(a, b, d);
    lemma_orient2d_sign_matches::<T>(c, d, a);
    lemma_orient2d_sign_matches::<T>(c, d, b);

    let o1 = orient2d_sign(a, b, c);
    let o2 = orient2d_sign(a, b, d);
    let o3 = orient2d_sign(c, d, a);
    let o4 = orient2d_sign(c, d, b);

    // ---- Case: all zero → collinear, overlap_kind ≥ 0 (handled above) ----
    if o1 == OrientationSign::Zero && o2 == OrientationSign::Zero
        && o3 == OrientationSign::Zero && o4 == OrientationSign::Zero
    {
        return;
    }

    // ---- Case: a ≡ b (degenerate segment [a,b]) ----
    if a.x.eqv(b.x) && a.y.eqv(b.y) {
        // Derive p ≡ a from p in bbox of [a,a]
        T::axiom_le_reflexive(a.x);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(a.x, a.x, b.x);
        T::axiom_eqv_symmetric(a.x, b.x);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(p.x, b.x, a.x);
        T::axiom_le_antisymmetric(a.x, p.x);
        T::axiom_eqv_symmetric(a.x, p.x);
        T::axiom_le_reflexive(a.y);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(a.y, a.y, b.y);
        T::axiom_eqv_symmetric(a.y, b.y);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(p.y, b.y, a.y);
        T::axiom_le_antisymmetric(a.y, p.y);
        T::axiom_eqv_symmetric(a.y, p.y);
        // p ≡ a → a on [c,d], a on [a,b] → touch3
        lemma_segment_membership_congruence::<T>(p, a, c, d);
        lemma_endpoint_on_own_segment::<T>(a, b);
        return;
    }

    // ---- Case: c ≡ d (degenerate segment [c,d]) ----
    if c.x.eqv(d.x) && c.y.eqv(d.y) {
        // Derive p ≡ c from p in bbox of [c,c]
        T::axiom_le_reflexive(c.x);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(c.x, c.x, d.x);
        T::axiom_eqv_symmetric(c.x, d.x);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(p.x, d.x, c.x);
        T::axiom_le_antisymmetric(c.x, p.x);
        T::axiom_eqv_symmetric(c.x, p.x);
        T::axiom_le_reflexive(c.y);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(c.y, c.y, d.y);
        T::axiom_eqv_symmetric(c.y, d.y);
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(p.y, d.y, c.y);
        T::axiom_le_antisymmetric(c.y, p.y);
        T::axiom_eqv_symmetric(c.y, p.y);
        // p ≡ c → c on [a,b], c on [c,d] → touch1
        lemma_segment_membership_congruence::<T>(p, c, a, b);
        lemma_endpoint_on_own_segment::<T>(c, d);
        return;
    }

    // ---- Now: a ≢ b, c ≢ d, not all zero ----
    // Show a touch holds (or derive contradiction) → not Disjoint

    if o1 == OrientationSign::Zero {
        if o2 == OrientationSign::Zero {
            // o1=o2=Zero. Derive o3=Zero via parallel-transitive.
            // ba nonzero (a ≢ b):
            let ba = sub2(b, a);
            if ba.x.eqv(T::zero()) && ba.y.eqv(T::zero()) {
                additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(b.x, a.x);
                T::axiom_eqv_symmetric(b.x, a.x);
                additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(b.y, a.y);
                T::axiom_eqv_symmetric(b.y, a.y);
                // a ≡ b — contradiction with a ≢ b
                return; // unreachable
            }
            let ca = sub2(c, a);
            let da = sub2(d, a);
            lemma_det2d_parallel_transitive::<T>(ba, ca, da);
            // det2d(ca, da) ≡ 0 → orient2d(a,c,d) ≡ 0
            // orient2d(c,d,a) ≡ orient2d(d,a,c) ≡ orient2d(a,c,d) = det2d(ca,da) ≡ 0
            lemma_orient2d_cyclic::<T>(c, d, a);
            lemma_orient2d_cyclic::<T>(d, a, c);
            T::axiom_eqv_transitive(
                orient2d(c, d, a), orient2d(d, a, c), orient2d(a, c, d),
            );
            T::axiom_eqv_transitive(orient2d(c, d, a), orient2d(a, c, d), T::zero());
            // Now o3 = Zero. Not all zero → o4 ≠ Zero.
            lemma_orient2d_sign_matches::<T>(c, d, a);
            // Apply Piece 3 with (c,d,a,b,p) → p ≡ a
            lemma_zero_orient_and_shared_point_implies_eqv::<T>(c, d, a, b, p);
            // p ≡ a → a on [c,d], a on [a,b] → touch3
            T::axiom_eqv_symmetric(p.x, a.x);
            T::axiom_eqv_symmetric(p.y, a.y);
            lemma_segment_membership_congruence::<T>(p, a, c, d);
            lemma_endpoint_on_own_segment::<T>(a, b);
        } else {
            // o1=Zero, o2≠Zero → Piece 3(a,b,c,d,p) → p ≡ c → touch1
            lemma_zero_orient_and_shared_point_implies_eqv::<T>(a, b, c, d, p);
            T::axiom_eqv_symmetric(p.x, c.x);
            T::axiom_eqv_symmetric(p.y, c.y);
            lemma_segment_membership_congruence::<T>(p, c, a, b);
            lemma_endpoint_on_own_segment::<T>(c, d);
        }
    } else if o2 == OrientationSign::Zero {
        // o1≠Zero, o2=Zero → Piece 3(a,b,d,c,p) → p ≡ d → touch2
        // Need orient2d(d,c,p) ≡ 0
        lemma_orient2d_swap_ab_zero::<T>(c, d, p);
        lemma_zero_orient_and_shared_point_implies_eqv::<T>(a, b, d, c, p);
        T::axiom_eqv_symmetric(p.x, d.x);
        T::axiom_eqv_symmetric(p.y, d.y);
        lemma_segment_membership_congruence::<T>(p, d, a, b);
        lemma_segment_membership_congruence::<T>(p, d, c, d);
    } else if o3 == OrientationSign::Zero {
        if o4 == OrientationSign::Zero {
            // o3=o4=Zero, o1≠Zero. Derive o1=Zero → contradiction.
            let dc = sub2(d, c);
            if dc.x.eqv(T::zero()) && dc.y.eqv(T::zero()) {
                additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.x, c.x);
                T::axiom_eqv_symmetric(d.x, c.x);
                additive_group_lemmas::lemma_sub_eqv_zero_implies_eqv::<T>(d.y, c.y);
                T::axiom_eqv_symmetric(d.y, c.y);
                return; // unreachable (c ≡ d already handled)
            }
            let ac = sub2(a, c);
            let bc = sub2(b, c);
            lemma_det2d_parallel_transitive::<T>(dc, ac, bc);
            // orient2d(a,b,c) ≡ orient2d(b,c,a) ≡ orient2d(c,a,b) = det2d(ac,bc) ≡ 0
            lemma_orient2d_cyclic::<T>(a, b, c);
            lemma_orient2d_cyclic::<T>(b, c, a);
            T::axiom_eqv_transitive(
                orient2d(a, b, c), orient2d(b, c, a), orient2d(c, a, b),
            );
            T::axiom_eqv_transitive(orient2d(a, b, c), orient2d(c, a, b), T::zero());
            // o1 = Zero. But o1 ≠ Zero. Contradiction.
            lemma_orient2d_sign_matches::<T>(a, b, c);
        } else {
            // o3=Zero, o4≠Zero → Piece 3(c,d,a,b,p) → p ≡ a → touch3
            lemma_zero_orient_and_shared_point_implies_eqv::<T>(c, d, a, b, p);
            T::axiom_eqv_symmetric(p.x, a.x);
            T::axiom_eqv_symmetric(p.y, a.y);
            lemma_segment_membership_congruence::<T>(p, a, c, d);
            lemma_endpoint_on_own_segment::<T>(a, b);
        }
    } else if o4 == OrientationSign::Zero {
        // o3≠Zero, o4=Zero → Piece 3(c,d,b,a,p) → p ≡ b → touch4
        // Need orient2d(b,a,p) ≡ 0
        lemma_orient2d_swap_ab_zero::<T>(a, b, p);
        lemma_zero_orient_and_shared_point_implies_eqv::<T>(c, d, b, a, p);
        T::axiom_eqv_symmetric(p.x, b.x);
        T::axiom_eqv_symmetric(p.y, b.y);
        lemma_segment_membership_congruence::<T>(p, b, c, d);
        lemma_segment_membership_congruence::<T>(p, b, a, b);
    } else {
        // All nonzero: o1≠Zero, o2≠Zero, o3≠Zero, o4≠Zero
        if o1 == o2 {
            // Same sign on AB → interpolation contradiction
            // orient2d(a,b,p) ≡ o1_val + s*(o2_val - o1_val) via Piece 6
            lemma_orient2d_interpolation_on_segment::<T>(a, b, c, d, p);
            let s = segment_parameter_of_point(p, c, d);
            let o1_val = orient2d(a, b, c);
            let o2_val = orient2d(a, b, d);
            let interp = o1_val.add(s.mul(o2_val.sub(o1_val)));

            lemma_segment_parameter_bounds::<T>(p, c, d);

            if o1 == OrientationSign::Positive {
                // Both positive
                lemma_convex_combination_positive::<T>(o1_val, o2_val, s);
            } else {
                // Both negative (can't be Zero since all nonzero)
                lemma_convex_combination_negative::<T>(o1_val, o2_val, s);
            }
            // interp ≢ 0 but orient2d(a,b,p) ≡ interp ≡ 0 — contradiction
            T::axiom_eqv_symmetric(orient2d(a, b, p), T::zero());
            T::axiom_eqv_transitive(T::zero(), orient2d(a, b, p), interp);
            T::axiom_eqv_symmetric(T::zero(), interp);
        } else if o3 == o4 {
            // Same sign on CD → interpolation contradiction
            lemma_orient2d_interpolation_on_segment::<T>(c, d, a, b, p);
            let t = segment_parameter_of_point(p, a, b);
            let o3_val = orient2d(c, d, a);
            let o4_val = orient2d(c, d, b);
            let interp = o3_val.add(t.mul(o4_val.sub(o3_val)));

            lemma_segment_parameter_bounds::<T>(p, a, b);

            if o3 == OrientationSign::Positive {
                lemma_convex_combination_positive::<T>(o3_val, o4_val, t);
            } else {
                lemma_convex_combination_negative::<T>(o3_val, o4_val, t);
            }
            T::axiom_eqv_symmetric(orient2d(c, d, p), T::zero());
            T::axiom_eqv_transitive(T::zero(), orient2d(c, d, p), interp);
            T::axiom_eqv_symmetric(T::zero(), interp);
        }
        // else: o1≠o2 && o3≠o4 && all nonzero → Proper → not Disjoint
    }
}

} // verus!
