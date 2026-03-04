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
proof fn lemma_sub2_add_vec2_cancel<T: Ring>(a: Point2<T>, v: Vec2<T>)
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
proof fn lemma_sub2_add_vec2_decompose<T: Ring>(a: Point2<T>, v: Vec2<T>, c: Point2<T>)
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

} // verus!
