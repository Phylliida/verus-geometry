use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::scale;
use crate::point2::*;
use crate::point3::*;
use crate::orient2d::*;
use crate::orient3d::*;
use crate::orientation_sign::*;
use crate::sidedness::*;

verus! {

// =========================================================================
// 6.1 — Segment-plane intersection
// =========================================================================

/// Intersection parameter t for segment (d, e) crossing plane (a, b, c).
///
/// t = orient3d(a,b,c,d) / (orient3d(a,b,c,d) - orient3d(a,b,c,e))
///
/// The intersection point is d + t*(e - d).
/// Requires OrderedField for division.
pub open spec fn segment_plane_intersection_parameter<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> T {
    let od = orient3d(a, b, c, d);
    let oe = orient3d(a, b, c, e);
    od.div(od.add(oe.neg()))
}

/// The intersection point: d + t * (e - d).
pub open spec fn segment_plane_intersection_point<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> Point3<T> {
    let t = segment_plane_intersection_parameter(d, e, a, b, c);
    let dir = sub3(e, d);
    add_vec3(d, scale(t, dir))
}

/// The denominator orient3d(a,b,c,d) - orient3d(a,b,c,e) is nonzero
/// when the segment strictly crosses the plane.
pub proof fn lemma_crossing_denominator_nonzero<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures ({
        let od = orient3d(a, b, c, d);
        let oe = orient3d(a, b, c, e);
        !od.add(oe.neg()).eqv(T::zero())
    }),
{
    let od = orient3d(a, b, c, d);
    let oe = orient3d(a, b, c, e);
    let denom = od.add(oe.neg());

    if denom.eqv(T::zero()) {
        // od + (-oe) ≡ 0 implies (-oe) ≡ -(od)
        additive_group_lemmas::lemma_neg_unique::<T>(od, oe.neg());
        // neg both sides: oe ≡ od
        T::axiom_neg_congruence(oe.neg(), od.neg());
        additive_group_lemmas::lemma_neg_involution::<T>(oe);
        additive_group_lemmas::lemma_neg_involution::<T>(od);
        T::axiom_eqv_symmetric(oe.neg().neg(), oe);
        T::axiom_eqv_transitive(oe, oe.neg().neg(), od.neg().neg());
        T::axiom_eqv_transitive(oe, od.neg().neg(), od);

        if point_above_plane(d, a, b, c) && point_below_plane(e, a, b, c) {
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), od);
            T::axiom_eqv_symmetric(oe, od);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), od, oe);
            T::axiom_lt_iff_le_and_not_eqv(oe, T::zero());
            T::axiom_le_antisymmetric(T::zero(), oe);
            T::axiom_eqv_symmetric(T::zero(), oe);
        } else {
            T::axiom_eqv_symmetric(oe, od);
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), oe);
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), oe, od);
            T::axiom_lt_iff_le_and_not_eqv(od, T::zero());
            T::axiom_le_antisymmetric(T::zero(), od);
            T::axiom_eqv_symmetric(T::zero(), od);
        }
    }
}

// =========================================================================
// 2D projection helpers (for segment-triangle)
// =========================================================================

/// Project 3D point to 2D by dropping the z coordinate.
pub open spec fn project_drop_z<T: Ring>(p: Point3<T>) -> Point2<T> {
    Point2 { x: p.x, y: p.y }
}

/// Project 3D point to 2D by dropping the y coordinate.
pub open spec fn project_drop_y<T: Ring>(p: Point3<T>) -> Point2<T> {
    Point2 { x: p.x, y: p.z }
}

/// Project 3D point to 2D by dropping the x coordinate.
pub open spec fn project_drop_x<T: Ring>(p: Point3<T>) -> Point2<T> {
    Point2 { x: p.y, y: p.z }
}

// =========================================================================
// Triangle normal component checks (for choosing projection axis)
// =========================================================================

/// The cross product normal of triangle (a, b, c).
pub open spec fn triangle_normal<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> Vec3<T> {
    verus_linalg::vec3::ops::cross(sub3(b, a), sub3(c, a))
}

/// Which axis to use for 2D projection: drop the axis where
/// the triangle normal is nonzero.
/// Returns 0 (drop x), 1 (drop y), 2 (drop z).
pub open spec fn triangle_projection_axis<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> int {
    let n = triangle_normal(a, b, c);
    if !n.x.eqv(T::zero()) {
        0  // drop x
    } else if !n.y.eqv(T::zero()) {
        1  // drop y
    } else {
        2  // drop z
    }
}

/// Project a 3D point to 2D using the chosen axis.
pub open spec fn project_by_axis<T: Ring>(p: Point3<T>, axis: int) -> Point2<T> {
    if axis == 0 {
        project_drop_x(p)
    } else if axis == 1 {
        project_drop_y(p)
    } else {
        project_drop_z(p)
    }
}

// =========================================================================
// 6.2 — Point in triangle (3D, via 2D projection)
// =========================================================================

/// Point p (assumed coplanar with triangle) is inside triangle (a, b, c)
/// boundary inclusive, checked via 2D projection.
pub open spec fn point_in_triangle_on_plane<T: OrderedRing>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    let axis = triangle_projection_axis(a, b, c);
    let p2 = project_by_axis(p, axis);
    let a2 = project_by_axis(a, axis);
    let b2 = project_by_axis(b, axis);
    let c2 = project_by_axis(c, axis);
    let o1 = orient2d_sign(a2, b2, p2);
    let o2 = orient2d_sign(b2, c2, p2);
    let o3 = orient2d_sign(c2, a2, p2);
    !(
        (o1 == OrientationSign::Positive && (o2 == OrientationSign::Negative || o3 == OrientationSign::Negative))
        || (o1 == OrientationSign::Negative && (o2 == OrientationSign::Positive || o3 == OrientationSign::Positive))
        || (o2 == OrientationSign::Positive && o3 == OrientationSign::Negative)
        || (o2 == OrientationSign::Negative && o3 == OrientationSign::Positive)
    )
}

// =========================================================================
// 6.2 — Segment-triangle intersection
// =========================================================================

/// Segment (d, e) strictly intersects triangle (a, b, c).
pub open spec fn segment_triangle_intersects_strict<T: OrderedField>(
    seg_start: Point3<T>, seg_end: Point3<T>,
    tri_a: Point3<T>, tri_b: Point3<T>, tri_c: Point3<T>,
) -> bool {
    &&& segment_crosses_plane_strict(seg_start, seg_end, tri_a, tri_b, tri_c)
    &&& ({
        let p = segment_plane_intersection_point(seg_start, seg_end, tri_a, tri_b, tri_c);
        point_in_triangle_on_plane(p, tri_a, tri_b, tri_c)
    })
}

/// If a segment-triangle intersection exists, the segment must cross the plane.
pub proof fn lemma_segment_triangle_implies_crossing<T: OrderedField>(
    seg_start: Point3<T>, seg_end: Point3<T>,
    tri_a: Point3<T>, tri_b: Point3<T>, tri_c: Point3<T>,
)
    requires
        segment_triangle_intersects_strict(seg_start, seg_end, tri_a, tri_b, tri_c),
    ensures
        segment_crosses_plane_strict(seg_start, seg_end, tri_a, tri_b, tri_c),
{
}

/// If a segment-triangle intersection exists, the endpoints are not on the plane.
pub proof fn lemma_segment_triangle_endpoints_off_plane<T: OrderedField>(
    seg_start: Point3<T>, seg_end: Point3<T>,
    tri_a: Point3<T>, tri_b: Point3<T>, tri_c: Point3<T>,
)
    requires
        segment_triangle_intersects_strict(seg_start, seg_end, tri_a, tri_b, tri_c),
    ensures
        !point_on_plane(seg_start, tri_a, tri_b, tri_c),
        !point_on_plane(seg_end, tri_a, tri_b, tri_c),
{
    lemma_crossing_implies_d_not_on_plane::<T>(seg_start, seg_end, tri_a, tri_b, tri_c);
    lemma_crossing_implies_e_not_on_plane::<T>(seg_start, seg_end, tri_a, tri_b, tri_c);
}

// =========================================================================
// Helpers for parameter bounds proof
// =========================================================================

/// a < 0 implies 0 < a.neg()
pub proof fn lemma_neg_of_neg_is_pos<T: OrderedRing>(a: T)
    requires
        a.lt(T::zero()),
    ensures
        T::zero().lt(a.neg()),
{
    // a < 0 → 0.neg() < a.neg()
    ordered_ring_lemmas::lemma_lt_neg_flip::<T>(a, T::zero());
    // 0.neg() ≡ 0
    additive_group_lemmas::lemma_neg_zero::<T>();
    // Decompose: 0.neg() < a.neg() → 0.neg() ≤ a.neg() ∧ ¬(0.neg() ≡ a.neg())
    T::axiom_lt_iff_le_and_not_eqv(T::zero().neg(), a.neg());
    // Transfer le: 0.neg() ≡ 0 ∧ 0.neg() ≤ a.neg() → 0 ≤ a.neg()
    ordered_ring_lemmas::lemma_le_congruence_left::<T>(
        T::zero().neg(), T::zero(), a.neg(),
    );
    // For strict: ¬(0 ≡ a.neg())
    // If 0 ≡ a.neg(), then since 0.neg() ≡ 0, by transitivity 0.neg() ≡ a.neg()
    // But ¬(0.neg() ≡ a.neg()). Contradiction.
    if T::zero().eqv(a.neg()) {
        T::axiom_eqv_transitive(T::zero().neg(), T::zero(), a.neg());
    }
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), a.neg());
}

/// 0 < a implies a.neg() < 0
pub proof fn lemma_neg_of_pos_is_neg<T: OrderedRing>(a: T)
    requires
        T::zero().lt(a),
    ensures
        a.neg().lt(T::zero()),
{
    // 0 < a → a.neg() < 0.neg()
    ordered_ring_lemmas::lemma_lt_neg_flip::<T>(T::zero(), a);
    // 0.neg() ≡ 0
    additive_group_lemmas::lemma_neg_zero::<T>();
    // Decompose: a.neg() < 0.neg() → a.neg() ≤ 0.neg() ∧ ¬(a.neg() ≡ 0.neg())
    T::axiom_lt_iff_le_and_not_eqv(a.neg(), T::zero().neg());
    // Transfer le: a.neg() ≤ 0.neg() ∧ 0.neg() ≡ 0 → a.neg() ≤ 0
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        a.neg(), T::zero().neg(), T::zero(),
    );
    // For strict: ¬(a.neg() ≡ 0)
    // Get 0 ≡ 0.neg() from neg_zero + symmetric
    T::axiom_eqv_symmetric(T::zero().neg(), T::zero());
    if a.neg().eqv(T::zero()) {
        // a.neg() ≡ 0 and 0 ≡ 0.neg() → a.neg() ≡ 0.neg()
        T::axiom_eqv_transitive(a.neg(), T::zero(), T::zero().neg());
        // But ¬(a.neg() ≡ 0.neg()). Contradiction.
    }
    T::axiom_lt_iff_le_and_not_eqv(a.neg(), T::zero());
}

/// Transfer 0 < a*r to 0 < a/b when a/b ≡ a*r.
/// (Used to transfer positivity from mul form to div form.)
pub proof fn lemma_lt_transfer_eqv<T: OrderedRing>(a: T, b: T)
    requires
        T::zero().lt(a),
        a.eqv(b),
    ensures
        T::zero().lt(b),
{
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), a);
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), a, b);
    if T::zero().eqv(b) {
        T::axiom_eqv_symmetric(T::zero(), b);
        T::axiom_eqv_transitive(a, b, T::zero());
        T::axiom_eqv_symmetric(a, T::zero());
    }
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), b);
}

/// If 0 < num < denom, then 0 < num/denom < 1.
pub proof fn lemma_positive_ratio_bounds<T: OrderedField>(num: T, denom: T)
    requires
        T::zero().lt(num),
        num.lt(denom),
    ensures
        T::zero().lt(num.div(denom)),
        num.div(denom).lt(T::one()),
{
    // 0 < num < denom → 0 < denom
    ordered_ring_lemmas::lemma_lt_transitive::<T>(T::zero(), num, denom);

    // Establish !denom.eqv(0) from 0 < denom
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), denom);
    // ¬(0 ≡ denom), need ¬(denom ≡ 0)
    if denom.eqv(T::zero()) {
        T::axiom_eqv_symmetric(denom, T::zero());
    }

    // --- 0 < num/denom ---
    // recip_pos: 0 < denom → 0 < recip(denom)
    ordered_field_lemmas::lemma_recip_pos::<T>(denom);
    // mul_pos_pos: 0 < num ∧ 0 < recip(denom) → 0 < num * recip(denom)
    ordered_field_lemmas::lemma_mul_pos_pos::<T>(num, denom.recip());
    // div_is_mul_recip: num/denom ≡ num * recip(denom)
    T::axiom_div_is_mul_recip(num, denom);
    T::axiom_eqv_symmetric(num.div(denom), num.mul(denom.recip()));
    // Transfer: 0 < num*r ∧ num*r ≡ num/denom → 0 < num/denom
    lemma_lt_transfer_eqv::<T>(num.mul(denom.recip()), num.div(denom));

    // --- num/denom < 1 ---
    // num < denom → num ≤ denom
    T::axiom_lt_iff_le_and_not_eqv(num, denom);
    // le_div_monotone: num ≤ denom ∧ 0 < denom → num/denom ≤ denom/denom
    ordered_field_lemmas::lemma_le_div_monotone::<T>(num, denom, denom);
    // div_self: denom/denom ≡ 1
    field_lemmas::lemma_div_self::<T>(denom);
    // num/denom ≤ denom/denom ≡ 1
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(
        num.div(denom), denom.div(denom), T::one(),
    );
    // For strict: ¬(num/denom ≡ 1)
    if num.div(denom).eqv(T::one()) {
        // num/denom ≡ 1 ≡ denom/denom → num ≡ denom by mul_cancel
        T::axiom_eqv_symmetric(denom.div(denom), T::one());
        T::axiom_eqv_transitive(num.div(denom), T::one(), denom.div(denom));
        // num/denom ≡ denom/denom
        T::axiom_mul_congruence_left(num.div(denom), denom.div(denom), denom);
        // num/denom * denom ≡ denom/denom * denom
        field_lemmas::lemma_div_mul_cancel::<T>(num, denom);
        field_lemmas::lemma_div_mul_cancel::<T>(denom, denom);
        // od ≡ ... ≡ denom
        T::axiom_eqv_symmetric(num.div(denom).mul(denom), num);
        T::axiom_eqv_transitive(
            num, num.div(denom).mul(denom), denom.div(denom).mul(denom),
        );
        T::axiom_eqv_transitive(num, denom.div(denom).mul(denom), denom);
        // num ≡ denom, but num < denom → ¬(num ≡ denom). Contradiction.
    }
    T::axiom_lt_iff_le_and_not_eqv(num.div(denom), T::one());
}

// =========================================================================
// Lemma: 0 < t < 1 for crossing parameter
// =========================================================================

/// When a segment strictly crosses a plane, the intersection parameter
/// t = od / (od - oe) satisfies 0 < t < 1.
pub proof fn lemma_crossing_parameter_bounds<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures ({
        let t = segment_plane_intersection_parameter(d, e, a, b, c);
        T::zero().lt(t) && t.lt(T::one())
    }),
{
    let od = orient3d(a, b, c, d);
    let oe = orient3d(a, b, c, e);
    let denom = od.add(oe.neg());
    let t = od.div(denom);

    lemma_crossing_denominator_nonzero::<T>(d, e, a, b, c);

    if point_above_plane(d, a, b, c) && point_below_plane(e, a, b, c) {
        // Case 1: od > 0, oe < 0
        // Show 0 < -oe
        lemma_neg_of_neg_is_pos::<T>(oe);

        // Show od < denom: 0 < -oe → od + 0 < od + (-oe) = denom
        // lt_add_compatible(0, -oe, od): 0 < -oe → 0+od < (-oe)+od
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(T::zero(), oe.neg(), od);
        // 0+od ≡ od
        additive_group_lemmas::lemma_add_zero_left::<T>(od);
        // (-oe)+od ≡ od+(-oe) = denom
        T::axiom_add_commutative(oe.neg(), od);
        // Transfer: 0+od < (-oe)+od → od < denom
        lemma_lt_congruence_both::<T>(
            T::zero().add(od), od,
            oe.neg().add(od), od.add(oe.neg()),
        );

        // Apply positive ratio bounds
        lemma_positive_ratio_bounds::<T>(od, denom);
    } else {
        // Case 2: od < 0, oe > 0
        // Show -oe < 0
        lemma_neg_of_pos_is_neg::<T>(oe);
        // Show denom < 0: od < 0, -oe < 0 → denom = od + (-oe) < 0
        lemma_sum_of_negatives_is_negative::<T>(od, oe.neg());

        // Show od.neg() > 0, denom.neg() > 0
        lemma_neg_of_neg_is_pos::<T>(od);
        lemma_neg_of_neg_is_pos::<T>(denom);

        // Show denom < od (so od.neg() < denom.neg()):
        // -oe < 0 → (-oe)+od < 0+od → denom < od
        ordered_ring_lemmas::lemma_lt_add_compatible::<T>(oe.neg(), T::zero(), od);
        additive_group_lemmas::lemma_add_zero_left::<T>(od);
        T::axiom_add_commutative(oe.neg(), od);
        lemma_lt_congruence_both::<T>(
            oe.neg().add(od), od.add(oe.neg()),
            T::zero().add(od), od,
        );
        // denom < od → od.neg() < denom.neg()
        ordered_ring_lemmas::lemma_lt_neg_flip::<T>(denom, od);

        // Apply positive ratio bounds to od.neg()/denom.neg()
        lemma_positive_ratio_bounds::<T>(od.neg(), denom.neg());
        // 0 < od.neg()/denom.neg() < 1

        // Show t ≡ od.neg()/denom.neg()
        // div_neg_denominator(od.neg(), denom): od.neg()/denom.neg() ≡ (od.neg()/denom).neg()
        field_lemmas::lemma_div_neg_denominator::<T>(od.neg(), denom);
        // div_neg_numerator(od, denom): od.neg()/denom ≡ (od/denom).neg()
        field_lemmas::lemma_div_neg_numerator::<T>(od, denom);
        // (od.neg()/denom).neg() ≡ ((od/denom).neg()).neg()
        T::axiom_neg_congruence(od.neg().div(denom), od.div(denom).neg());
        // Chain: od.neg()/denom.neg() ≡ (od.neg()/denom).neg() ≡ (od/denom).neg().neg()
        T::axiom_eqv_transitive(
            od.neg().div(denom.neg()),
            od.neg().div(denom).neg(),
            od.div(denom).neg().neg(),
        );
        // neg_involution: (od/denom).neg().neg() ≡ od/denom
        additive_group_lemmas::lemma_neg_involution::<T>(od.div(denom));
        T::axiom_eqv_transitive(
            od.neg().div(denom.neg()),
            od.div(denom).neg().neg(),
            od.div(denom),
        );
        // od.neg()/denom.neg() ≡ t

        // Transfer bounds from od.neg()/denom.neg() to t
        lemma_lt_transfer_eqv::<T>(od.neg().div(denom.neg()), od.div(denom));

        // For t < 1: od.neg()/denom.neg() ≤ 1 and od.neg()/denom.neg() ≡ t → t ≤ 1
        // Then strict via same not-eqv argument
        T::axiom_lt_iff_le_and_not_eqv(od.neg().div(denom.neg()), T::one());
        T::axiom_eqv_symmetric(od.neg().div(denom.neg()), od.div(denom));
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            od.neg().div(denom.neg()), od.div(denom), T::one(),
        );
        // t ≤ 1. For strict: ¬(t ≡ 1)
        if od.div(denom).eqv(T::one()) {
            T::axiom_eqv_transitive(od.neg().div(denom.neg()), od.div(denom), T::one());
            // od.neg()/denom.neg() ≡ 1, contradicts od.neg()/denom.neg() < 1
        }
        T::axiom_lt_iff_le_and_not_eqv(od.div(denom), T::one());
    }
}

/// Transfer a < b to c < d when a ≡ c and b ≡ d.
pub proof fn lemma_lt_congruence_both<T: OrderedRing>(a: T, c: T, b: T, d: T)
    requires
        a.lt(b),
        a.eqv(c),
        b.eqv(d),
    ensures
        c.lt(d),
{
    T::axiom_lt_iff_le_and_not_eqv(a, b);
    ordered_ring_lemmas::lemma_le_congruence_left::<T>(a, c, b);
    ordered_ring_lemmas::lemma_le_congruence_right::<T>(c, b, d);
    // c ≤ d. Need ¬(c ≡ d).
    if c.eqv(d) {
        // c ≡ d, a ≡ c, b ≡ d → a ≡ b. But a < b → ¬(a ≡ b). Contradiction.
        T::axiom_eqv_symmetric(a, c);
        T::axiom_eqv_transitive(a, c, d);
        T::axiom_eqv_symmetric(b, d);
        T::axiom_eqv_transitive(a, d, b);
    }
    T::axiom_lt_iff_le_and_not_eqv(c, d);
}

/// Show denom < 0 from od < 0 and oe.neg() < 0.
pub proof fn lemma_sum_of_negatives_is_negative<T: OrderedRing>(a: T, b: T)
    requires
        a.lt(T::zero()),
        b.lt(T::zero()),
    ensures
        a.add(b).lt(T::zero()),
{
    // a < 0 and b < 0 → a + b < 0 + 0
    ordered_ring_lemmas::lemma_lt_add_both::<T>(a, T::zero(), b, T::zero());
    // 0 + 0 ≡ 0
    T::axiom_add_zero_right(T::zero());
    // a+b ≡ a+b (reflexive)
    T::axiom_eqv_reflexive(a.add(b));
    // Transfer: a+b < 0+0 → a+b < 0
    lemma_lt_congruence_both::<T>(
        a.add(b), a.add(b),
        T::zero().add(T::zero()), T::zero(),
    );
}


// =========================================================================
// Helpers for intersection-point-on-plane proof
// =========================================================================

/// Scalar: (a+b)-c ≡ (a-c)+b, bridging opaque sub via axiom_sub_is_add_neg.
pub proof fn lemma_add_sub_rearrange<T: Ring>(a: T, b: T, c: T)
    ensures
        a.add(b).sub(c).eqv(a.sub(c).add(b)),
{
    // a.add(b).sub(c) ≡ a.add(b).add(c.neg())
    T::axiom_sub_is_add_neg(a.add(b), c);
    // Swap: a+b+(-c) ≡ a+(-c)+b via assoc+comm
    T::axiom_add_associative(a, b, c.neg());
    T::axiom_add_commutative(b, c.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.add(c.neg()), c.neg().add(b));
    T::axiom_eqv_transitive(
        a.add(b).add(c.neg()),
        a.add(b.add(c.neg())),
        a.add(c.neg().add(b)),
    );
    T::axiom_add_associative(a, c.neg(), b);
    T::axiom_eqv_symmetric(a.add(c.neg()).add(b), a.add(c.neg().add(b)));
    T::axiom_eqv_transitive(
        a.add(b).add(c.neg()),
        a.add(c.neg().add(b)),
        a.add(c.neg()).add(b),
    );
    // Chain: a.add(b).sub(c) ≡ a.add(b).add(c.neg()) ≡ a.add(c.neg()).add(b)
    T::axiom_eqv_transitive(
        a.add(b).sub(c),
        a.add(b).add(c.neg()),
        a.add(c.neg()).add(b),
    );
    // a.add(c.neg()) ≡ a.sub(c)
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    T::axiom_add_congruence_left(a.add(c.neg()), a.sub(c), b);
    T::axiom_eqv_transitive(
        a.add(b).sub(c),
        a.add(c.neg()).add(b),
        a.sub(c).add(b),
    );
}

/// sub3(add_vec3(d, w), a) ≡ sub3(d, a).add(w)
pub proof fn lemma_sub3_add_vec3<T: Ring>(
    d: Point3<T>, w: Vec3<T>, a: Point3<T>,
)
    ensures
        sub3(add_vec3(d, w), a).eqv(sub3(d, a).add(w)),
{
    lemma_add_sub_rearrange::<T>(d.x, w.x, a.x);
    lemma_add_sub_rearrange::<T>(d.y, w.y, a.y);
    lemma_add_sub_rearrange::<T>(d.z, w.z, a.z);
}

/// Scalar: e-d ≡ (e-a)-(d-a)
pub proof fn lemma_sub_triangle_scalar<T: Ring>(e: T, d: T, a: T)
    ensures
        e.sub(d).eqv(e.sub(a).sub(d.sub(a))),
{
    // sub_add_sub: (e-a)+(a-d) ≡ e-d
    additive_group_lemmas::lemma_sub_add_sub::<T>(e, a, d);
    T::axiom_eqv_symmetric(e.sub(a).add(a.sub(d)), e.sub(d));
    // sub_antisymmetric: a-d ≡ -(d-a)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a, d);
    // congruence: (e-a)+(a-d) ≡ (e-a)+(-(d-a))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        e.sub(a), a.sub(d), d.sub(a).neg(),
    );
    T::axiom_eqv_transitive(
        e.sub(d),
        e.sub(a).add(a.sub(d)),
        e.sub(a).add(d.sub(a).neg()),
    );
    // (e-a)+neg(d-a) ≡ (e-a)-(d-a) via sub_is_add_neg reversed
    T::axiom_sub_is_add_neg(e.sub(a), d.sub(a));
    T::axiom_eqv_symmetric(e.sub(a).sub(d.sub(a)), e.sub(a).add(d.sub(a).neg()));
    T::axiom_eqv_transitive(
        e.sub(d),
        e.sub(a).add(d.sub(a).neg()),
        e.sub(a).sub(d.sub(a)),
    );
}

/// sub3(e, d) ≡ sub3(e, a).sub(sub3(d, a))
pub proof fn lemma_sub3_triangle<T: Ring>(
    e: Point3<T>, d: Point3<T>, a: Point3<T>,
)
    ensures
        sub3(e, d).eqv(sub3(e, a).sub(sub3(d, a))),
{
    lemma_sub_triangle_scalar::<T>(e.x, d.x, a.x);
    lemma_sub_triangle_scalar::<T>(e.y, d.y, a.y);
    lemma_sub_triangle_scalar::<T>(e.z, d.z, a.z);
}

use verus_algebra::lemmas::ring_lemmas;

/// Algebraic cancellation: od + (od/denom) * (-(denom)) ≡ 0.
/// Here oe_minus_od = oe.add(od.neg()) and denom = od.add(oe.neg()).
/// We prove od + t * oe_minus_od ≡ 0 where t = od/denom.
pub proof fn lemma_orient_cancel<T: OrderedField>(od: T, oe: T)
    requires
        !od.add(oe.neg()).eqv(T::zero()),
    ensures
        od.add(od.div(od.add(oe.neg())).mul(oe.add(od.neg()))).eqv(T::zero()),
{
    let denom = od.add(oe.neg());
    let t = od.div(denom);
    let eo = oe.add(od.neg());

    // Step 1: eo ≡ denom.neg()
    // denom.neg() = (od + (-oe)).neg() ≡ od.neg() + (-oe).neg()
    additive_group_lemmas::lemma_neg_add::<T>(od, oe.neg());
    // (-oe).neg() ≡ oe
    additive_group_lemmas::lemma_neg_involution::<T>(oe);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od.neg(), oe.neg().neg(), oe,
    );
    T::axiom_eqv_transitive(
        denom.neg(),
        od.neg().add(oe.neg().neg()),
        od.neg().add(oe),
    );
    // od.neg() + oe ≡ oe + od.neg() = eo
    T::axiom_add_commutative(od.neg(), oe);
    T::axiom_eqv_transitive(denom.neg(), od.neg().add(oe), eo);
    // Symmetric: eo ≡ denom.neg()
    T::axiom_eqv_symmetric(denom.neg(), eo);

    // Step 2: t * eo ≡ t * denom.neg()
    ring_lemmas::lemma_mul_congruence_right::<T>(t, eo, denom.neg());

    // Step 3: t * denom.neg() ≡ (t * denom).neg()
    ring_lemmas::lemma_mul_neg_right::<T>(t, denom);
    T::axiom_eqv_transitive(t.mul(eo), t.mul(denom.neg()), t.mul(denom).neg());

    // Step 4: t * denom = (od/denom) * denom ≡ od
    field_lemmas::lemma_div_mul_cancel::<T>(od, denom);

    // Step 5: (t * denom).neg() ≡ od.neg()
    T::axiom_neg_congruence(t.mul(denom), od);
    T::axiom_eqv_transitive(t.mul(eo), t.mul(denom).neg(), od.neg());

    // Step 6: od + t*eo ≡ od + od.neg()
    additive_group_lemmas::lemma_add_congruence_right::<T>(od, t.mul(eo), od.neg());

    // Step 7: od + od.neg() ≡ 0
    T::axiom_add_inverse_right(od);
    T::axiom_eqv_transitive(od.add(t.mul(eo)), od.add(od.neg()), T::zero());
}

/// The intersection point lies on the plane: orient3d(a,b,c,p) ≡ 0.
pub proof fn lemma_intersection_point_on_plane<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures ({
        let p = segment_plane_intersection_point(d, e, a, b, c);
        orient3d(a, b, c, p).eqv(T::zero())
    }),
{
    let od = orient3d(a, b, c, d);
    let oe = orient3d(a, b, c, e);
    let denom = od.add(oe.neg());
    let t = od.div(denom);
    let dir = sub3(e, d);
    let p = segment_plane_intersection_point(d, e, a, b, c);

    let u = sub3(b, a);
    let v = sub3(c, a);
    let w = sub3(d, a);
    let z = sub3(e, a);

    lemma_crossing_denominator_nonzero::<T>(d, e, a, b, c);

    // === Part 1: orient3d(a,b,c,p) ≡ od + t*triple(u,v,dir) ===

    // A: sub3(p, a) ≡ w + scale(t, dir)
    lemma_sub3_add_vec3::<T>(d, scale(t, dir), a);

    // B: congruence in 3rd arg
    verus_linalg::vec3::ops::lemma_triple_congruence_third::<T>(u, v, sub3(p, a), w.add(scale(t, dir)));

    // C: linearity in 3rd arg
    verus_linalg::vec3::ops::lemma_triple_linear_third::<T>(u, v, w, scale(t, dir));

    // orient3d(a,b,c,p) ≡ triple(u,v,w) + triple(u,v,scale(t,dir))
    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, sub3(p, a)),
        verus_linalg::vec3::ops::triple(u, v, w.add(scale(t, dir))),
        verus_linalg::vec3::ops::triple(u, v, w).add(
            verus_linalg::vec3::ops::triple(u, v, scale(t, dir))
        ),
    );

    // D: scale extraction
    verus_linalg::vec3::ops::lemma_triple_scale_third::<T>(t, u, v, dir);

    // triple(u,v,w) + triple(u,v,scale(t,dir)) ≡ od + t*triple(u,v,dir)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od,
        verus_linalg::vec3::ops::triple(u, v, scale(t, dir)),
        t.mul(verus_linalg::vec3::ops::triple(u, v, dir)),
    );

    // orient3d(a,b,c,p) ≡ od + t*triple(u,v,dir)
    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, sub3(p, a)),
        od.add(verus_linalg::vec3::ops::triple(u, v, scale(t, dir))),
        od.add(t.mul(verus_linalg::vec3::ops::triple(u, v, dir))),
    );

    // === Part 2: triple(u,v,dir) ≡ oe + od.neg() ===

    // E: sub3(e,d) ≡ sub3(e,a).sub(sub3(d,a)) = z.sub(w)
    lemma_sub3_triangle::<T>(e, d, a);

    // F: z.sub(w) ≡ z.add(w.neg()) via Vec3 axiom
    Vec3::<T>::axiom_sub_is_add_neg(z, w);

    // G: dir ≡ z.add(w.neg())
    T::axiom_eqv_transitive(
        dir.x, z.sub(w).x, z.add(w.neg()).x,
    );
    T::axiom_eqv_transitive(
        dir.y, z.sub(w).y, z.add(w.neg()).y,
    );
    T::axiom_eqv_transitive(
        dir.z, z.sub(w).z, z.add(w.neg()).z,
    );

    // H: congruence in 3rd arg
    verus_linalg::vec3::ops::lemma_triple_congruence_third::<T>(u, v, dir, z.add(w.neg()));

    // I: linearity
    verus_linalg::vec3::ops::lemma_triple_linear_third::<T>(u, v, z, w.neg());

    // triple(u,v,dir) ≡ triple(u,v,z) + triple(u,v,w.neg())
    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, dir),
        verus_linalg::vec3::ops::triple(u, v, z.add(w.neg())),
        verus_linalg::vec3::ops::triple(u, v, z).add(
            verus_linalg::vec3::ops::triple(u, v, w.neg())
        ),
    );

    // J: neg in 3rd arg
    verus_linalg::vec3::ops::lemma_triple_neg_third::<T>(u, v, w);

    // triple(u,v,z) + triple(u,v,w.neg()) ≡ oe + od.neg()
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oe,
        verus_linalg::vec3::ops::triple(u, v, w.neg()),
        od.neg(),
    );

    // triple(u,v,dir) ≡ oe + od.neg()
    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, dir),
        oe.add(verus_linalg::vec3::ops::triple(u, v, w.neg())),
        oe.add(od.neg()),
    );

    // === Part 3: combine and cancel ===

    // t * triple(u,v,dir) ≡ t * (oe + od.neg())
    ring_lemmas::lemma_mul_congruence_right::<T>(
        t,
        verus_linalg::vec3::ops::triple(u, v, dir),
        oe.add(od.neg()),
    );

    // od + t*triple(u,v,dir) ≡ od + t*(oe + od.neg())
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od,
        t.mul(verus_linalg::vec3::ops::triple(u, v, dir)),
        t.mul(oe.add(od.neg())),
    );

    // orient3d(a,b,c,p) ≡ od + t*(oe + od.neg())
    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, sub3(p, a)),
        od.add(t.mul(verus_linalg::vec3::ops::triple(u, v, dir))),
        od.add(t.mul(oe.add(od.neg()))),
    );

    // Algebraic cancellation: od + t*(oe + od.neg()) ≡ 0
    lemma_orient_cancel::<T>(od, oe);

    T::axiom_eqv_transitive(
        verus_linalg::vec3::ops::triple(u, v, sub3(p, a)),
        od.add(t.mul(oe.add(od.neg()))),
        T::zero(),
    );
}

// =========================================================================
// Combined lemma: segment-triangle intersection point properties
// =========================================================================

/// When a segment-triangle intersection exists, the intersection point:
/// - lies on the plane (orient3d ≡ 0)
/// - is strictly between the segment endpoints (0 < t < 1)
/// - is the affine combination (1-t)*d + t*e
/// - is inside the triangle
pub proof fn lemma_segment_triangle_intersection_properties<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_triangle_intersects_strict(d, e, a, b, c),
    ensures ({
        let p = segment_plane_intersection_point(d, e, a, b, c);
        let t = segment_plane_intersection_parameter(d, e, a, b, c);
        let s = T::one().sub(t);
        // On plane
        &&& orient3d(a, b, c, p).eqv(T::zero())
        // Strictly between d and e
        &&& T::zero().lt(t) && t.lt(T::one())
        // Affine combination
        &&& p.x.eqv(s.mul(d.x).add(t.mul(e.x)))
        &&& p.y.eqv(s.mul(d.y).add(t.mul(e.y)))
        &&& p.z.eqv(s.mul(d.z).add(t.mul(e.z)))
        // In triangle
        &&& point_in_triangle_on_plane(p, a, b, c)
    }),
{
    let t = segment_plane_intersection_parameter(d, e, a, b, c);
    lemma_intersection_point_on_plane::<T>(d, e, a, b, c);
    lemma_crossing_parameter_bounds::<T>(d, e, a, b, c);
    lemma_intersection_affine_combination::<T>(d, e, t);
}

// =========================================================================
// Affine combination form: d + t*(e - d) ≡ (1-t)*d + t*e
// =========================================================================

/// Scalar identity: a + t*(b - a) ≡ (1-t)*a + t*b.
pub proof fn lemma_affine_scalar<T: Ring>(a: T, b: T, t: T)
    ensures
        a.add(t.mul(b.sub(a))).eqv(T::one().sub(t).mul(a).add(t.mul(b))),
{
    let ta = t.mul(a);
    let tb = t.mul(b);
    let common = a.add(tb.sub(ta));

    // === LHS ≡ common ===
    // t*(b-a) ≡ t*b - t*a
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(t, b, a);
    // a + t*(b-a) ≡ a + (t*b - t*a)
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, t.mul(b.sub(a)), tb.sub(ta));

    // === RHS ≡ common ===
    // (1-t)*a ≡ 1*a - t*a
    ring_lemmas::lemma_sub_mul_right::<T>(T::one(), t, a);
    // 1*a ≡ a
    ring_lemmas::lemma_mul_one_left::<T>(a);
    // 1*a - t*a ≡ a - t*a
    T::axiom_eqv_reflexive(ta);
    additive_group_lemmas::lemma_sub_congruence::<T>(T::one().mul(a), a, ta, ta);
    // (1-t)*a ≡ a - t*a
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a), T::one().mul(a).sub(ta), a.sub(ta),
    );
    // RHS = (1-t)*a + t*b ≡ (a - t*a) + t*b
    T::axiom_add_congruence_left(T::one().sub(t).mul(a), a.sub(ta), tb);

    // (a - t*a) + t*b ≡ a + (t*b - t*a) = common
    // Expand sub: a.sub(ta) ≡ a.add(ta.neg())
    T::axiom_sub_is_add_neg(a, ta);
    T::axiom_add_congruence_left(a.sub(ta), a.add(ta.neg()), tb);
    // (a + (-ta)) + tb ≡ a + ((-ta) + tb)
    T::axiom_add_associative(a, ta.neg(), tb);
    T::axiom_eqv_transitive(
        a.sub(ta).add(tb), a.add(ta.neg()).add(tb), a.add(ta.neg().add(tb)),
    );
    // (-ta) + tb ≡ tb + (-ta)
    T::axiom_add_commutative(ta.neg(), tb);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, ta.neg().add(tb), tb.add(ta.neg()),
    );
    T::axiom_eqv_transitive(
        a.sub(ta).add(tb), a.add(ta.neg().add(tb)), a.add(tb.add(ta.neg())),
    );
    // tb + (-ta) ≡ tb - ta
    T::axiom_sub_is_add_neg(tb, ta);
    T::axiom_eqv_symmetric(tb.sub(ta), tb.add(ta.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, tb.add(ta.neg()), tb.sub(ta),
    );
    T::axiom_eqv_transitive(
        a.sub(ta).add(tb), a.add(tb.add(ta.neg())), common,
    );

    // Chain: RHS ≡ a.sub(ta).add(tb) ≡ common
    let rhs = T::one().sub(t).mul(a).add(tb);
    T::axiom_eqv_transitive(rhs, a.sub(ta).add(tb), common);

    // Final: LHS ≡ common, common ≡ RHS (symmetric), so LHS ≡ RHS
    T::axiom_eqv_symmetric(rhs, common);
    let lhs = a.add(t.mul(b.sub(a)));
    T::axiom_eqv_transitive(lhs, common, rhs);
}

/// The intersection point p = d + t*(e - d) equals (1-t)*d + t*e
/// coordinate-wise (affine combination form).
pub proof fn lemma_intersection_affine_combination<T: Ring>(
    d: Point3<T>, e: Point3<T>, t: T,
)
    ensures ({
        let dir = sub3(e, d);
        let p = add_vec3(d, scale(t, dir));
        let s = T::one().sub(t);
        &&& p.x.eqv(s.mul(d.x).add(t.mul(e.x)))
        &&& p.y.eqv(s.mul(d.y).add(t.mul(e.y)))
        &&& p.z.eqv(s.mul(d.z).add(t.mul(e.z)))
    }),
{
    lemma_affine_scalar::<T>(d.x, e.x, t);
    lemma_affine_scalar::<T>(d.y, e.y, t);
    lemma_affine_scalar::<T>(d.z, e.z, t);
}

} // verus!
