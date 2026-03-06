use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{scale, triple};
use verus_linalg::vec3::ops::{
    lemma_triple_scale_third,
    lemma_triple_congruence_third,
};
use crate::point3::*;
use crate::point2::Point2;
use crate::orient2d::{orient2d};
use crate::orient3d::*;
use crate::orientation_sign::*;
use crate::sidedness::*;
use crate::intersection3d::*;
use crate::barycentric::*;

verus! {

// =========================================================================
// Triangle-triangle intersection (3D, strict / non-coplanar)
// =========================================================================

/// All three vertices p, q, r are strictly above the plane (a, b, c).
pub open spec fn all_above_plane<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    point_above_plane(p, a, b, c)
    && point_above_plane(q, a, b, c)
    && point_above_plane(r, a, b, c)
}

/// All three vertices p, q, r are strictly below the plane (a, b, c).
pub open spec fn all_below_plane<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    point_below_plane(p, a, b, c)
    && point_below_plane(q, a, b, c)
    && point_below_plane(r, a, b, c)
}

/// All three vertices p, q, r are on the same strict side of the plane (a, b, c).
pub open spec fn all_same_strict_side<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    all_above_plane(p, q, r, a, b, c) || all_below_plane(p, q, r, a, b, c)
}

/// Two triangles T1 = (a1, b1, c1) and T2 = (a2, b2, c2) strictly intersect:
/// some edge of one triangle passes strictly through the other triangle's interior.
///
/// "Strict" means: endpoints of each tested segment are on opposite sides of the
/// other triangle's plane (neither endpoint lies on the plane). This excludes
/// coplanar configurations, vertex-on-face touching, and edge-on-edge touching.
pub open spec fn triangles_intersect_strict<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
) -> bool {
    // Edges of T1 through T2
    segment_triangle_intersects_strict(a1, b1, a2, b2, c2)
    || segment_triangle_intersects_strict(b1, c1, a2, b2, c2)
    || segment_triangle_intersects_strict(c1, a1, a2, b2, c2)
    // Edges of T2 through T1
    || segment_triangle_intersects_strict(a2, b2, a1, b1, c1)
    || segment_triangle_intersects_strict(b2, c2, a1, b1, c1)
    || segment_triangle_intersects_strict(c2, a2, a1, b1, c1)
}

// =========================================================================
// Lemma: plane separation kills edge crossing
// =========================================================================

/// If both endpoints of a segment are strictly above a plane, the segment
/// does not strictly cross that plane.
pub proof fn lemma_both_above_no_crossing<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        point_above_plane(d, a, b, c),
        point_above_plane(e, a, b, c),
    ensures
        !segment_crosses_plane_strict(d, e, a, b, c),
{
    lemma_point_plane_trichotomy::<T>(d, a, b, c);
    lemma_point_plane_trichotomy::<T>(e, a, b, c);
}

/// If both endpoints of a segment are strictly below a plane, the segment
/// does not strictly cross that plane.
pub proof fn lemma_both_below_no_crossing<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        point_below_plane(d, a, b, c),
        point_below_plane(e, a, b, c),
    ensures
        !segment_crosses_plane_strict(d, e, a, b, c),
{
    lemma_point_plane_trichotomy::<T>(d, a, b, c);
    lemma_point_plane_trichotomy::<T>(e, a, b, c);
}

// =========================================================================
// Lemma: all-same-side → no edge of that triangle crosses the plane
// =========================================================================

/// If all vertices of triangle (p, q, r) are on the same strict side of
/// the plane (a, b, c), then no edge of (p, q, r) strictly crosses that plane.
pub proof fn lemma_same_side_no_edge_crossing<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        all_same_strict_side(p, q, r, a, b, c),
    ensures
        !segment_crosses_plane_strict(p, q, a, b, c),
        !segment_crosses_plane_strict(q, r, a, b, c),
        !segment_crosses_plane_strict(r, p, a, b, c),
{
    if all_above_plane(p, q, r, a, b, c) {
        lemma_both_above_no_crossing::<T>(p, q, a, b, c);
        lemma_both_above_no_crossing::<T>(q, r, a, b, c);
        lemma_both_above_no_crossing::<T>(r, p, a, b, c);
    } else {
        lemma_both_below_no_crossing::<T>(p, q, a, b, c);
        lemma_both_below_no_crossing::<T>(q, r, a, b, c);
        lemma_both_below_no_crossing::<T>(r, p, a, b, c);
    }
}

// =========================================================================
// Lemma: one-sided separation kills that triangle's edge tests
// =========================================================================

/// If all vertices of T1 are on the same strict side of plane(T2), then
/// no edge of T1 can pass strictly through T2.
pub proof fn lemma_t1_separated_no_t1_edges<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        all_same_strict_side(a1, b1, c1, a2, b2, c2),
    ensures
        !segment_triangle_intersects_strict(a1, b1, a2, b2, c2),
        !segment_triangle_intersects_strict(b1, c1, a2, b2, c2),
        !segment_triangle_intersects_strict(c1, a1, a2, b2, c2),
{
    lemma_same_side_no_edge_crossing::<T>(a1, b1, c1, a2, b2, c2);
}

/// Symmetric: if all vertices of T2 are on the same strict side of plane(T1),
/// then no edge of T2 can pass strictly through T1.
pub proof fn lemma_t2_separated_no_t2_edges<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        all_same_strict_side(a2, b2, c2, a1, b1, c1),
    ensures
        !segment_triangle_intersects_strict(a2, b2, a1, b1, c1),
        !segment_triangle_intersects_strict(b2, c2, a1, b1, c1),
        !segment_triangle_intersects_strict(c2, a2, a1, b1, c1),
{
    lemma_same_side_no_edge_crossing::<T>(a2, b2, c2, a1, b1, c1);
}

// =========================================================================
// Lemma: BOTH sides separated → no intersection
// =========================================================================

/// If T1's vertices are all on the same strict side of plane(T2), AND
/// T2's vertices are all on the same strict side of plane(T1), then the
/// triangles do not strictly intersect.
///
/// This is the common case in mesh processing: most triangle pairs are
/// separated by at least one of the two half-space tests.
pub proof fn lemma_both_separated_no_intersection<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        all_same_strict_side(a1, b1, c1, a2, b2, c2),
        all_same_strict_side(a2, b2, c2, a1, b1, c1),
    ensures
        !triangles_intersect_strict(a1, b1, c1, a2, b2, c2),
{
    lemma_t1_separated_no_t1_edges::<T>(a1, b1, c1, a2, b2, c2);
    lemma_t2_separated_no_t2_edges::<T>(a1, b1, c1, a2, b2, c2);
}

// =========================================================================
// Lemma: symmetry
// =========================================================================

/// Triangle-triangle strict intersection is symmetric.
pub proof fn lemma_triangles_intersect_strict_symmetric<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    ensures
        triangles_intersect_strict(a1, b1, c1, a2, b2, c2)
            == triangles_intersect_strict(a2, b2, c2, a1, b1, c1),
{
    // Both sides are the same 6 disjuncts, just reordered.
    // T1 edges through T2 become the last 3 disjuncts of the swapped version,
    // T2 edges through T1 become the first 3. OR is commutative.
}

// =========================================================================
// Helper: orient3d zero on segment between coplanar points
// =========================================================================

/// If two points d, e both satisfy orient3d(a,b,c,_) ≡ 0, then any point
/// on the line through d,e also satisfies orient3d ≡ 0.
pub proof fn lemma_orient3d_zero_on_coplanar_segment<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    d: Point3<T>, e: Point3<T>,
    t: T,
)
    requires
        orient3d(a, b, c, d).eqv(T::zero()),
        orient3d(a, b, c, e).eqv(T::zero()),
    ensures
        orient3d(a, b, c, add_vec3(d, scale(t, sub3(e, d)))).eqv(T::zero()),
{
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let ed = sub3(e, d);
    let w = scale(t, ed);

    // (1) orient3d(a,b,c, d+w) ≡ orient3d(a,b,c,d) + triple(ba, ca, w)
    lemma_orient3d_linear_last::<T>(a, b, c, d, w);

    // (2) triple(ba, ca, scale(t, ed)) ≡ t * triple(ba, ca, ed)
    lemma_triple_scale_third::<T>(t, ba, ca, ed);

    // (3) Derive triple(ba, ca, ed) ≡ 0:
    //     shift_endpoint: orient3d(a,b,c, add_vec3(d, ed)) ≡ orient3d(a,b,c,e)
    //     linear_last:    orient3d(a,b,c, add_vec3(d, ed)) ≡ orient3d(a,b,c,d) + triple(ba,ca,ed)
    //     So: orient3d(a,b,c,d) + triple(ba,ca,ed) ≡ orient3d(a,b,c,e) ≡ 0
    lemma_orient3d_shift_endpoint::<T>(a, b, c, d, e);
    lemma_orient3d_linear_last::<T>(a, b, c, d, ed);
    // orient3d(a,b,c,d) + triple(ba,ca,ed) ≡ orient3d(a,b,c,e)
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, add_vec3(d, ed)),
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        orient3d(a, b, c, add_vec3(d, ed)),
        orient3d(a, b, c, e),
    );
    // orient3d(a,b,c,d) + triple(...) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        orient3d(a, b, c, e),
        T::zero(),
    );
    // Substitute orient3d(a,b,c,d) ≡ 0: orient3d(..,d)+triple ≡ 0+triple
    T::axiom_add_congruence_left(
        orient3d(a, b, c, d), T::zero(), triple(ba, ca, ed),
    );
    // orient3d(..,d)+triple ≡ 0+triple [above gives this direction]
    // We already have orient3d(..,d)+triple ≡ 0, so 0+triple ≡ 0
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        T::zero().add(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        T::zero().add(triple(ba, ca, ed)),
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        T::zero(),
    );
    // 0 + triple(...) ≡ triple(...)
    additive_group_lemmas::lemma_add_zero_left::<T>(triple(ba, ca, ed));
    // triple(ba, ca, ed) ≡ 0
    T::axiom_eqv_symmetric(T::zero().add(triple(ba, ca, ed)), triple(ba, ca, ed));
    T::axiom_eqv_transitive(
        triple(ba, ca, ed), T::zero().add(triple(ba, ca, ed)), T::zero(),
    );

    // (4) t * triple(ba,ca,ed) ≡ t * 0 ≡ 0
    T::axiom_mul_commutative(t, triple(ba, ca, ed));
    T::axiom_mul_congruence_left(triple(ba, ca, ed), T::zero(), t);
    T::axiom_eqv_transitive(
        t.mul(triple(ba, ca, ed)), triple(ba, ca, ed).mul(t), T::zero().mul(t),
    );
    ring_lemmas::lemma_mul_zero_left::<T>(t);
    T::axiom_eqv_transitive(
        t.mul(triple(ba, ca, ed)), T::zero().mul(t), T::zero(),
    );

    // (5) triple(ba, ca, w) ≡ t * triple(ba, ca, ed) ≡ 0
    T::axiom_eqv_transitive(
        triple(ba, ca, w), t.mul(triple(ba, ca, ed)), T::zero(),
    );

    // (6) orient3d(a,b,c,d) + triple(ba,ca,w) ≡ 0 + 0 ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        orient3d(a, b, c, d), T::zero(),
        triple(ba, ca, w), T::zero(),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d).add(triple(ba, ca, w)),
        T::zero().add(T::zero()),
        T::zero(),
    );

    // (7) Final chain: orient3d(a,b,c, d+w) ≡ orient3d(...,d) + triple(...) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, add_vec3(d, w)),
        orient3d(a, b, c, d).add(triple(ba, ca, w)),
        T::zero(),
    );
}

// =========================================================================
// Helper: triple = orient3d difference
// =========================================================================

/// triple(sub3(y,x), sub3(z,x), sub3(b,a)) ≡ orient3d(x,y,z,b) - orient3d(x,y,z,a).
pub proof fn lemma_triple_is_orient_diff<T: Ring>(
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    a: Point3<T>, b: Point3<T>,
)
    ensures
        triple(sub3(y, x), sub3(z, x), sub3(b, a)).eqv(
            orient3d(x, y, z, b).sub(orient3d(x, y, z, a))
        ),
{
    let yx = sub3(y, x);
    let zx = sub3(z, x);
    let ba = sub3(b, a);
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let tb = triple(yx, zx, ba);

    // orient3d(x,y,z, add_vec3(a, ba)) ≡ oa + tb  [linear_last]
    lemma_orient3d_linear_last::<T>(x, y, z, a, ba);
    // orient3d(x,y,z, add_vec3(a, ba)) ≡ ob  [shift_endpoint]
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, b);
    // oa + tb ≡ ob  [combine]
    T::axiom_eqv_symmetric(
        orient3d(x, y, z, add_vec3(a, ba)),
        oa.add(tb),
    );
    T::axiom_eqv_transitive(oa.add(tb), orient3d(x, y, z, add_vec3(a, ba)), ob);

    // oa + (ob - oa) ≡ ob  [sub_then_add_cancel + commutativity]
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(ob, oa);
    T::axiom_add_commutative(oa, ob.sub(oa));
    T::axiom_eqv_transitive(oa.add(ob.sub(oa)), ob.sub(oa).add(oa), ob);

    // Left cancel: oa + tb ≡ ob ≡ oa + (ob - oa), so tb ≡ ob - oa.
    T::axiom_eqv_symmetric(oa.add(ob.sub(oa)), ob);
    T::axiom_eqv_transitive(oa.add(tb), ob, oa.add(ob.sub(oa)));
    additive_group_lemmas::lemma_add_left_cancel::<T>(tb, ob.sub(oa), oa);
}

// =========================================================================
// Helper: a + (x - y) ≡ (a - y) + x
// =========================================================================

/// Rearrangement: a + (x - y) ≡ (a - y) + x.
pub proof fn lemma_add_sub_rearrange<T: Ring>(a: T, x: T, y: T)
    ensures
        a.add(x.sub(y)).eqv(a.sub(y).add(x)),
{
    // a + (x - y) ≡ a + (x + (-y))  [sub_is_add_neg]
    T::axiom_sub_is_add_neg(x, y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, x.sub(y), x.add(y.neg()));
    // ≡ (a + x) + (-y)  [assoc, symmetric]
    T::axiom_add_associative(a, x, y.neg());
    T::axiom_eqv_symmetric(a.add(x).add(y.neg()), a.add(x.add(y.neg())));
    T::axiom_eqv_transitive(a.add(x.sub(y)), a.add(x.add(y.neg())), a.add(x).add(y.neg()));
    // ≡ (x + a) + (-y)  [commutative on inner]
    T::axiom_add_commutative(a, x);
    T::axiom_add_congruence_left(a.add(x), x.add(a), y.neg());
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), a.add(x).add(y.neg()), x.add(a).add(y.neg()),
    );
    // ≡ x + (a + (-y))  [assoc]
    T::axiom_add_associative(x, a, y.neg());
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), x.add(a).add(y.neg()), x.add(a.add(y.neg())),
    );
    // ≡ x + (a - y)  [reverse sub_is_add_neg]
    T::axiom_sub_is_add_neg(a, y);
    T::axiom_eqv_symmetric(a.sub(y), a.add(y.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(x, a.add(y.neg()), a.sub(y));
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), x.add(a.add(y.neg())), x.add(a.sub(y)),
    );
    // ≡ (a - y) + x  [commutative]
    T::axiom_add_commutative(x, a.sub(y));
    T::axiom_eqv_transitive(a.add(x.sub(y)), x.add(a.sub(y)), a.sub(y).add(x));
}

// =========================================================================
// Helper: factoring a - t*a ≡ (1 - t) * a
// =========================================================================

/// a - t*a ≡ (1 - t) * a.
pub proof fn lemma_factor_out<T: Ring>(a: T, t: T)
    ensures
        a.sub(t.mul(a)).eqv(T::one().sub(t).mul(a)),
{
    // (1-t)*a ≡ a*(1-t)  [commutative]
    T::axiom_mul_commutative(T::one().sub(t), a);
    // a*(1-t) ≡ a*1 - a*t  [distributes_over_sub]
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(a, T::one(), t);
    // Chain: (1-t)*a ≡ a*1 - a*t
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a), a.mul(T::one().sub(t)), a.mul(T::one()).sub(a.mul(t)),
    );

    // Now show a*1 - a*t ≡ a - t*a:
    // a*1 ≡ a
    T::axiom_mul_one_right(a);
    // a*t ≡ t*a
    T::axiom_mul_commutative(a, t);
    // a*1 - a*t ≡ a - t*a  by sub congruence (a.sub(b) respects eqv)
    T::axiom_sub_is_add_neg(a.mul(T::one()), a.mul(t));
    T::axiom_sub_is_add_neg(a, t.mul(a));
    T::axiom_neg_congruence(a.mul(t), t.mul(a));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.mul(T::one()), a,
        a.mul(t).neg(), t.mul(a).neg(),
    );
    // a.mul(T::one()).add(a.mul(t).neg()) ≡ a.add(t.mul(a).neg())
    // Convert from add_neg form to sub form:
    T::axiom_eqv_symmetric(a.mul(T::one()).sub(a.mul(t)), a.mul(T::one()).add(a.mul(t).neg()));
    T::axiom_eqv_transitive(
        a.mul(T::one()).sub(a.mul(t)),
        a.mul(T::one()).add(a.mul(t).neg()),
        a.add(t.mul(a).neg()),
    );
    T::axiom_eqv_symmetric(a.sub(t.mul(a)), a.add(t.mul(a).neg()));
    T::axiom_eqv_transitive(
        a.mul(T::one()).sub(a.mul(t)),
        a.add(t.mul(a).neg()),
        a.sub(t.mul(a)),
    );

    // Chain: (1-t)*a ≡ a*1 - a*t ≡ a - t*a
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a),
        a.mul(T::one()).sub(a.mul(t)),
        a.sub(t.mul(a)),
    );
    // Symmetric: a - t*a ≡ (1-t)*a
    T::axiom_eqv_symmetric(T::one().sub(t).mul(a), a.sub(t.mul(a)));
}

// =========================================================================
// Helper: orient3d positive on affine combination
// =========================================================================

/// If orient3d(x,y,z,_) is strictly positive at all three vertices a, b, c,
/// and α ≥ 0, β ≥ 0, 1-α-β ≥ 0, then orient3d is positive at the
/// affine combination a + α*(b-a) + β*(c-a).
pub proof fn lemma_orient3d_affine_positive<T: OrderedField>(
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    alpha: T, beta: T,
)
    requires
        T::zero().lt(orient3d(x, y, z, a)),
        T::zero().lt(orient3d(x, y, z, b)),
        T::zero().lt(orient3d(x, y, z, c)),
        T::zero().le(alpha),
        T::zero().le(beta),
        T::zero().le(T::one().sub(alpha).sub(beta)),
    ensures
        T::zero().lt(
            orient3d(x, y, z, add_vec3(a, scale(alpha, sub3(b, a)).add(scale(beta, sub3(c, a)))))
        ),
{
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let oc = orient3d(x, y, z, c);
    let u = T::one().sub(alpha).sub(beta);
    let p_orient = orient3d(x, y, z,
        add_vec3(a, scale(alpha, sub3(b, a)).add(scale(beta, sub3(c, a)))));
    let weighted = u.mul(oa).add(alpha.mul(ob)).add(beta.mul(oc));

    // --- Algebraic identity: orient3d(p) ≡ u*oa + alpha*ob + beta*oc ---
    // Via orient3d_affine_combination + triple_is_orient_diff + rearrangement.
    lemma_orient3d_weighted_form::<T>(x, y, z, a, b, c, alpha, beta);

    // --- Positivity: u*oa + alpha*ob + beta*oc > 0 ---
    // 0 ≤ oa, ob, oc from 0 < ...
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oa);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), ob);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oc);
    // Each product ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(u, oa);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(alpha, ob);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(beta, oc);

    // Case split: at least one weight > 0.
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), u);
    if T::zero().lt(u) {
        ordered_field_lemmas::lemma_mul_pos_pos::<T>(u, oa);
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(u.mul(oa), alpha.mul(ob));
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
            u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
        );
    } else {
        // u ≡ 0.
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), alpha);
        if T::zero().lt(alpha) {
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(alpha, ob);
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(u.mul(oa), alpha.mul(ob));
            ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
                u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
            );
        } else {
            // alpha ≡ 0 and u ≡ 0 → beta > 0 (since if beta ≡ 0 too, then
            // u = 1-0-0 = 1, but u ≡ 0 contradicts 0 < 1).
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), beta);
            if T::zero().eqv(beta) {
                // Contradiction: 0≡u, 0≡alpha, 0≡beta → u≡1, but 0≡u and 0<1.
                T::axiom_eqv_reflexive(u);
                lemma_all_zero_contradiction::<T>(alpha, beta, u);
            }
            // Now: !T::zero().eqv(beta) + T::zero().le(beta) → T::zero().lt(beta)
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(beta, oc);
            // Need: u*oa + alpha*ob ≥ 0 (both nonneg from lines above)
            ordered_ring_lemmas::lemma_le_add_both::<T>(
                T::zero(), u.mul(oa), T::zero(), alpha.mul(ob),
            );
            T::axiom_add_zero_right(T::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().add(T::zero()), T::zero(), u.mul(oa).add(alpha.mul(ob)),
            );
            // Now: 0 <= u*oa + alpha*ob and 0 < beta*oc → 0 < sum
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(
                u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
            );
        }
    }

    // Transfer: 0 < weighted and p_orient ≡ weighted → 0 < p_orient
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_symmetric(p_orient, weighted);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), weighted, p_orient,
    );
}

// =========================================================================
// Helper: algebraic identity for weighted form
// =========================================================================

/// orient3d(x,y,z, a + alpha*(b-a) + beta*(c-a))
///   ≡ (1-alpha-beta)*orient3d(x,y,z,a) + alpha*orient3d(x,y,z,b) + beta*orient3d(x,y,z,c)
pub proof fn lemma_orient3d_weighted_form<T: OrderedField>(
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    alpha: T, beta: T,
)
    ensures
        orient3d(x, y, z, add_vec3(a, scale(alpha, sub3(b, a)).add(scale(beta, sub3(c, a)))))
            .eqv(
                T::one().sub(alpha).sub(beta).mul(orient3d(x, y, z, a))
                    .add(alpha.mul(orient3d(x, y, z, b)))
                    .add(beta.mul(orient3d(x, y, z, c)))
            ),
{
    assume(false); // proof debt: algebraic identity via affine_combination + rearrangement
}

// =========================================================================
// Helper: contradiction when all weights are zero but should sum to 1
// =========================================================================

/// If alpha ≡ 0, beta ≡ 0, and u = 1-alpha-beta, then u cannot be ≡ 0
/// (because that would require 1 ≡ 0, contradicting 0 < 1).
pub proof fn lemma_all_zero_contradiction<T: OrderedField>(alpha: T, beta: T, u: T)
    requires
        T::zero().eqv(alpha),
        T::zero().eqv(beta),
        T::zero().eqv(u),
        u.eqv(T::one().sub(alpha).sub(beta)),
    ensures
        false,
{
    // Step 1: alpha ≡ 0, beta ≡ 0 (symmetric of given)
    T::axiom_eqv_symmetric(T::zero(), alpha);
    T::axiom_eqv_symmetric(T::zero(), beta);
    // Step 2: 1 - alpha ≡ 1 - 0
    T::axiom_eqv_reflexive(T::one());
    additive_group_lemmas::lemma_sub_congruence::<T>(T::one(), T::one(), alpha, T::zero());
    // Step 3: 1 - 0 ≡ 1 (via sub_is_add_neg + neg_zero + add_zero_right)
    T::axiom_sub_is_add_neg(T::one(), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(T::one(), T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::zero()), T::one().add(T::zero().neg()), T::one().add(T::zero()));
    T::axiom_add_zero_right(T::one());
    T::axiom_eqv_transitive(T::one().sub(T::zero()), T::one().add(T::zero()), T::one());
    // Step 4: 1 - alpha ≡ 1 (transitive)
    T::axiom_eqv_transitive(T::one().sub(alpha), T::one().sub(T::zero()), T::one());
    // Step 5: (1-alpha) - beta ≡ 1 - 0
    T::axiom_eqv_reflexive(T::one().sub(alpha));
    additive_group_lemmas::lemma_sub_congruence::<T>(T::one().sub(alpha), T::one(), beta, T::zero());
    // Step 6: 1 - alpha - beta ≡ 1 (transitive through 1 - 0)
    T::axiom_eqv_transitive(T::one().sub(alpha).sub(beta), T::one().sub(T::zero()), T::one());
    // Step 7: u ≡ 1 (from u ≡ 1-alpha-beta ≡ 1)
    T::axiom_eqv_transitive(u, T::one().sub(alpha).sub(beta), T::one());
    // Step 8: 0 ≡ 1 (from 0 ≡ u ≡ 1)
    T::axiom_eqv_transitive(T::zero(), u, T::one());
    // Step 9: But 0 < 1 implies !(0 ≡ 1). Contradiction.
    ordered_ring_lemmas::lemma_zero_lt_one::<T>();
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), T::one());
}

// =========================================================================
// Helper: inside triangle + all above → orient3d positive
// =========================================================================

/// If point_in_triangle_on_plane(p, a, b, c) holds, orient3d(a,b,c,p) ≡ 0
/// (p is on the plane of the triangle), and orient3d(x,y,z,_) is strictly
/// positive at all three vertices a, b, c, then orient3d(x,y,z,p) > 0.
///
/// The proof connects the 2D inside-triangle condition to the 3D affine
/// coordinates via projection injectivity, then applies
/// lemma_orient3d_affine_positive.
///
/// Proof debt: 2D barycentric coordinates → 3D affine combination
/// via projection injectivity.
pub proof fn lemma_inside_triangle_orient3d_positive<T: OrderedField>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
)
    requires
        point_in_triangle_on_plane(p, a, b, c),
        orient3d(a, b, c, p).eqv(T::zero()),
        T::zero().lt(orient3d(x, y, z, a)),
        T::zero().lt(orient3d(x, y, z, b)),
        T::zero().lt(orient3d(x, y, z, c)),
    ensures
        T::zero().lt(orient3d(x, y, z, p)),
{
    // The key argument:
    // 1. p is on the plane of (a,b,c), so there exist unique α, β such that
    //    p = a + α*(b-a) + β*(c-a)
    // 2. The 2D barycentric coordinates from point_in_triangle_on_plane give
    //    the same α, β (by projection injectivity).
    // 3. point_in_triangle_on_plane ensures the orient2d signs are consistent,
    //    giving α ≥ 0, β ≥ 0, 1-α-β ≥ 0.
    // 4. lemma_orient3d_affine_positive gives orient3d(x,y,z,p) > 0.
    assume(false);  // proof debt: barycentric + projection injectivity
}

// =========================================================================
// Lemma: single-sided separation → no T2 edge through T1
// =========================================================================

/// If a T2 edge (d,e) has orient3d(a2,b2,c2,d) ≡ 0 and orient3d(a2,b2,c2,e) ≡ 0
/// (i.e., d,e are coplanar with T2), and all T1 vertices are strictly above
/// the plane of T2, then the segment (d,e) does not strictly intersect T1.
pub proof fn lemma_coplanar_edge_no_intersection<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        orient3d(a2, b2, c2, d).eqv(T::zero()),
        orient3d(a2, b2, c2, e).eqv(T::zero()),
        all_above_plane(a1, b1, c1, a2, b2, c2),
    ensures
        !segment_triangle_intersects_strict(d, e, a1, b1, c1),
{
    // Assume for contradiction that segment_triangle_intersects_strict(d,e,a1,b1,c1).
    if segment_triangle_intersects_strict(d, e, a1, b1, c1) {
        let t = segment_plane_intersection_parameter(d, e, a1, b1, c1);
        let p = segment_plane_intersection_point(d, e, a1, b1, c1);

        // (A) orient3d(a2,b2,c2,p) ≡ 0:
        //     p = add_vec3(d, scale(t, sub3(e,d))), and d,e are coplanar with T2.
        lemma_orient3d_zero_on_coplanar_segment::<T>(a2, b2, c2, d, e, t);

        // (B) orient3d(a1,b1,c1,p) ≡ 0:
        //     p is on the plane of T1 by construction (intersection point).
        //     This follows from the intersection parameter definition.
        lemma_intersection_on_plane::<T>(d, e, a1, b1, c1);

        // (C) point_in_triangle_on_plane(p, a1, b1, c1):
        //     from the definition of segment_triangle_intersects_strict.

        // (D) orient3d(a2,b2,c2,p) > 0:
        //     from lemma_inside_triangle_orient3d_positive.
        lemma_inside_triangle_orient3d_positive::<T>(p, a1, b1, c1, a2, b2, c2);

        // Contradiction: orient3d(a2,b2,c2,p) ≡ 0 AND orient3d(a2,b2,c2,p) > 0.
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), orient3d(a2, b2, c2, p));
        T::axiom_eqv_symmetric(orient3d(a2, b2, c2, p), T::zero());
    }
}

/// The intersection point lies on the plane of the triangle.
pub proof fn lemma_intersection_on_plane<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures
        orient3d(a, b, c, segment_plane_intersection_point(d, e, a, b, c)).eqv(T::zero()),
{
    let od = orient3d(a, b, c, d);
    let oe = orient3d(a, b, c, e);
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let ed = sub3(e, d);
    let t = segment_plane_intersection_parameter(d, e, a, b, c);
    let w = scale(t, ed);

    // Precondition for orient_cancel: od - oe ≠ 0
    lemma_crossing_denominator_nonzero::<T>(d, e, a, b, c);

    // (1) orient3d(a,b,c,p) ≡ od + triple(ba,ca,w) by linear_last
    lemma_orient3d_linear_last::<T>(a, b, c, d, w);

    // (2) triple(ba,ca,w) ≡ t * triple(ba,ca,ed) by triple_scale_third
    lemma_triple_scale_third::<T>(t, ba, ca, ed);

    // (3) Establish triple(ba,ca,ed) ≡ oe + (-od):
    //     From linear_last: orient3d(a,b,c,d+ed) ≡ od + triple(ba,ca,ed)
    //     From shift_endpoint: orient3d(a,b,c,d+ed) ≡ oe
    //     So: od + triple(ba,ca,ed) ≡ oe
    lemma_orient3d_linear_last::<T>(a, b, c, d, ed);
    lemma_orient3d_shift_endpoint::<T>(a, b, c, d, e);
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, add_vec3(d, ed)),
        od.add(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        od.add(triple(ba, ca, ed)),
        orient3d(a, b, c, add_vec3(d, ed)),
        oe,
    );
    // Now: od + triple(ba,ca,ed) ≡ oe

    //     Derive: od + (oe + (-od)) ≡ oe
    //     sub_then_add_cancel(oe, od): (oe - od) + od ≡ oe
    //     commutativity: od + (oe - od) ≡ (oe - od) + od ≡ oe
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(oe, od);
    T::axiom_add_commutative(od, oe.sub(od));
    T::axiom_eqv_transitive(
        od.add(oe.sub(od)),
        oe.sub(od).add(od),
        oe,
    );
    //     sub_is_add_neg: oe.sub(od) ≡ oe + (-od)
    T::axiom_sub_is_add_neg(oe, od);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od, oe.sub(od), oe.add(od.neg()),
    );
    T::axiom_eqv_symmetric(
        od.add(oe.sub(od)),
        od.add(oe.add(od.neg())),
    );
    T::axiom_eqv_transitive(
        od.add(oe.add(od.neg())),
        od.add(oe.sub(od)),
        oe,
    );
    // Now: od + (oe + (-od)) ≡ oe

    //     Left cancel: triple(ba,ca,ed) ≡ oe + (-od)
    T::axiom_eqv_symmetric(od.add(oe.add(od.neg())), oe);
    T::axiom_eqv_transitive(
        od.add(triple(ba, ca, ed)),
        oe,
        od.add(oe.add(od.neg())),
    );
    additive_group_lemmas::lemma_add_left_cancel::<T>(triple(ba, ca, ed), oe.add(od.neg()), od);

    // (4) t * triple(ba,ca,ed) ≡ t * (oe + (-od)) by mul congruence
    ring_lemmas::lemma_mul_congruence_right::<T>(t, triple(ba, ca, ed), oe.add(od.neg()));

    // (5) od + t*triple ≡ od + t*(oe+(-od)) by add congruence
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od, t.mul(triple(ba, ca, ed)), t.mul(oe.add(od.neg())),
    );

    // (6) od + t*(oe+(-od)) ≡ 0 by orient_cancel
    lemma_orient_cancel::<T>(od, oe);

    // (7) Chain: od + triple(ba,ca,w) ≡ od + t*triple ≡ od + t*(oe+(-od)) ≡ 0
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od, triple(ba, ca, w), t.mul(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        od.add(triple(ba, ca, w)),
        od.add(t.mul(triple(ba, ca, ed))),
        od.add(t.mul(oe.add(od.neg()))),
    );
    T::axiom_eqv_transitive(
        od.add(triple(ba, ca, w)),
        od.add(t.mul(oe.add(od.neg()))),
        T::zero(),
    );

    // (8) Final: orient3d(a,b,c,p) ≡ od + triple(ba,ca,w) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, add_vec3(d, w)),
        od.add(triple(ba, ca, w)),
        T::zero(),
    );
}

// =========================================================================
// Lemma: SINGLE-sided separation → no intersection
// =========================================================================

/// If all vertices of T1 are on the same strict side of plane(T2), then
/// the two triangles do not strictly intersect.
///
/// This strengthens `lemma_both_separated_no_intersection` which requires
/// BOTH planes to separate. Single-sided separation suffices because:
/// - T1 edges can't cross plane(T2) (they're all on one side)
/// - T2 edges that cross plane(T1) would produce intersection points that
///   are both on plane(T2) (from being on a T2 edge) AND strictly above/below
///   plane(T2) (from being inside T1 with all vertices above/below), a
///   contradiction.
pub proof fn lemma_single_sided_separation<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        all_same_strict_side(a1, b1, c1, a2, b2, c2),
    ensures
        !triangles_intersect_strict(a1, b1, c1, a2, b2, c2),
{
    // T1 edges through T2: all T1 vertices on same side → no edge crosses plane(T2)
    lemma_t1_separated_no_t1_edges::<T>(a1, b1, c1, a2, b2, c2);

    // T2 edges through T1: each T2 edge endpoint is a vertex of T2, so coplanar with T2.
    // orient3d(a2,b2,c2,vertex_of_T2) ≡ 0 by the degenerate lemmas.
    if all_above_plane(a1, b1, c1, a2, b2, c2) {
        // Edge (a2, b2)
        lemma_orient3d_degenerate_da::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_bd::<T>(a2, b2, c2);
        lemma_coplanar_edge_no_intersection::<T>(a2, b2, a1, b1, c1, a2, b2, c2);

        // Edge (b2, c2)
        lemma_orient3d_degenerate_cd::<T>(a2, b2, c2);
        lemma_coplanar_edge_no_intersection::<T>(b2, c2, a1, b1, c1, a2, b2, c2);

        // Edge (c2, a2)
        lemma_coplanar_edge_no_intersection::<T>(c2, a2, a1, b1, c1, a2, b2, c2);
    } else {
        // all_below_plane case: orient3d(a2,b2,c2,a1) < 0, etc.
        // The argument is symmetric. We need orient3d(a2,b2,c2,p) < 0 from
        // all-below, but orient3d(a2,b2,c2,p) ≡ 0 from coplanarity.
        // For now, prove via negation: -orient3d gives all-above with swapped plane.
        lemma_orient3d_degenerate_da::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_bd::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_cd::<T>(a2, b2, c2);

        // Need below-plane variant of coplanar_edge_no_intersection.
        lemma_coplanar_edge_no_intersection_below::<T>(a2, b2, a1, b1, c1, a2, b2, c2);
        lemma_coplanar_edge_no_intersection_below::<T>(b2, c2, a1, b1, c1, a2, b2, c2);
        lemma_coplanar_edge_no_intersection_below::<T>(c2, a2, a1, b1, c1, a2, b2, c2);
    }
}

/// Symmetric version for all-below-plane case.
pub proof fn lemma_coplanar_edge_no_intersection_below<T: OrderedField>(
    d: Point3<T>, e: Point3<T>,
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        orient3d(a2, b2, c2, d).eqv(T::zero()),
        orient3d(a2, b2, c2, e).eqv(T::zero()),
        all_below_plane(a1, b1, c1, a2, b2, c2),
    ensures
        !segment_triangle_intersects_strict(d, e, a1, b1, c1),
{
    // Same as coplanar_edge_no_intersection but with orient3d(a2,b2,c2,p) < 0
    // contradicting orient3d(a2,b2,c2,p) ≡ 0.
    if segment_triangle_intersects_strict(d, e, a1, b1, c1) {
        let t = segment_plane_intersection_parameter(d, e, a1, b1, c1);
        let p = segment_plane_intersection_point(d, e, a1, b1, c1);

        lemma_orient3d_zero_on_coplanar_segment::<T>(a2, b2, c2, d, e, t);
        lemma_intersection_on_plane::<T>(d, e, a1, b1, c1);

        // orient3d(a2,b2,c2,p) < 0 from all-below + inside triangle
        // (uses the negative version of orient3d_affine_positive)
        lemma_inside_triangle_orient3d_negative::<T>(p, a1, b1, c1, a2, b2, c2);

        // Contradiction: orient3d(a2,b2,c2,p) ≡ 0 AND < 0
        T::axiom_lt_iff_le_and_not_eqv(orient3d(a2, b2, c2, p), T::zero());
    }
}

/// Negative version: if all vertices are below the plane, orient3d(x,y,z,p) < 0.
pub proof fn lemma_inside_triangle_orient3d_negative<T: OrderedField>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
)
    requires
        point_in_triangle_on_plane(p, a, b, c),
        orient3d(a, b, c, p).eqv(T::zero()),
        orient3d(x, y, z, a).lt(T::zero()),
        orient3d(x, y, z, b).lt(T::zero()),
        orient3d(x, y, z, c).lt(T::zero()),
    ensures
        orient3d(x, y, z, p).lt(T::zero()),
{
    // Symmetric to the positive case via negation.
    assume(false);  // proof debt: same structure as positive case
}

} // verus!
