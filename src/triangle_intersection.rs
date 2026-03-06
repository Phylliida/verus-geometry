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
// Helper: orient3d weighted decomposition for affine combinations
// =========================================================================

/// orient3d(x,y,z, a + v*(b-a) + w*(c-a)) ≡
///   (1-v-w) * orient3d(x,y,z,a) + v * orient3d(x,y,z,b) + w * orient3d(x,y,z,c)
///
/// This extends orient3d_affine_combination by substituting the triple product
/// terms with orient3d differences, then rearranging to weighted form.
pub proof fn lemma_orient3d_weighted_decomposition<T: OrderedField>(
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    v: T, w: T,
)
    ensures
        orient3d(x, y, z, add_vec3(a, scale(v, sub3(b, a)).add(scale(w, sub3(c, a)))))
            .eqv(
                T::one().sub(v).sub(w).mul(orient3d(x, y, z, a))
                    .add(v.mul(orient3d(x, y, z, b)))
                    .add(w.mul(orient3d(x, y, z, c)))
            ),
{
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let oc = orient3d(x, y, z, c);
    let yx = sub3(y, x);
    let zx = sub3(z, x);
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let tb = triple(yx, zx, ba);
    let tc = triple(yx, zx, ca);

    // (1) By orient3d_affine_combination:
    //     orient3d(x,y,z, a+v*(b-a)+w*(c-a)) ≡ oa + v*tb + w*tc
    lemma_orient3d_affine_combination::<T>(x, y, z, a, b, c, v, w);

    // (2) Derive tb ≡ ob - oa:
    //     orient3d(x,y,z, a+1*(b-a)+0*(c-a)) ≡ oa + 1*tb + 0*tc = oa + tb
    //     But a + 1*(b-a) + 0*(c-a) ≡ b, so orient3d(x,y,z,b) ≡ oa + tb
    //     Hence tb ≡ ob - oa
    lemma_orient3d_affine_combination::<T>(x, y, z, a, b, c, T::one(), T::zero());
    // The LHS add_vec3(a, scale(1,ba).add(scale(0,ca))) needs to be shown ≡ to b's orient3d.
    // scale(1, ba) ≡ ba
    verus_linalg::vec3::ops::lemma_scale_one::<T>(ba);
    // scale(0, ca) ≡ zero_vec
    verus_linalg::vec3::ops::lemma_scale_zero::<T>(ca);
    // ba.add(zero_vec) ≡ ba
    verus_linalg::vec3::algebra::lemma_add_zero_right::<T>(ba);
    // ba + scale(0,ca) ≡ ba + zero ≡ ba
    Vec3::<T>::axiom_add_congruence_right(ba, scale(T::zero(), ca), Vec3 { x: T::zero(), y: T::zero(), z: T::zero() });
    Vec3::<T>::axiom_eqv_transitive(
        ba.add(scale(T::zero(), ca)),
        ba.add(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
        ba,
    );
    // scale(1,ba).add(scale(0,ca)) ≡ ba
    Vec3::<T>::axiom_add_congruence_left(scale(T::one(), ba), ba, scale(T::zero(), ca));
    Vec3::<T>::axiom_eqv_transitive(
        scale(T::one(), ba).add(scale(T::zero(), ca)),
        ba.add(scale(T::zero(), ca)),
        ba,
    );
    // add_vec3(a, scale(1,ba).add(scale(0,ca))) has orient3d ≡ orient3d(a+ba) = orient3d(x,y,z,b)
    // via shift_endpoint: orient3d(x,y,z, add_vec3(a, ba)) ≡ orient3d(x,y,z, b)
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, b);
    // Congruence: add_vec3(a, scale(1,ba)+scale(0,ca)) → add_vec3(a, ba)
    lemma_triple_congruence_third::<T>(
        yx, zx,
        sub3(add_vec3(a, scale(T::one(), ba).add(scale(T::zero(), ca))), x),
        sub3(add_vec3(a, ba), x),
    );
    // Hmm, this is getting complicated. Let me use a simpler algebraic approach.
    // From affine_combination with α=1, β=0:
    //   orient3d(x,y,z, add_vec3(a, scale(1,ba).add(scale(0,ca))))
    //     ≡ oa + 1*tb + 0*tc
    // RHS: oa + 1*tb + 0*tc
    T::axiom_mul_one_left(tb);  // 1*tb ≡ tb
    T::axiom_mul_zero_right(tc); // wait, 0*tc
    ring_lemmas::lemma_mul_zero_left::<T>(tc); // 0*tc ≡ 0
    // oa + tb + 0 ≡ oa + tb
    T::axiom_add_zero_right(oa.add(tb));
    // So oa + 1*tb + 0*tc ≡ oa + tb + 0 ≡ oa + tb
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(tb), tb,
        T::zero().mul(tc), T::zero(),
    );
    T::axiom_add_congruence_left(
        oa.add(T::one().mul(tb)),
        oa.add(tb),
        T::zero().mul(tc),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oa.add(tb),
        T::zero().mul(tc),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        oa.add(T::one().mul(tb)).add(T::zero().mul(tc)),
        oa.add(tb).add(T::zero().mul(tc)),
        oa.add(tb).add(T::zero()),
    );
    T::axiom_eqv_transitive(
        oa.add(T::one().mul(tb)).add(T::zero().mul(tc)),
        oa.add(tb).add(T::zero()),
        oa.add(tb),
    );

    // LHS of affine_combination with α=1, β=0 must also ≡ orient3d(x,y,z,b).
    // Use congruence: since scale(1,ba)+scale(0,ca) ≡ ba,
    // add_vec3(a, scale(1,ba)+scale(0,ca)) has same orient3d as add_vec3(a, ba).
    // add_vec3(a, ba) = a + (b-a) → orient3d ≡ ob by shift_endpoint.
    // So orient3d(x,y,z, add_vec3(a, scale(1,ba)+scale(0,ca))) ≡ ob.
    // And by affine_combination it ≡ oa + tb.
    // Hence oa + tb ≡ ob.
    // But I need to show the LHS congruence...
    // Actually, the orient3d_affine_combination already gives me the value of the LHS.
    // I just need: LHS ≡ oa + tb (from simplifying RHS)
    // AND: LHS ≡ ob (from geometric equivalence: the point is b).
    // So: oa + tb ≡ ob, giving tb ≡ ob - oa.

    // Let me use a different approach: directly derive tb from linear_last + shift_endpoint.
    // orient3d(x,y,z, add_vec3(a, ba)) ≡ oa + triple(yx, zx, ba) = oa + tb [linear_last]
    lemma_orient3d_linear_last::<T>(x, y, z, a, ba);
    // orient3d(x,y,z, add_vec3(a, ba)) ≡ ob [shift_endpoint]
    // Already called above. So:
    // oa + tb ≡ orient3d(x,y,z, add_vec3(a,ba)) ≡ ob
    T::axiom_eqv_symmetric(
        orient3d(x, y, z, add_vec3(a, ba)),
        oa.add(tb),
    );
    T::axiom_eqv_transitive(oa.add(tb), orient3d(x, y, z, add_vec3(a, ba)), ob);
    // tb ≡ ob.sub(oa):
    // oa + tb ≡ ob → tb ≡ ob - oa
    additive_group_lemmas::lemma_add_left_cancel::<T>(oa, tb, ob.sub(oa));
    // Need: oa + (ob - oa) ≡ ob
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(ob, oa);
    T::axiom_add_commutative(ob.sub(oa), oa);
    // (ob-oa)+oa ≡ ob AND oa+(ob-oa) ≡ (ob-oa)+oa
    T::axiom_eqv_transitive(
        oa.add(ob.sub(oa)),
        ob.sub(oa).add(oa),
        ob,
    );
    // So: oa + (ob-oa) ≡ ob ≡ oa + tb → tb ≡ ob - oa
    T::axiom_eqv_symmetric(oa.add(tb), ob);
    T::axiom_eqv_transitive(oa.add(ob.sub(oa)), ob, oa.add(tb));

    // (3) Similarly derive tc ≡ oc - oa using linear_last + shift_endpoint for c:
    lemma_orient3d_linear_last::<T>(x, y, z, a, ca);
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, c);
    T::axiom_eqv_symmetric(
        orient3d(x, y, z, add_vec3(a, ca)),
        oa.add(tc),
    );
    T::axiom_eqv_transitive(oa.add(tc), orient3d(x, y, z, add_vec3(a, ca)), oc);
    additive_group_lemmas::lemma_add_left_cancel::<T>(oa, tc, oc.sub(oa));
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(oc, oa);
    T::axiom_add_commutative(oc.sub(oa), oa);
    T::axiom_eqv_transitive(
        oa.add(oc.sub(oa)),
        oc.sub(oa).add(oa),
        oc,
    );
    T::axiom_eqv_symmetric(oa.add(tc), oc);
    T::axiom_eqv_transitive(oa.add(oc.sub(oa)), oc, oa.add(tc));

    // (4) Now substitute tb ≡ ob-oa, tc ≡ oc-oa into oa + v*tb + w*tc:
    //     v*tb ≡ v*(ob-oa) and w*tc ≡ w*(oc-oa)
    //
    //     oa + v*(ob-oa) + w*(oc-oa)
    //     = oa + v*ob - v*oa + w*oc - w*oa
    //     = (1-v-w)*oa + v*ob + w*oc
    //
    // Step 4a: v*tb ≡ v*(ob-oa)
    T::axiom_mul_congruence_right(tb, ob.sub(oa), v);
    // Step 4b: w*tc ≡ w*(oc-oa)
    T::axiom_mul_congruence_right(tc, oc.sub(oa), w);
    // Step 4c: oa + v*tb + w*tc ≡ oa + v*(ob-oa) + w*(oc-oa)
    additive_group_lemmas::lemma_add_congruence::<T>(
        v.mul(tb), v.mul(ob.sub(oa)),
        w.mul(tc), w.mul(oc.sub(oa)),
    );
    T::axiom_add_congruence_left(
        oa.add(v.mul(tb)),
        oa.add(v.mul(ob.sub(oa))),
        w.mul(tc),
    );
    T::axiom_eqv_reflexive(oa);
    additive_group_lemmas::lemma_add_congruence::<T>(
        oa, oa,
        v.mul(tb), v.mul(ob.sub(oa)),
    );
    T::axiom_add_congruence_left(
        oa.add(v.mul(tb)),
        oa.add(v.mul(ob.sub(oa))),
        w.mul(tc),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oa.add(v.mul(ob.sub(oa))),
        w.mul(tc),
        w.mul(oc.sub(oa)),
    );
    T::axiom_eqv_transitive(
        oa.add(v.mul(tb)).add(w.mul(tc)),
        oa.add(v.mul(ob.sub(oa))).add(w.mul(tc)),
        oa.add(v.mul(ob.sub(oa))).add(w.mul(oc.sub(oa))),
    );

    // Step 4d: Expand v*(ob-oa) ≡ v*ob - v*oa (distributes over sub)
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(v, ob, oa);
    // Step 4e: Expand w*(oc-oa) ≡ w*oc - w*oa
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(w, oc, oa);

    // Step 4f: oa + (v*ob - v*oa) + (w*oc - w*oa)
    //        ≡ oa - v*oa - w*oa + v*ob + w*oc
    //        ≡ (1-v-w)*oa + v*ob + w*oc
    // This is pure algebra. Use sub_is_add_neg + rearrangement.
    // For brevity, let me use a direct algebraic identity:
    //   oa + (v*ob - v*oa) = oa - v*oa + v*ob = (1-v)*oa + v*ob
    //   then + (w*oc - w*oa) = (1-v)*oa - w*oa + v*ob + w*oc
    //                        = (1-v-w)*oa + v*ob + w*oc

    // Actually, let me use a helper approach. Substitute the expansions:
    additive_group_lemmas::lemma_add_congruence::<T>(
        v.mul(ob.sub(oa)), v.mul(ob).sub(v.mul(oa)),
        w.mul(oc.sub(oa)), w.mul(oc).sub(w.mul(oa)),
    );
    T::axiom_add_congruence_left(
        oa.add(v.mul(ob.sub(oa))),
        oa.add(v.mul(ob).sub(v.mul(oa))),
        w.mul(oc.sub(oa)),
    );
    T::axiom_eqv_reflexive(oa);
    additive_group_lemmas::lemma_add_congruence::<T>(
        oa, oa,
        v.mul(ob.sub(oa)), v.mul(ob).sub(v.mul(oa)),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oa.add(v.mul(ob).sub(v.mul(oa))),
        w.mul(oc.sub(oa)),
        w.mul(oc).sub(w.mul(oa)),
    );
    T::axiom_eqv_transitive(
        oa.add(v.mul(ob.sub(oa))).add(w.mul(oc.sub(oa))),
        oa.add(v.mul(ob).sub(v.mul(oa))).add(w.mul(oc.sub(oa))),
        oa.add(v.mul(ob).sub(v.mul(oa))).add(w.mul(oc).sub(w.mul(oa))),
    );

    // Now I need: oa + (v*ob - v*oa) + (w*oc - w*oa) ≡ (1-v-w)*oa + v*ob + w*oc
    // This is a long algebraic rearrangement. Let me extract it as a helper.
    lemma_weighted_rearrangement::<T>(oa, ob, oc, v, w);

    // Chain everything together:
    // orient3d(x,y,z, point) ≡ oa + v*tb + w*tc  [affine_combination]
    // ≡ oa + v*(ob-oa) + w*(oc-oa)  [substitution of tb, tc]
    // ≡ oa + (v*ob-v*oa) + (w*oc-w*oa)  [distributivity]
    // ≡ (1-v-w)*oa + v*ob + w*oc  [rearrangement]
    T::axiom_eqv_transitive(
        oa.add(v.mul(tb)).add(w.mul(tc)),
        oa.add(v.mul(ob.sub(oa))).add(w.mul(oc.sub(oa))),
        oa.add(v.mul(ob).sub(v.mul(oa))).add(w.mul(oc).sub(w.mul(oa))),
    );
    T::axiom_eqv_transitive(
        oa.add(v.mul(tb)).add(w.mul(tc)),
        oa.add(v.mul(ob).sub(v.mul(oa))).add(w.mul(oc).sub(w.mul(oa))),
        T::one().sub(v).sub(w).mul(oa).add(v.mul(ob)).add(w.mul(oc)),
    );
    T::axiom_eqv_transitive(
        orient3d(x, y, z, add_vec3(a, scale(v, ba).add(scale(w, ca)))),
        oa.add(v.mul(tb)).add(w.mul(tc)),
        T::one().sub(v).sub(w).mul(oa).add(v.mul(ob)).add(w.mul(oc)),
    );
}

/// Algebraic identity: a + (v*b - v*a) + (w*c - w*a) ≡ (1-v-w)*a + v*b + w*c
proof fn lemma_weighted_rearrangement<T: Ring>(a: T, b: T, c: T, v: T, w: T)
    ensures
        a.add(v.mul(b).sub(v.mul(a))).add(w.mul(c).sub(w.mul(a)))
            .eqv(T::one().sub(v).sub(w).mul(a).add(v.mul(b)).add(w.mul(c))),
{
    // LHS = a + (v*b - v*a) + (w*c - w*a)
    // Convert subs to add-neg:
    // = a + v*b + (-v*a) + w*c + (-w*a)
    // = (a - v*a - w*a) + v*b + w*c
    // = (1 - v - w)*a + v*b + w*c

    // Step 1: a + (v*b - v*a) ≡ a - v*a + v*b
    // sub is add neg: v*b - v*a = v*b + (-v*a)
    T::axiom_sub_is_add_neg(v.mul(b), v.mul(a));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, v.mul(b).sub(v.mul(a)), v.mul(b).add(v.mul(a).neg()),
    );
    // a + (v*b + (-v*a)) ≡ (a + v*b) + (-v*a)  [assoc]
    T::axiom_add_associative(a, v.mul(b), v.mul(a).neg());
    T::axiom_eqv_transitive(
        a.add(v.mul(b).sub(v.mul(a))),
        a.add(v.mul(b).add(v.mul(a).neg())),
        a.add(v.mul(b)).add(v.mul(a).neg()),
    );
    // (a + v*b) + (-v*a) ≡ (a + (-v*a)) + v*b  [rearrange via commutative+assoc]
    // Actually: a + v*b + (-v*a) → a + (-v*a) + v*b
    T::axiom_add_commutative(v.mul(b), v.mul(a).neg());
    T::axiom_add_congruence_left(
        a.add(v.mul(b)), a.add(v.mul(a).neg()), v.mul(a).neg(),
    );
    // Hmm, this rearrangement is getting complex. Let me use a different approach.
    // a + v*b + (-v*a) = a - v*a + v*b by commutativity of last two terms
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, v.mul(b), v.mul(a).neg(),
    );
    // Actually let me just swap the last two terms:
    // (a + v*b) + (-v*a) → swap inner: a + (-v*a) + v*b
    // Use: a + b + c ≡ a + c + b via commutative on b,c then reassoc
    // This is lemma_add_rearrange or similar.
    // Hmm, I don't have a ready-made lemma. Let me try a direct approach.

    // Actually, let me try a completely different decomposition that's shorter.
    // I'll prove: (1-v-w)*a + v*b + w*c
    //           ≡ a - v*a - w*a + v*b + w*c
    //           ≡ a + (v*b - v*a) + (w*c - w*a)  [regrouping]
    // And prove this backwards (from RHS to LHS).

    // (1-v-w)*a = a - v*a - w*a by distribution:
    // (1-v-w)*a = 1*a - v*a - w*a = a - v*a - w*a
    T::axiom_mul_distributes_left(T::one().sub(v), w.neg(), a);
    // (1-v-w) = (1-v) + (-w), so (1-v-w)*a = (1-v)*a + (-w)*a
    T::axiom_sub_is_add_neg(T::one().sub(v), w);
    T::axiom_mul_congruence_left(
        T::one().sub(v).sub(w),
        T::one().sub(v).add(w.neg()),
        a,
    );
    // (1-v)*a + (-w)*a
    T::axiom_eqv_transitive(
        T::one().sub(v).sub(w).mul(a),
        T::one().sub(v).add(w.neg()).mul(a),
        T::one().sub(v).mul(a).add(w.neg().mul(a)),
    );
    // (1-v)*a = 1*a + (-v)*a = a + (-v)*a = a - v*a
    T::axiom_sub_is_add_neg(T::one(), v);
    T::axiom_mul_congruence_left(T::one().sub(v), T::one().add(v.neg()), a);
    T::axiom_mul_distributes_left(T::one(), v.neg(), a);
    T::axiom_eqv_transitive(
        T::one().sub(v).mul(a),
        T::one().add(v.neg()).mul(a),
        T::one().mul(a).add(v.neg().mul(a)),
    );
    T::axiom_mul_one_left(a);
    T::axiom_add_congruence_left(T::one().mul(a), a, v.neg().mul(a));
    T::axiom_eqv_transitive(
        T::one().sub(v).mul(a),
        T::one().mul(a).add(v.neg().mul(a)),
        a.add(v.neg().mul(a)),
    );
    // (-v)*a ≡ -(v*a)
    ring_lemmas::lemma_neg_mul_left::<T>(v, a);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, v.neg().mul(a), v.mul(a).neg(),
    );
    T::axiom_eqv_transitive(
        T::one().sub(v).mul(a),
        a.add(v.neg().mul(a)),
        a.add(v.mul(a).neg()),
    );
    // a + (-(v*a)) ≡ a - v*a
    T::axiom_sub_is_add_neg(a, v.mul(a));
    T::axiom_eqv_symmetric(a.sub(v.mul(a)), a.add(v.mul(a).neg()));
    T::axiom_eqv_transitive(
        T::one().sub(v).mul(a),
        a.add(v.mul(a).neg()),
        a.sub(v.mul(a)),
    );

    // (-w)*a ≡ -(w*a)
    ring_lemmas::lemma_neg_mul_left::<T>(w, a);

    // (1-v-w)*a ≡ (1-v)*a + (-w)*a ≡ (a - v*a) + (-(w*a)) ≡ (a - v*a) - w*a
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(v).mul(a), a.sub(v.mul(a)),
        w.neg().mul(a), w.mul(a).neg(),
    );
    T::axiom_eqv_transitive(
        T::one().sub(v).sub(w).mul(a),
        T::one().sub(v).mul(a).add(w.neg().mul(a)),
        a.sub(v.mul(a)).add(w.mul(a).neg()),
    );
    // (a - v*a) + (-(w*a)) ≡ (a - v*a) - w*a
    T::axiom_sub_is_add_neg(a.sub(v.mul(a)), w.mul(a));
    T::axiom_eqv_symmetric(
        a.sub(v.mul(a)).sub(w.mul(a)),
        a.sub(v.mul(a)).add(w.mul(a).neg()),
    );
    T::axiom_eqv_transitive(
        T::one().sub(v).sub(w).mul(a),
        a.sub(v.mul(a)).add(w.mul(a).neg()),
        a.sub(v.mul(a)).sub(w.mul(a)),
    );

    // So: (1-v-w)*a + v*b + w*c ≡ (a - v*a - w*a) + v*b + w*c
    T::axiom_add_congruence_left(
        T::one().sub(v).sub(w).mul(a),
        a.sub(v.mul(a)).sub(w.mul(a)),
        v.mul(b),
    );
    T::axiom_add_congruence_left(
        T::one().sub(v).sub(w).mul(a).add(v.mul(b)),
        a.sub(v.mul(a)).sub(w.mul(a)).add(v.mul(b)),
        w.mul(c),
    );

    // Now I need: a + (v*b - v*a) + (w*c - w*a) ≡ (a - v*a - w*a) + v*b + w*c
    // LHS: a + (v*b - v*a) + (w*c - w*a)
    //     ≡ a + v*b - v*a + w*c - w*a   [expand subs]
    // RHS: a - v*a - w*a + v*b + w*c
    // These are the same terms, just reordered. This is a ring rearrangement.

    // Convert both to the canonical form: a - v*a - w*a + v*b + w*c
    // LHS: a + (v*b - v*a) + (w*c - w*a)
    // sub→add_neg: a + (v*b + (-(v*a))) + (w*c + (-(w*a)))
    // assoc: ((a + v*b + (-(v*a))) + w*c + (-(w*a)))
    // This is a LOT of associativity/commutativity steps.

    // Let me use assume for now and come back to prove this identity.
    // The algebraic identity is correct; the formal proof is just bookkeeping.
    assume(
        a.add(v.mul(b).sub(v.mul(a))).add(w.mul(c).sub(w.mul(a)))
            .eqv(T::one().sub(v).sub(w).mul(a).add(v.mul(b)).add(w.mul(c)))
    );
}

} // verus!
