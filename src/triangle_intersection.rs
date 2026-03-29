use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{scale, triple, dot, cross};
use verus_linalg::vec3::ops::{
    lemma_triple_scale_third,
    lemma_triple_congruence_third,
    lemma_triple_cyclic,
    lemma_triple_self_zero_13,
    lemma_triple_self_zero_23,
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

//  =========================================================================
//  Triangle-triangle intersection (3D, strict / non-coplanar)
//  =========================================================================

///  All three vertices p, q, r are strictly above the plane (a, b, c).
pub open spec fn all_above_plane<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    point_above_plane(p, a, b, c)
    && point_above_plane(q, a, b, c)
    && point_above_plane(r, a, b, c)
}

///  All three vertices p, q, r are strictly below the plane (a, b, c).
pub open spec fn all_below_plane<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    point_below_plane(p, a, b, c)
    && point_below_plane(q, a, b, c)
    && point_below_plane(r, a, b, c)
}

///  All three vertices p, q, r are on the same strict side of the plane (a, b, c).
pub open spec fn all_same_strict_side<T: OrderedRing>(
    p: Point3<T>, q: Point3<T>, r: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    all_above_plane(p, q, r, a, b, c) || all_below_plane(p, q, r, a, b, c)
}

///  Two triangles T1 = (a1, b1, c1) and T2 = (a2, b2, c2) strictly intersect:
///  some edge of one triangle passes strictly through the other triangle's interior.
///
///  "Strict" means: endpoints of each tested segment are on opposite sides of the
///  other triangle's plane (neither endpoint lies on the plane). This excludes
///  coplanar configurations, vertex-on-face touching, and edge-on-edge touching.
pub open spec fn triangles_intersect_strict<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
) -> bool {
    //  Edges of T1 through T2
    segment_triangle_intersects_strict(a1, b1, a2, b2, c2)
    || segment_triangle_intersects_strict(b1, c1, a2, b2, c2)
    || segment_triangle_intersects_strict(c1, a1, a2, b2, c2)
    //  Edges of T2 through T1
    || segment_triangle_intersects_strict(a2, b2, a1, b1, c1)
    || segment_triangle_intersects_strict(b2, c2, a1, b1, c1)
    || segment_triangle_intersects_strict(c2, a2, a1, b1, c1)
}

//  =========================================================================
//  Lemma: plane separation kills edge crossing
//  =========================================================================

///  If both endpoints of a segment are strictly above a plane, the segment
///  does not strictly cross that plane.
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

///  If both endpoints of a segment are strictly below a plane, the segment
///  does not strictly cross that plane.
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

//  =========================================================================
//  Lemma: all-same-side → no edge of that triangle crosses the plane
//  =========================================================================

///  If all vertices of triangle (p, q, r) are on the same strict side of
///  the plane (a, b, c), then no edge of (p, q, r) strictly crosses that plane.
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

//  =========================================================================
//  Lemma: one-sided separation kills that triangle's edge tests
//  =========================================================================

///  If all vertices of T1 are on the same strict side of plane(T2), then
///  no edge of T1 can pass strictly through T2.
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

///  Symmetric: if all vertices of T2 are on the same strict side of plane(T1),
///  then no edge of T2 can pass strictly through T1.
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

//  =========================================================================
//  Lemma: BOTH sides separated → no intersection
//  =========================================================================

///  If T1's vertices are all on the same strict side of plane(T2), AND
///  T2's vertices are all on the same strict side of plane(T1), then the
///  triangles do not strictly intersect.
///
///  This is the common case in mesh processing: most triangle pairs are
///  separated by at least one of the two half-space tests.
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

//  =========================================================================
//  Lemma: symmetry
//  =========================================================================

///  Triangle-triangle strict intersection is symmetric.
pub proof fn lemma_triangles_intersect_strict_symmetric<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    ensures
        triangles_intersect_strict(a1, b1, c1, a2, b2, c2)
            == triangles_intersect_strict(a2, b2, c2, a1, b1, c1),
{
    //  Both sides are the same 6 disjuncts, just reordered.
    //  T1 edges through T2 become the last 3 disjuncts of the swapped version,
    //  T2 edges through T1 become the first 3. OR is commutative.
}

//  =========================================================================
//  Helper: orient3d zero on segment between coplanar points
//  =========================================================================

///  If two points d, e both satisfy orient3d(a,b,c,_) ≡ 0, then any point
///  on the line through d,e also satisfies orient3d ≡ 0.
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

    //  (1) orient3d(a,b,c, d+w) ≡ orient3d(a,b,c,d) + triple(ba, ca, w)
    lemma_orient3d_linear_last::<T>(a, b, c, d, w);

    //  (2) triple(ba, ca, scale(t, ed)) ≡ t * triple(ba, ca, ed)
    lemma_triple_scale_third::<T>(t, ba, ca, ed);

    //  (3) Derive triple(ba, ca, ed) ≡ 0:
    //      shift_endpoint: orient3d(a,b,c, add_vec3(d, ed)) ≡ orient3d(a,b,c,e)
    //      linear_last:    orient3d(a,b,c, add_vec3(d, ed)) ≡ orient3d(a,b,c,d) + triple(ba,ca,ed)
    //      So: orient3d(a,b,c,d) + triple(ba,ca,ed) ≡ orient3d(a,b,c,e) ≡ 0
    lemma_orient3d_shift_endpoint::<T>(a, b, c, d, e);
    lemma_orient3d_linear_last::<T>(a, b, c, d, ed);
    //  orient3d(a,b,c,d) + triple(ba,ca,ed) ≡ orient3d(a,b,c,e)
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, add_vec3(d, ed)),
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        orient3d(a, b, c, add_vec3(d, ed)),
        orient3d(a, b, c, e),
    );
    //  orient3d(a,b,c,d) + triple(...) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        orient3d(a, b, c, e),
        T::zero(),
    );
    //  Substitute orient3d(a,b,c,d) ≡ 0: orient3d(..,d)+triple ≡ 0+triple
    T::axiom_add_congruence_left(
        orient3d(a, b, c, d), T::zero(), triple(ba, ca, ed),
    );
    //  orient3d(..,d)+triple ≡ 0+triple [above gives this direction]
    //  We already have orient3d(..,d)+triple ≡ 0, so 0+triple ≡ 0
    T::axiom_eqv_symmetric(
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        T::zero().add(triple(ba, ca, ed)),
    );
    T::axiom_eqv_transitive(
        T::zero().add(triple(ba, ca, ed)),
        orient3d(a, b, c, d).add(triple(ba, ca, ed)),
        T::zero(),
    );
    //  0 + triple(...) ≡ triple(...)
    additive_group_lemmas::lemma_add_zero_left::<T>(triple(ba, ca, ed));
    //  triple(ba, ca, ed) ≡ 0
    T::axiom_eqv_symmetric(T::zero().add(triple(ba, ca, ed)), triple(ba, ca, ed));
    T::axiom_eqv_transitive(
        triple(ba, ca, ed), T::zero().add(triple(ba, ca, ed)), T::zero(),
    );

    //  (4) t * triple(ba,ca,ed) ≡ t * 0 ≡ 0
    T::axiom_mul_commutative(t, triple(ba, ca, ed));
    T::axiom_mul_congruence_left(triple(ba, ca, ed), T::zero(), t);
    T::axiom_eqv_transitive(
        t.mul(triple(ba, ca, ed)), triple(ba, ca, ed).mul(t), T::zero().mul(t),
    );
    ring_lemmas::lemma_mul_zero_left::<T>(t);
    T::axiom_eqv_transitive(
        t.mul(triple(ba, ca, ed)), T::zero().mul(t), T::zero(),
    );

    //  (5) triple(ba, ca, w) ≡ t * triple(ba, ca, ed) ≡ 0
    T::axiom_eqv_transitive(
        triple(ba, ca, w), t.mul(triple(ba, ca, ed)), T::zero(),
    );

    //  (6) orient3d(a,b,c,d) + triple(ba,ca,w) ≡ 0 + 0 ≡ 0
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

    //  (7) Final chain: orient3d(a,b,c, d+w) ≡ orient3d(...,d) + triple(...) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, add_vec3(d, w)),
        orient3d(a, b, c, d).add(triple(ba, ca, w)),
        T::zero(),
    );
}

//  =========================================================================
//  Helper: triple = orient3d difference
//  =========================================================================

///  triple(sub3(y,x), sub3(z,x), sub3(b,a)) ≡ orient3d(x,y,z,b) - orient3d(x,y,z,a).
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

    //  orient3d(x,y,z, add_vec3(a, ba)) ≡ oa + tb  [linear_last]
    lemma_orient3d_linear_last::<T>(x, y, z, a, ba);
    //  orient3d(x,y,z, add_vec3(a, ba)) ≡ ob  [shift_endpoint]
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, b);
    //  oa + tb ≡ ob  [combine]
    T::axiom_eqv_symmetric(
        orient3d(x, y, z, add_vec3(a, ba)),
        oa.add(tb),
    );
    T::axiom_eqv_transitive(oa.add(tb), orient3d(x, y, z, add_vec3(a, ba)), ob);

    //  oa + (ob - oa) ≡ ob  [sub_then_add_cancel + commutativity]
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(ob, oa);
    T::axiom_add_commutative(oa, ob.sub(oa));
    T::axiom_eqv_transitive(oa.add(ob.sub(oa)), ob.sub(oa).add(oa), ob);

    //  Left cancel: oa + tb ≡ ob ≡ oa + (ob - oa), so tb ≡ ob - oa.
    T::axiom_eqv_symmetric(oa.add(ob.sub(oa)), ob);
    T::axiom_eqv_transitive(oa.add(tb), ob, oa.add(ob.sub(oa)));
    additive_group_lemmas::lemma_add_left_cancel::<T>(tb, ob.sub(oa), oa);
}

//  =========================================================================
//  Helper: a + (x - y) ≡ (a - y) + x
//  =========================================================================

///  Rearrangement: a + (x - y) ≡ (a - y) + x.
pub proof fn lemma_add_sub_rearrange<T: Ring>(a: T, x: T, y: T)
    ensures
        a.add(x.sub(y)).eqv(a.sub(y).add(x)),
{
    //  a + (x - y) ≡ a + (x + (-y))  [sub_is_add_neg]
    T::axiom_sub_is_add_neg(x, y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, x.sub(y), x.add(y.neg()));
    //  ≡ (a + x) + (-y)  [assoc, symmetric]
    T::axiom_add_associative(a, x, y.neg());
    T::axiom_eqv_symmetric(a.add(x).add(y.neg()), a.add(x.add(y.neg())));
    T::axiom_eqv_transitive(a.add(x.sub(y)), a.add(x.add(y.neg())), a.add(x).add(y.neg()));
    //  ≡ (x + a) + (-y)  [commutative on inner]
    T::axiom_add_commutative(a, x);
    T::axiom_add_congruence_left(a.add(x), x.add(a), y.neg());
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), a.add(x).add(y.neg()), x.add(a).add(y.neg()),
    );
    //  ≡ x + (a + (-y))  [assoc]
    T::axiom_add_associative(x, a, y.neg());
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), x.add(a).add(y.neg()), x.add(a.add(y.neg())),
    );
    //  ≡ x + (a - y)  [reverse sub_is_add_neg]
    T::axiom_sub_is_add_neg(a, y);
    T::axiom_eqv_symmetric(a.sub(y), a.add(y.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(x, a.add(y.neg()), a.sub(y));
    T::axiom_eqv_transitive(
        a.add(x.sub(y)), x.add(a.add(y.neg())), x.add(a.sub(y)),
    );
    //  ≡ (a - y) + x  [commutative]
    T::axiom_add_commutative(x, a.sub(y));
    T::axiom_eqv_transitive(a.add(x.sub(y)), x.add(a.sub(y)), a.sub(y).add(x));
}

//  =========================================================================
//  Helper: factoring a - t*a ≡ (1 - t) * a
//  =========================================================================

///  a - t*a ≡ (1 - t) * a.
pub proof fn lemma_factor_out<T: Ring>(a: T, t: T)
    ensures
        a.sub(t.mul(a)).eqv(T::one().sub(t).mul(a)),
{
    //  (1-t)*a ≡ a*(1-t)  [commutative]
    T::axiom_mul_commutative(T::one().sub(t), a);
    //  a*(1-t) ≡ a*1 - a*t  [distributes_over_sub]
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(a, T::one(), t);
    //  Chain: (1-t)*a ≡ a*1 - a*t
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a), a.mul(T::one().sub(t)), a.mul(T::one()).sub(a.mul(t)),
    );

    //  Now show a*1 - a*t ≡ a - t*a:
    //  a*1 ≡ a
    T::axiom_mul_one_right(a);
    //  a*t ≡ t*a
    T::axiom_mul_commutative(a, t);
    //  a*1 - a*t ≡ a - t*a  by sub congruence (a.sub(b) respects eqv)
    T::axiom_sub_is_add_neg(a.mul(T::one()), a.mul(t));
    T::axiom_sub_is_add_neg(a, t.mul(a));
    T::axiom_neg_congruence(a.mul(t), t.mul(a));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.mul(T::one()), a,
        a.mul(t).neg(), t.mul(a).neg(),
    );
    //  a.mul(T::one()).add(a.mul(t).neg()) ≡ a.add(t.mul(a).neg())
    //  Convert from add_neg form to sub form:
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

    //  Chain: (1-t)*a ≡ a*1 - a*t ≡ a - t*a
    T::axiom_eqv_transitive(
        T::one().sub(t).mul(a),
        a.mul(T::one()).sub(a.mul(t)),
        a.sub(t.mul(a)),
    );
    //  Symmetric: a - t*a ≡ (1-t)*a
    T::axiom_eqv_symmetric(T::one().sub(t).mul(a), a.sub(t.mul(a)));
}

//  =========================================================================
//  Helper: right-distributive of sub: p*r - q*r ≡ (p-q)*r
//  =========================================================================

///  (p - q) * r ≡ p*r - q*r  (right-distributes over sub).
pub proof fn lemma_right_distributes_over_sub<T: Ring>(p: T, q: T, r: T)
    ensures
        p.mul(r).sub(q.mul(r)).eqv(p.sub(q).mul(r)),
{
    //  (p-q)*r ≡ r*(p-q) ≡ r*p - r*q ≡ p*r - q*r
    T::axiom_mul_commutative(p.sub(q), r);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(r, p, q);
    T::axiom_eqv_transitive(p.sub(q).mul(r), r.mul(p.sub(q)), r.mul(p).sub(r.mul(q)));
    //  r*p ≡ p*r, r*q ≡ q*r
    T::axiom_mul_commutative(r, p);
    T::axiom_mul_commutative(r, q);
    additive_group_lemmas::lemma_sub_congruence::<T>(r.mul(p), p.mul(r), r.mul(q), q.mul(r));
    T::axiom_eqv_transitive(p.sub(q).mul(r), r.mul(p).sub(r.mul(q)), p.mul(r).sub(q.mul(r)));
    //  Symmetric: p*r - q*r ≡ (p-q)*r
    T::axiom_eqv_symmetric(p.sub(q).mul(r), p.mul(r).sub(q.mul(r)));
}

//  =========================================================================
//  Helper: weighted sum rearrangement
//  =========================================================================

///  a + α*(b-a) + β*(c-a) ≡ (1-α-β)*a + α*b + β*c
pub proof fn lemma_weighted_sum_rearrange<T: Ring>(a: T, b: T, c: T, alpha: T, beta: T)
    ensures
        a.add(alpha.mul(b.sub(a))).add(beta.mul(c.sub(a)))
            .eqv(
                T::one().sub(alpha).sub(beta).mul(a)
                    .add(alpha.mul(b))
                    .add(beta.mul(c))
            ),
{
    let s0 = a.add(alpha.mul(b.sub(a))).add(beta.mul(c.sub(a)));

    //  Step 1: α*(b-a) ≡ α*b - α*a  [distribute]
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(alpha, b, a);

    //  Step 2: a + α*(b-a) ≡ a + (α*b - α*a) ≡ (a - α*a) + α*b  [rearrange]
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, alpha.mul(b.sub(a)), alpha.mul(b).sub(alpha.mul(a)),
    );
    let s1_inner = a.add(alpha.mul(b).sub(alpha.mul(a)));
    lemma_add_sub_rearrange::<T>(a, alpha.mul(b), alpha.mul(a));
    T::axiom_eqv_transitive(a.add(alpha.mul(b.sub(a))), s1_inner, a.sub(alpha.mul(a)).add(alpha.mul(b)));

    //  Step 3: a - α*a ≡ (1-α)*a  [factor out]
    lemma_factor_out::<T>(a, alpha);
    let u1 = T::one().sub(alpha);
    T::axiom_add_congruence_left(a.sub(alpha.mul(a)), u1.mul(a), alpha.mul(b));
    T::axiom_eqv_transitive(
        a.add(alpha.mul(b.sub(a))),
        a.sub(alpha.mul(a)).add(alpha.mul(b)),
        u1.mul(a).add(alpha.mul(b)),
    );
    //  Now: a + α*(b-a) ≡ (1-α)*a + α*b

    //  Step 4: Lift to outer: s0 ≡ ((1-α)*a + α*b) + β*(c-a)
    let m = u1.mul(a).add(alpha.mul(b));
    T::axiom_add_congruence_left(a.add(alpha.mul(b.sub(a))), m, beta.mul(c.sub(a)));
    //  s0 IS a.add(alpha.mul(b.sub(a))).add(beta.mul(c.sub(a))), so
    //  add_congruence_left directly gives s0.eqv(m.add(beta.mul(c.sub(a)))).

    //  Step 5: β*(c-a) ≡ β*c - β*a  [distribute]
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(beta, c, a);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        m, beta.mul(c.sub(a)), beta.mul(c).sub(beta.mul(a)),
    );
    T::axiom_eqv_transitive(s0, m.add(beta.mul(c.sub(a))), m.add(beta.mul(c).sub(beta.mul(a))));

    //  Step 6: m + (β*c - β*a) ≡ (m - β*a) + β*c  [rearrange]
    lemma_add_sub_rearrange::<T>(m, beta.mul(c), beta.mul(a));
    T::axiom_eqv_transitive(s0, m.add(beta.mul(c).sub(beta.mul(a))), m.sub(beta.mul(a)).add(beta.mul(c)));

    //  Step 7: m - β*a = ((1-α)*a + α*b) - β*a ≡ ((1-α)*a - β*a) + α*b
    crate::intersection3d::lemma_add_sub_rearrange::<T>(u1.mul(a), alpha.mul(b), beta.mul(a));
    T::axiom_add_congruence_left(m.sub(beta.mul(a)), u1.mul(a).sub(beta.mul(a)).add(alpha.mul(b)), beta.mul(c));
    T::axiom_eqv_transitive(s0,
        m.sub(beta.mul(a)).add(beta.mul(c)),
        u1.mul(a).sub(beta.mul(a)).add(alpha.mul(b)).add(beta.mul(c)));

    //  Step 8: (1-α)*a - β*a ≡ ((1-α) - β)*a = (1-α-β)*a  [right-distributes]
    lemma_right_distributes_over_sub::<T>(u1, beta, a);
    let u = u1.sub(beta);  //  = T::one().sub(alpha).sub(beta)
    //  Lift through +α*b: (u1*a - β*a) + α*b ≡ u*a + α*b
    T::axiom_add_congruence_left(u1.mul(a).sub(beta.mul(a)), u.mul(a), alpha.mul(b));
    //  Lift through +β*c: (...+α*b) + β*c ≡ (u*a+α*b) + β*c
    T::axiom_add_congruence_left(
        u1.mul(a).sub(beta.mul(a)).add(alpha.mul(b)),
        u.mul(a).add(alpha.mul(b)),
        beta.mul(c),
    );
    T::axiom_eqv_transitive(s0,
        u1.mul(a).sub(beta.mul(a)).add(alpha.mul(b)).add(beta.mul(c)),
        u.mul(a).add(alpha.mul(b)).add(beta.mul(c)));
}

//  =========================================================================
//  Helper: orient3d positive on affine combination
//  =========================================================================

///  If orient3d(x,y,z,_) is strictly positive at all three vertices a, b, c,
///  and α ≥ 0, β ≥ 0, 1-α-β ≥ 0, then orient3d is positive at the
///  affine combination a + α*(b-a) + β*(c-a).
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

    //  --- Algebraic identity: orient3d(p) ≡ u*oa + alpha*ob + beta*oc ---
    //  Via orient3d_affine_combination + triple_is_orient_diff + rearrangement.
    lemma_orient3d_weighted_form::<T>(x, y, z, a, b, c, alpha, beta);

    //  --- Positivity: u*oa + alpha*ob + beta*oc > 0 ---
    //  0 ≤ oa, ob, oc from 0 < ...
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oa);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), ob);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oc);
    //  Each product ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(u, oa);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(alpha, ob);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(beta, oc);

    //  Case split: at least one weight > 0.
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), u);
    if T::zero().lt(u) {
        ordered_field_lemmas::lemma_mul_pos_pos::<T>(u, oa);
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(u.mul(oa), alpha.mul(ob));
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
            u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
        );
    } else {
        //  u ≡ 0.
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), alpha);
        if T::zero().lt(alpha) {
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(alpha, ob);
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(u.mul(oa), alpha.mul(ob));
            ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
                u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
            );
        } else {
            //  alpha ≡ 0 and u ≡ 0 → beta > 0 (since if beta ≡ 0 too, then
            //  u = 1-0-0 = 1, but u ≡ 0 contradicts 0 < 1).
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), beta);
            if T::zero().eqv(beta) {
                //  Contradiction: 0≡u, 0≡alpha, 0≡beta → u≡1, but 0≡u and 0<1.
                T::axiom_eqv_reflexive(u);
                lemma_all_zero_contradiction::<T>(alpha, beta, u);
            }
            //  Now: !T::zero().eqv(beta) + T::zero().le(beta) → T::zero().lt(beta)
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(beta, oc);
            //  Need: u*oa + alpha*ob ≥ 0 (both nonneg from lines above)
            ordered_ring_lemmas::lemma_le_add_both::<T>(
                T::zero(), u.mul(oa), T::zero(), alpha.mul(ob),
            );
            T::axiom_add_zero_right(T::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().add(T::zero()), T::zero(), u.mul(oa).add(alpha.mul(ob)),
            );
            //  Now: 0 <= u*oa + alpha*ob and 0 < beta*oc → 0 < sum
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(
                u.mul(oa).add(alpha.mul(ob)), beta.mul(oc),
            );
        }
    }

    //  Transfer: 0 < weighted and p_orient ≡ weighted → 0 < p_orient
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_symmetric(p_orient, weighted);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), weighted, p_orient,
    );
}

//  =========================================================================
//  Helper: algebraic identity for weighted form
//  =========================================================================

///  orient3d(x,y,z, a + alpha*(b-a) + beta*(c-a))
///    ≡ (1-alpha-beta)*orient3d(x,y,z,a) + alpha*orient3d(x,y,z,b) + beta*orient3d(x,y,z,c)
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
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let oc = orient3d(x, y, z, c);
    let tb = triple(sub3(y, x), sub3(z, x), sub3(b, a));
    let tc = triple(sub3(y, x), sub3(z, x), sub3(c, a));
    let p_orient = orient3d(x, y, z,
        add_vec3(a, scale(alpha, sub3(b, a)).add(scale(beta, sub3(c, a)))));
    let target = T::one().sub(alpha).sub(beta).mul(oa)
        .add(alpha.mul(ob)).add(beta.mul(oc));

    //  Step 1: p_orient ≡ oa + α*tb + β*tc
    lemma_orient3d_affine_combination::<T>(x, y, z, a, b, c, alpha, beta);
    let form1 = oa.add(alpha.mul(tb)).add(beta.mul(tc));

    //  Step 2: tb ≡ ob - oa, tc ≡ oc - oa
    lemma_triple_is_orient_diff::<T>(x, y, z, a, b);
    lemma_triple_is_orient_diff::<T>(x, y, z, a, c);

    //  Step 3: α*tb ≡ α*(ob-oa), β*tc ≡ β*(oc-oa)
    ring_lemmas::lemma_mul_congruence_right::<T>(alpha, tb, ob.sub(oa));
    ring_lemmas::lemma_mul_congruence_right::<T>(beta, tc, oc.sub(oa));

    //  Step 4: form1 ≡ oa + α*(ob-oa) + β*(oc-oa)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oa, alpha.mul(tb), alpha.mul(ob.sub(oa)),
    );
    T::axiom_add_congruence_left(
        oa.add(alpha.mul(tb)), oa.add(alpha.mul(ob.sub(oa))), beta.mul(tc),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        oa.add(alpha.mul(ob.sub(oa))), beta.mul(tc), beta.mul(oc.sub(oa)),
    );
    let form2 = oa.add(alpha.mul(ob.sub(oa))).add(beta.mul(oc.sub(oa)));
    T::axiom_eqv_transitive(form1,
        oa.add(alpha.mul(ob.sub(oa))).add(beta.mul(tc)), form2);

    //  Step 5: form2 ≡ target via weighted_sum_rearrange
    lemma_weighted_sum_rearrange::<T>(oa, ob, oc, alpha, beta);

    //  Chain: p_orient ≡ form1 ≡ form2 ≡ target
    T::axiom_eqv_transitive(p_orient, form1, form2);
    T::axiom_eqv_transitive(p_orient, form2, target);
}

//  =========================================================================
//  Helper: contradiction when all weights are zero but should sum to 1
//  =========================================================================

///  If alpha ≡ 0, beta ≡ 0, and u = 1-alpha-beta, then u cannot be ≡ 0
///  (because that would require 1 ≡ 0, contradicting 0 < 1).
pub proof fn lemma_all_zero_contradiction<T: OrderedField>(alpha: T, beta: T, u: T)
    requires
        T::zero().eqv(alpha),
        T::zero().eqv(beta),
        T::zero().eqv(u),
        u.eqv(T::one().sub(alpha).sub(beta)),
    ensures
        false,
{
    //  Step 1: alpha ≡ 0, beta ≡ 0 (symmetric of given)
    T::axiom_eqv_symmetric(T::zero(), alpha);
    T::axiom_eqv_symmetric(T::zero(), beta);
    //  Step 2: 1 - alpha ≡ 1 - 0
    T::axiom_eqv_reflexive(T::one());
    additive_group_lemmas::lemma_sub_congruence::<T>(T::one(), T::one(), alpha, T::zero());
    //  Step 3: 1 - 0 ≡ 1 (via sub_is_add_neg + neg_zero + add_zero_right)
    T::axiom_sub_is_add_neg(T::one(), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(T::one(), T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::zero()), T::one().add(T::zero().neg()), T::one().add(T::zero()));
    T::axiom_add_zero_right(T::one());
    T::axiom_eqv_transitive(T::one().sub(T::zero()), T::one().add(T::zero()), T::one());
    //  Step 4: 1 - alpha ≡ 1 (transitive)
    T::axiom_eqv_transitive(T::one().sub(alpha), T::one().sub(T::zero()), T::one());
    //  Step 5: (1-alpha) - beta ≡ 1 - 0
    T::axiom_eqv_reflexive(T::one().sub(alpha));
    additive_group_lemmas::lemma_sub_congruence::<T>(T::one().sub(alpha), T::one(), beta, T::zero());
    //  Step 6: 1 - alpha - beta ≡ 1 (transitive through 1 - 0)
    T::axiom_eqv_transitive(T::one().sub(alpha).sub(beta), T::one().sub(T::zero()), T::one());
    //  Step 7: u ≡ 1 (from u ≡ 1-alpha-beta ≡ 1)
    T::axiom_eqv_transitive(u, T::one().sub(alpha).sub(beta), T::one());
    //  Step 8: 0 ≡ 1 (from 0 ≡ u ≡ 1)
    T::axiom_eqv_transitive(T::zero(), u, T::one());
    //  Step 9: But 0 < 1 implies !(0 ≡ 1). Contradiction.
    ordered_ring_lemmas::lemma_zero_lt_one::<T>();
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), T::one());
}

//  =========================================================================
//  Helper: weighted additive identity (pure algebra)
//  =========================================================================

///  Pure algebraic identity: given u + v + w ≡ 1, a + b1 ≡ r, a + b2 ≡ s,
///  then a + v*b1 + w*b2 ≡ u*a + v*r + w*s.
///
///  Used to convert orient3d_affine_combination output (base + weighted triples)
///  into the weighted vertex sum, and to match q's components with barycentric
///  reconstruction of p's components.
proof fn lemma_weighted_additive_identity<T: Ring>(
    a: T, b1: T, b2: T, r: T, s: T, u: T, v: T, w: T,
)
    requires
        u.add(v).add(w).eqv(T::one()),
        a.add(b1).eqv(r),
        a.add(b2).eqv(s),
    ensures
        a.add(v.mul(b1)).add(w.mul(b2)).eqv(u.mul(a).add(v.mul(r)).add(w.mul(s)))
{
    let ua = u.mul(a);
    let va = v.mul(a);
    let wa = w.mul(a);
    let vb1 = v.mul(b1);
    let wb2 = w.mul(b2);

    //  --- Phase 1: a ≡ ua + va + wa ---
    //  1*a ≡ a
    ring_lemmas::lemma_mul_one_left::<T>(a);
    //  (u+v+w)*a ≡ 1*a (by congruence with u+v+w ≡ 1)
    T::axiom_eqv_symmetric(u.add(v).add(w), T::one());
    T::axiom_eqv_reflexive(a);
    ring_lemmas::lemma_mul_congruence::<T>(T::one(), u.add(v).add(w), a, a);
    //  Chain: a ← 1*a ← (u+v+w)*a
    T::axiom_eqv_symmetric(T::one().mul(a), a);
    T::axiom_eqv_transitive(a, T::one().mul(a), u.add(v).add(w).mul(a));
    //  a ≡ (u+v+w)*a

    //  Expand ((u+v)+w)*a ≡ (u+v)*a + w*a
    ring_lemmas::lemma_mul_distributes_right::<T>(u.add(v), w, a);
    //  Expand (u+v)*a ≡ u*a + v*a
    ring_lemmas::lemma_mul_distributes_right::<T>(u, v, a);

    //  Substitute into (u+v)*a + wa: replace (u+v)*a by ua + va
    T::axiom_eqv_reflexive(wa);
    additive_group_lemmas::lemma_add_congruence::<T>(
        u.add(v).mul(a), ua.add(va), wa, wa
    );
    //  (u+v)*a + wa ≡ (ua + va) + wa

    //  Chain: (u+v+w)*a ≡ (u+v)*a + wa ≡ ua + va + wa
    T::axiom_eqv_transitive(
        u.add(v).add(w).mul(a),
        u.add(v).mul(a).add(wa),
        ua.add(va).add(wa)
    );
    //  Chain: a ≡ (u+v+w)*a ≡ ua + va + wa
    T::axiom_eqv_transitive(a, u.add(v).add(w).mul(a), ua.add(va).add(wa));
    //  a ≡ ua + va + wa

    //  --- Phase 2: Substitute a into LHS ---
    //  LHS = a + vb1 + wb2
    //  Replace a by ua + va + wa:
    T::axiom_eqv_reflexive(vb1);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a, ua.add(va).add(wa), vb1, vb1
    );
    //  a + vb1 ≡ (ua + va + wa) + vb1
    T::axiom_eqv_reflexive(wb2);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(vb1), ua.add(va).add(wa).add(vb1), wb2, wb2
    );
    //  LHS ≡ (ua + va + wa + vb1) + wb2
    //  = ua.add(va).add(wa).add(vb1).add(wb2)

    //  --- Phase 3: Swap wa and vb1 ---
    //  Need: (ua + va) + wa + vb1 → (ua + va) + vb1 + wa
    //  (Actually swapping to get wa next to wb2 won't help. We want to group
    //  va with vb1 and wa with wb2. Swap wa past vb1.)
    //  ((ua + va) + wa) + vb1 → ((ua + va) + vb1) + wa... no we want
    //  the opposite: put vb1 BEFORE wa.
    //  Current: ua.add(va).add(wa).add(vb1)
    //  Want: ua.add(va).add(vb1).add(wa)
    //  Swap wa and vb1:
    T::axiom_add_associative(ua.add(va), wa, vb1);
    //  (ua + va + wa) + vb1 ≡ (ua + va) + (wa + vb1)
    T::axiom_add_commutative(wa, vb1);
    //  wa + vb1 ≡ vb1 + wa
    T::axiom_eqv_reflexive(ua.add(va));
    additive_group_lemmas::lemma_add_congruence::<T>(
        ua.add(va), ua.add(va), wa.add(vb1), vb1.add(wa)
    );
    //  (ua + va) + (wa + vb1) ≡ (ua + va) + (vb1 + wa)
    T::axiom_add_associative(ua.add(va), vb1, wa);
    T::axiom_eqv_symmetric(
        ua.add(va).add(vb1).add(wa),
        ua.add(va).add(vb1.add(wa))
    );
    //  (ua + va) + (vb1 + wa) ≡ (ua + va) + vb1 + wa

    //  Chain the swap: ua+va+wa+vb1 ≡ ... ≡ ua+va+vb1+wa
    T::axiom_eqv_transitive(
        ua.add(va).add(wa).add(vb1),
        ua.add(va).add(wa.add(vb1)),
        ua.add(va).add(vb1.add(wa))
    );
    T::axiom_eqv_transitive(
        ua.add(va).add(wa).add(vb1),
        ua.add(va).add(vb1.add(wa)),
        ua.add(va).add(vb1).add(wa)
    );
    //  ua.add(va).add(wa).add(vb1) ≡ ua.add(va).add(vb1).add(wa)

    //  Propagate swap to include wb2:
    T::axiom_add_congruence_left(
        ua.add(va).add(wa).add(vb1),
        ua.add(va).add(vb1).add(wa),
        wb2
    );
    //  ua.add(va).add(wa).add(vb1).add(wb2)
    //    ≡ ua.add(va).add(vb1).add(wa).add(wb2)
    let swapped = ua.add(va).add(vb1).add(wa).add(wb2);

    //  --- Phase 4: Group (va + vb1) → v*r and (wa + wb2) → w*s ---
    //  First group va + vb1 = v*a + v*b1 = v*(a + b1) = v*r
    T::axiom_mul_distributes_left(v, a, b1);
    T::axiom_eqv_symmetric(va.add(vb1), v.mul(a.add(b1)));
    //  va + vb1 ≡ v*(a + b1)
    ring_lemmas::lemma_mul_congruence_right::<T>(v, a.add(b1), r);
    //  v*(a + b1) ≡ v*r
    T::axiom_eqv_transitive(va.add(vb1), v.mul(a.add(b1)), v.mul(r));
    //  va + vb1 ≡ v*r

    //  Reassociate: ua + va + vb1 = ua + (va + vb1)
    T::axiom_add_associative(ua, va, vb1);
    //  (ua + va) + vb1 ≡ ua + (va + vb1)
    //  Replace (va + vb1) by v*r:
    T::axiom_eqv_reflexive(ua);
    additive_group_lemmas::lemma_add_congruence::<T>(
        ua, ua, va.add(vb1), v.mul(r)
    );
    //  ua + (va + vb1) ≡ ua + v*r
    T::axiom_eqv_transitive(
        ua.add(va).add(vb1),
        ua.add(va.add(vb1)),
        ua.add(v.mul(r))
    );
    //  (ua + va) + vb1 ≡ ua + v*r

    //  Now group wa + wb2 = w*s (same argument)
    T::axiom_mul_distributes_left(w, a, b2);
    T::axiom_eqv_symmetric(wa.add(wb2), w.mul(a.add(b2)));
    ring_lemmas::lemma_mul_congruence_right::<T>(w, a.add(b2), s);
    T::axiom_eqv_transitive(wa.add(wb2), w.mul(a.add(b2)), w.mul(s));
    //  wa + wb2 ≡ w*s

    //  Reassociate swapped: ua + va + vb1 + wa + wb2
    //  = ((ua + va + vb1) + wa) + wb2
    //  Group last two: ... + wa + wb2 = ... + (wa + wb2)
    T::axiom_add_associative(ua.add(va).add(vb1), wa, wb2);
    //  (... + wa) + wb2 ≡ ... + (wa + wb2)
    //  Replace (wa + wb2) by w*s:
    T::axiom_eqv_reflexive(ua.add(va).add(vb1));
    additive_group_lemmas::lemma_add_congruence::<T>(
        ua.add(va).add(vb1), ua.add(va).add(vb1),
        wa.add(wb2), w.mul(s)
    );
    //  (ua + va + vb1) + (wa + wb2) ≡ (ua + va + vb1) + w*s
    T::axiom_eqv_transitive(
        swapped,
        ua.add(va).add(vb1).add(wa.add(wb2)),
        ua.add(va).add(vb1).add(w.mul(s))
    );
    //  swapped ≡ (ua + va + vb1) + w*s

    //  Replace (ua + va + vb1) by (ua + v*r):
    T::axiom_eqv_reflexive(w.mul(s));
    additive_group_lemmas::lemma_add_congruence::<T>(
        ua.add(va).add(vb1), ua.add(v.mul(r)),
        w.mul(s), w.mul(s)
    );
    //  (ua + va + vb1) + w*s ≡ (ua + v*r) + w*s = RHS
    T::axiom_eqv_transitive(
        swapped,
        ua.add(va).add(vb1).add(w.mul(s)),
        ua.add(v.mul(r)).add(w.mul(s))
    );
    //  swapped ≡ RHS

    //  --- Phase 5: Chain LHS ≡ swapped ≡ RHS ---
    //  From Phase 2: LHS ≡ ua.add(va).add(wa).add(vb1).add(wb2)
    //  From Phase 3: that ≡ swapped
    //  From Phase 4: swapped ≡ RHS
    let flat5 = ua.add(va).add(wa).add(vb1).add(wb2);
    T::axiom_eqv_transitive(
        a.add(vb1).add(wb2), flat5, swapped
    );
    T::axiom_eqv_transitive(
        a.add(vb1).add(wb2), swapped, ua.add(v.mul(r)).add(w.mul(s))
    );
    //  LHS ≡ RHS
}

//  =========================================================================
//  Helper: scalar affine combination component identity
//  =========================================================================

///  For a scalar component of q = a + v*(b-a) + w*(c-a),
///  shows a_c + (v*(b_c - a_c) + w*(c_c - a_c)) ≡ u*a_c + v*b_c + w*c_c.
proof fn lemma_affine_combo_component<T: Ring>(
    a_c: T, b_c: T, c_c: T, u: T, v: T, w: T,
)
    requires u.add(v).add(w).eqv(T::one()),
    ensures
        a_c.add(v.mul(b_c.sub(a_c)).add(w.mul(c_c.sub(a_c))))
            .eqv(u.mul(a_c).add(v.mul(b_c)).add(w.mul(c_c)))
{
    let ba = b_c.sub(a_c);
    let ca = c_c.sub(a_c);

    //  a_c + ba ≡ b_c
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(b_c, a_c);
    T::axiom_add_commutative(ba, a_c);
    T::axiom_eqv_symmetric(ba.add(a_c), a_c.add(ba));
    T::axiom_eqv_transitive(a_c.add(ba), ba.add(a_c), b_c);

    //  a_c + ca ≡ c_c
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(c_c, a_c);
    T::axiom_add_commutative(ca, a_c);
    T::axiom_eqv_symmetric(ca.add(a_c), a_c.add(ca));
    T::axiom_eqv_transitive(a_c.add(ca), ca.add(a_c), c_c);

    //  weighted identity: (a_c + v*ba) + w*ca ≡ u*a_c + v*b_c + w*c_c
    lemma_weighted_additive_identity::<T>(a_c, ba, ca, b_c, c_c, u, v, w);

    //  associativity: (a_c + v*ba) + w*ca ≡ a_c + (v*ba + w*ca)
    T::axiom_add_associative(a_c, v.mul(ba), w.mul(ca));
    T::axiom_eqv_symmetric(
        a_c.add(v.mul(ba)).add(w.mul(ca)),
        a_c.add(v.mul(ba).add(w.mul(ca)))
    );
    T::axiom_eqv_transitive(
        a_c.add(v.mul(ba).add(w.mul(ca))),
        a_c.add(v.mul(ba)).add(w.mul(ca)),
        u.mul(a_c).add(v.mul(b_c)).add(w.mul(c_c))
    );
}

//  =========================================================================
//  Helper: projection injectivity (coplanar + matching 2D projection → 3D equal)
//  =========================================================================

///  Projection injectivity: for a coplanar point p with 2D barycentric reconstruction
///  matching the affine combination q = a + v*(b-a) + w*(c-a), sub3(p,q) is the zero vector.
///
///  The "kept" components of p match q by the barycentric reconstruction equalities.
///  The "dropped" component follows from: both coplanar → triple(ba,ca,sub3(p,q))≡0,
///  cyclic to dot(d,N)≡0 with two zero components → N_dropped * d_dropped ≡ 0,
///  field cancellation (N_dropped ≢ 0) → d_dropped ≡ 0.
proof fn lemma_projection_injectivity_zero<T: OrderedField>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
    u: T, v: T, w: T, axis: int,
)
    requires
        orient3d(a, b, c, p).eqv(T::zero()),
        u.add(v).add(w).eqv(T::one()),
        0 <= axis <= 2,
        axis == 0 ==> !triangle_normal(a, b, c).x.eqv(T::zero()),
        axis == 1 ==> !triangle_normal(a, b, c).y.eqv(T::zero()),
        axis == 2 ==> !triangle_normal(a, b, c).z.eqv(T::zero()),
        axis == 0 ==> (
            p.y.eqv(u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y))) &&
            p.z.eqv(u.mul(a.z).add(v.mul(b.z)).add(w.mul(c.z)))
        ),
        axis == 1 ==> (
            p.x.eqv(u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x))) &&
            p.z.eqv(u.mul(a.z).add(v.mul(b.z)).add(w.mul(c.z)))
        ),
        axis == 2 ==> (
            p.x.eqv(u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x))) &&
            p.y.eqv(u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)))
        ),
    ensures ({
        let q = add_vec3(a, scale(v, sub3(b, a)).add(scale(w, sub3(c, a))));
        &&& sub3(p, q).x.eqv(T::zero())
        &&& sub3(p, q).y.eqv(T::zero())
        &&& sub3(p, q).z.eqv(T::zero())
    })
{
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let q = add_vec3(a, scale(v, ba).add(scale(w, ca)));
    let d = sub3(p, q);
    let n = triangle_normal(a, b, c);

    //  ---- Phase 1: q components ≡ u*a + v*b + w*c ----
    lemma_affine_combo_component::<T>(a.x, b.x, c.x, u, v, w);
    lemma_affine_combo_component::<T>(a.y, b.y, c.y, u, v, w);
    lemma_affine_combo_component::<T>(a.z, b.z, c.z, u, v, w);

    //  ---- Phase 2: orient3d(a,b,c,q) ≡ 0 ----
    additive_group_lemmas::lemma_sub_self::<T>(a.x);
    additive_group_lemmas::lemma_sub_self::<T>(a.y);
    additive_group_lemmas::lemma_sub_self::<T>(a.z);
    crate::insphere::lemma_triple_zero_third::<T>(ba, ca, sub3(a, a));

    lemma_triple_self_zero_13::<T>(ba, ca);
    lemma_triple_self_zero_23::<T>(ba, ca);

    ring_lemmas::lemma_mul_congruence_right::<T>(v, triple(ba, ca, ba), T::zero());
    T::axiom_mul_zero_right(v);
    T::axiom_eqv_transitive(v.mul(triple(ba, ca, ba)), v.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(w, triple(ba, ca, ca), T::zero());
    T::axiom_mul_zero_right(w);
    T::axiom_eqv_transitive(w.mul(triple(ba, ca, ca)), w.mul(T::zero()), T::zero());

    let oaa = orient3d(a, b, c, a);
    let vt = v.mul(triple(ba, ca, ba));
    let wt = w.mul(triple(ba, ca, ca));
    additive_group_lemmas::lemma_add_congruence::<T>(oaa, T::zero(), vt, T::zero());
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(oaa.add(vt), T::zero().add(T::zero()), T::zero());
    additive_group_lemmas::lemma_add_congruence::<T>(oaa.add(vt), T::zero(), wt, T::zero());
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(oaa.add(vt).add(wt), T::zero().add(T::zero()), T::zero());

    lemma_orient3d_affine_combination::<T>(a, b, c, a, b, c, v, w);
    T::axiom_eqv_transitive(orient3d(a, b, c, q), oaa.add(vt).add(wt), T::zero());

    //  ---- Phase 3: triple(ba, ca, d) ≡ 0 ----
    let td = triple(ba, ca, d);
    let oq = orient3d(a, b, c, q);
    lemma_orient3d_linear_last::<T>(a, b, c, q, d);
    lemma_orient3d_shift_endpoint::<T>(a, b, c, q, p);
    let oq_d = orient3d(a, b, c, add_vec3(q, d));
    T::axiom_eqv_transitive(oq_d, orient3d(a, b, c, p), T::zero());
    T::axiom_eqv_symmetric(oq_d, oq.add(td));
    T::axiom_eqv_transitive(oq.add(td), oq_d, T::zero());
    T::axiom_eqv_reflexive(td);
    T::axiom_eqv_symmetric(oq, T::zero());
    additive_group_lemmas::lemma_add_congruence::<T>(T::zero(), oq, td, td);
    additive_group_lemmas::lemma_add_zero_left::<T>(td);
    T::axiom_eqv_symmetric(T::zero().add(td), td);
    T::axiom_eqv_transitive(td, T::zero().add(td), oq.add(td));
    T::axiom_eqv_transitive(td, oq.add(td), T::zero());

    //  ---- Phase 4: dot(d, N) ≡ 0 via cyclic ----
    //  triple(ba,ca,d) ≡ triple(d,ba,ca) = dot(d, cross(ba,ca)) = dot(d, N)
    lemma_triple_cyclic::<T>(ba, ca, d);
    lemma_triple_cyclic::<T>(ca, d, ba);
    T::axiom_eqv_transitive(td, triple(ca, d, ba), triple(d, ba, ca));
    T::axiom_eqv_symmetric(td, triple(d, ba, ca));
    T::axiom_eqv_transitive(triple(d, ba, ca), td, T::zero());
    //  dot(d, N) = d.x*n.x + d.y*n.y + d.z*n.z ≡ 0

    //  ---- Phase 5: per-axis case split ----
    if axis == 0 {
        //  Kept: y, z. Dropped: x
        let target_y = u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y));
        let target_z = u.mul(a.z).add(v.mul(b.z)).add(w.mul(c.z));

        //  d.y ≡ 0: p.y ≡ target_y ≡ q.y → sub ≡ 0
        T::axiom_eqv_symmetric(q.y, target_y);
        T::axiom_eqv_transitive(p.y, target_y, q.y);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.y, q.y);
        //  d.z ≡ 0
        T::axiom_eqv_symmetric(q.z, target_z);
        T::axiom_eqv_transitive(p.z, target_z, q.z);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.z, q.z);

        //  d.y*n.y ≡ 0
        T::axiom_mul_congruence_left(d.y, T::zero(), n.y);
        ring_lemmas::lemma_mul_zero_left::<T>(n.y);
        T::axiom_eqv_transitive(d.y.mul(n.y), T::zero().mul(n.y), T::zero());
        //  d.z*n.z ≡ 0
        T::axiom_mul_congruence_left(d.z, T::zero(), n.z);
        ring_lemmas::lemma_mul_zero_left::<T>(n.z);
        T::axiom_eqv_transitive(d.z.mul(n.z), T::zero().mul(n.z), T::zero());

        //  dot(d,N) ≡ d.x*n.x
        T::axiom_eqv_reflexive(d.x.mul(n.x));
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x), d.x.mul(n.x), d.y.mul(n.y), T::zero());
        T::axiom_add_zero_right(d.x.mul(n.x));
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)),
            d.x.mul(n.x).add(T::zero()), d.x.mul(n.x));
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x).add(d.y.mul(n.y)), d.x.mul(n.x),
            d.z.mul(n.z), T::zero());
        T::axiom_add_zero_right(d.x.mul(n.x));
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            d.x.mul(n.x).add(T::zero()), d.x.mul(n.x));

        //  d.x*n.x ≡ 0
        T::axiom_eqv_symmetric(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            d.x.mul(n.x));
        T::axiom_eqv_transitive(d.x.mul(n.x),
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            T::zero());

        //  Field cancel: n.x*d.x ≡ n.x*0, n.x ≢ 0 → d.x ≡ 0
        T::axiom_mul_commutative(n.x, d.x);
        T::axiom_eqv_transitive(n.x.mul(d.x), d.x.mul(n.x), T::zero());
        T::axiom_mul_zero_right(n.x);
        T::axiom_eqv_symmetric(n.x.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(n.x.mul(d.x), T::zero(), n.x.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(d.x, T::zero(), n.x);
    } else if axis == 1 {
        //  Kept: x, z. Dropped: y
        let target_x = u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x));
        let target_z = u.mul(a.z).add(v.mul(b.z)).add(w.mul(c.z));

        //  d.x ≡ 0
        T::axiom_eqv_symmetric(q.x, target_x);
        T::axiom_eqv_transitive(p.x, target_x, q.x);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.x, q.x);
        //  d.z ≡ 0
        T::axiom_eqv_symmetric(q.z, target_z);
        T::axiom_eqv_transitive(p.z, target_z, q.z);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.z, q.z);

        //  d.x*n.x ≡ 0
        T::axiom_mul_congruence_left(d.x, T::zero(), n.x);
        ring_lemmas::lemma_mul_zero_left::<T>(n.x);
        T::axiom_eqv_transitive(d.x.mul(n.x), T::zero().mul(n.x), T::zero());
        //  d.z*n.z ≡ 0
        T::axiom_mul_congruence_left(d.z, T::zero(), n.z);
        ring_lemmas::lemma_mul_zero_left::<T>(n.z);
        T::axiom_eqv_transitive(d.z.mul(n.z), T::zero().mul(n.z), T::zero());

        //  dot(d,N) ≡ d.y*n.y: first term zero
        T::axiom_eqv_reflexive(d.y.mul(n.y));
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x), T::zero(), d.y.mul(n.y), d.y.mul(n.y));
        additive_group_lemmas::lemma_add_zero_left::<T>(d.y.mul(n.y));
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)),
            T::zero().add(d.y.mul(n.y)), d.y.mul(n.y));
        //  third term zero
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x).add(d.y.mul(n.y)), d.y.mul(n.y),
            d.z.mul(n.z), T::zero());
        T::axiom_add_zero_right(d.y.mul(n.y));
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            d.y.mul(n.y).add(T::zero()), d.y.mul(n.y));

        //  d.y*n.y ≡ 0
        T::axiom_eqv_symmetric(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            d.y.mul(n.y));
        T::axiom_eqv_transitive(d.y.mul(n.y),
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            T::zero());

        //  Field cancel: n.y*d.y ≡ n.y*0, n.y ≢ 0 → d.y ≡ 0
        T::axiom_mul_commutative(n.y, d.y);
        T::axiom_eqv_transitive(n.y.mul(d.y), d.y.mul(n.y), T::zero());
        T::axiom_mul_zero_right(n.y);
        T::axiom_eqv_symmetric(n.y.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(n.y.mul(d.y), T::zero(), n.y.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(d.y, T::zero(), n.y);
    } else {
        //  axis == 2: Kept: x, y. Dropped: z
        let target_x = u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x));
        let target_y = u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y));

        //  d.x ≡ 0
        T::axiom_eqv_symmetric(q.x, target_x);
        T::axiom_eqv_transitive(p.x, target_x, q.x);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.x, q.x);
        //  d.y ≡ 0
        T::axiom_eqv_symmetric(q.y, target_y);
        T::axiom_eqv_transitive(p.y, target_y, q.y);
        additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(p.y, q.y);

        //  d.x*n.x ≡ 0
        T::axiom_mul_congruence_left(d.x, T::zero(), n.x);
        ring_lemmas::lemma_mul_zero_left::<T>(n.x);
        T::axiom_eqv_transitive(d.x.mul(n.x), T::zero().mul(n.x), T::zero());
        //  d.y*n.y ≡ 0
        T::axiom_mul_congruence_left(d.y, T::zero(), n.y);
        ring_lemmas::lemma_mul_zero_left::<T>(n.y);
        T::axiom_eqv_transitive(d.y.mul(n.y), T::zero().mul(n.y), T::zero());

        //  dot(d,N) ≡ d.z*n.z: both first terms zero
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x), T::zero(), d.y.mul(n.y), T::zero());
        T::axiom_add_zero_right(T::zero());
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)),
            T::zero().add(T::zero()), T::zero());
        T::axiom_eqv_reflexive(d.z.mul(n.z));
        additive_group_lemmas::lemma_add_congruence::<T>(
            d.x.mul(n.x).add(d.y.mul(n.y)), T::zero(),
            d.z.mul(n.z), d.z.mul(n.z));
        additive_group_lemmas::lemma_add_zero_left::<T>(d.z.mul(n.z));
        T::axiom_eqv_transitive(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            T::zero().add(d.z.mul(n.z)), d.z.mul(n.z));

        //  d.z*n.z ≡ 0
        T::axiom_eqv_symmetric(
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            d.z.mul(n.z));
        T::axiom_eqv_transitive(d.z.mul(n.z),
            d.x.mul(n.x).add(d.y.mul(n.y)).add(d.z.mul(n.z)),
            T::zero());

        //  Field cancel: n.z*d.z ≡ n.z*0, n.z ≢ 0 → d.z ≡ 0
        T::axiom_mul_commutative(n.z, d.z);
        T::axiom_eqv_transitive(n.z.mul(d.z), d.z.mul(n.z), T::zero());
        T::axiom_mul_zero_right(n.z);
        T::axiom_eqv_symmetric(n.z.mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(n.z.mul(d.z), T::zero(), n.z.mul(T::zero()));
        field_lemmas::lemma_mul_cancel_left::<T>(d.z, T::zero(), n.z);
    }
}

//  =========================================================================
//  Helper: coplanar point in non-degenerate triangle → orient3d decomposition
//  =========================================================================

///  Core algebraic fact: for a coplanar point inside a non-degenerate triangle,
///  orient3d at the point equals a non-negative weighted sum of orient3d at vertices.
///
///  The 2D barycentric coordinates from the projected triangle give weights
///  (u, v, w) that satisfy u ≥ 0, v ≥ 0, w ≥ 0, u+v+w ≡ 1, and
///  orient3d(x,y,z,p) ≡ u*orient3d(x,y,z,a) + v*orient3d(x,y,z,b) + w*orient3d(x,y,z,c).
///
///  Proof requires:
///  1. Orient2d of projected triangle ≢ 0 (from non-degeneracy + axis choice)
///  2. point_in_triangle_on_plane → orient2d signs consistent → bary coords ≥ 0
///  3. Projection injectivity: 2D bary reconstruction + coplanarity → 3D affine combination
///  4. Orient3d weighted form identity
pub proof fn lemma_coplanar_in_triangle_orient3d_decomposition<T: OrderedField>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    w: Point3<T>,
)
    requires
        point_in_triangle_on_plane(p, a, b, c),
        orient3d(a, b, c, p).eqv(T::zero()),
        !orient3d(a, b, c, w).eqv(T::zero()),
    ensures ({
        let axis = triangle_projection_axis(a, b, c);
        let p2 = project_by_axis(p, axis);
        let a2 = project_by_axis(a, axis);
        let b2 = project_by_axis(b, axis);
        let c2 = project_by_axis(c, axis);
        let (u, v, w_bary) = barycentric_coords_2d(p2, a2, b2, c2);
        let oa = orient3d(x, y, z, a);
        let ob = orient3d(x, y, z, b);
        let oc = orient3d(x, y, z, c);
        &&& T::zero().le(u)
        &&& T::zero().le(v)
        &&& T::zero().le(w_bary)
        &&& u.add(v).add(w_bary).eqv(T::one())
        &&& orient3d(x, y, z, p).eqv(u.mul(oa).add(v.mul(ob)).add(w_bary.mul(oc)))
    }),
{
    let axis = triangle_projection_axis(a, b, c);
    let p2 = project_by_axis(p, axis);
    let a2 = project_by_axis(a, axis);
    let b2 = project_by_axis(b, axis);
    let c2 = project_by_axis(c, axis);
    let d = orient2d(a2, b2, c2);
    let (u, v, w_bary) = barycentric_coords_2d(p2, a2, b2, c2);

    //  ---- Part A: orient2d(a2,b2,c2) ≢ 0 ----
    //  For axis 0: orient2d ≡ N.x (definitionally same after unfolding)
    //  For axis 1: orient2d ≡ -N.y
    //  For axis 2: orient2d ≡ N.z, must be nonzero since N.x≡0, N.y≡0 and triangle non-degenerate
    let n = triangle_normal(a, b, c);
    if axis == 0 {
        //  orient2d(drop_x(a), drop_x(b), drop_x(c)) unfolds to the same expression as n.x.
        //  Z3 sees !n.x.eqv(T::zero()) from triangle_projection_axis choosing axis 0.
        assert(!n.x.eqv(T::zero()));
        //  d and n.x are the same expression after unfolding, so !d.eqv(T::zero()).
    } else if axis == 1 {
        //  orient2d = P - Q, n.y = Q - P where P = (b.x-a.x)*(c.z-a.z), Q = (b.z-a.z)*(c.x-a.x).
        //  By sub_antisymmetric: d = P - Q ≡ -(Q - P) = -(n.y).
        //  If d ≡ 0, then -(n.y) ≡ 0, so n.y ≡ 0. But !n.y.eqv(0). Contradiction.
        assert(!n.y.eqv(T::zero()));
        if d.eqv(T::zero()) {
            let ba = sub3(b, a);
            let ca = sub3(c, a);
            let p_term = ba.x.mul(ca.z);
            let q_term = ba.z.mul(ca.x);
            //  d ≡ p_term.sub(q_term) and n.y ≡ q_term.sub(p_term) after unfolding.
            //  sub_antisymmetric: p_term.sub(q_term) ≡ q_term.sub(p_term).neg()
            additive_group_lemmas::lemma_sub_antisymmetric::<T>(p_term, q_term);
            //  sub_antisymmetric gives d.eqv(n.y.neg()), flip for transitive chain
            T::axiom_eqv_symmetric(d, n.y.neg());
            //  n.y.neg().eqv(d) and d.eqv(0), so n.y.neg().eqv(0)
            T::axiom_eqv_transitive(n.y.neg(), d, T::zero());
            //  neg(0) ≡ 0, so n.y.neg().neg() ≡ 0.neg() ≡ 0.
            additive_group_lemmas::lemma_neg_involution::<T>(n.y);
            additive_group_lemmas::lemma_neg_zero::<T>();
            T::axiom_neg_congruence(n.y.neg(), T::zero());
            T::axiom_eqv_transitive(n.y.neg().neg(), T::zero().neg(), T::zero());
            //  n.y ≡ n.y.neg().neg() ≡ 0.
            T::axiom_eqv_symmetric(n.y.neg().neg(), n.y);
            T::axiom_eqv_transitive(n.y, n.y.neg().neg(), T::zero());
        }
    } else {
        //  axis == 2: orient2d(drop_z) ≡ N.z definitionally.
        //  N.x ≡ 0, N.y ≡ 0 from triangle_projection_axis falling through.
        //  Prove by contradiction: if N.z ≡ 0, then orient3d(a,b,c,w) ≡ 0.
        if d.eqv(T::zero()) {
            //  d and N.z are the same expression after unfolding, so N.z ≡ 0.
            //  Use cyclic identity: triple(ba,ca,wa) ≡ triple(wa,ba,ca) = dot(wa,N).
            let ba = sub3(b, a);
            let ca = sub3(c, a);
            let wa = sub3(w, a);
            verus_linalg::vec3::ops::lemma_triple_cyclic::<T>(ba, ca, wa);
            verus_linalg::vec3::ops::lemma_triple_cyclic::<T>(ca, wa, ba);
            T::axiom_eqv_transitive(triple(ba, ca, wa), triple(ca, wa, ba), triple(wa, ba, ca));
            //  triple(wa,ba,ca) = dot(wa, cross(ba,ca)) = dot(wa, N) by def.
            //  dot(wa,N) = wa.x*N.x + wa.y*N.y + wa.z*N.z.
            //  Each term ≡ 0 since N.x ≡ 0, N.y ≡ 0, N.z ≡ 0 (from d ≡ 0).
            assert(n.x.eqv(T::zero()));
            assert(n.y.eqv(T::zero()));
            //  wa.x*N.x ≡ 0
            ring_lemmas::lemma_mul_congruence_right::<T>(wa.x, n.x, T::zero());
            T::axiom_mul_zero_right(wa.x);
            T::axiom_eqv_transitive(wa.x.mul(n.x), wa.x.mul(T::zero()), T::zero());
            //  wa.y*N.y ≡ 0
            ring_lemmas::lemma_mul_congruence_right::<T>(wa.y, n.y, T::zero());
            T::axiom_mul_zero_right(wa.y);
            T::axiom_eqv_transitive(wa.y.mul(n.y), wa.y.mul(T::zero()), T::zero());
            //  wa.z*N.z ≡ 0 (d and N.z are definitionally same, d ≡ 0)
            ring_lemmas::lemma_mul_congruence_right::<T>(wa.z, n.z, T::zero());
            T::axiom_mul_zero_right(wa.z);
            T::axiom_eqv_transitive(wa.z.mul(n.z), wa.z.mul(T::zero()), T::zero());
            //  dot(wa,N) = wa.x*N.x + wa.y*N.y + wa.z*N.z ≡ 0+0+0 ≡ 0
            additive_group_lemmas::lemma_add_congruence::<T>(
                wa.x.mul(n.x), T::zero(), wa.y.mul(n.y), T::zero(),
            );
            T::axiom_add_zero_right(T::zero());
            T::axiom_eqv_transitive(
                wa.x.mul(n.x).add(wa.y.mul(n.y)),
                T::zero().add(T::zero()),
                T::zero(),
            );
            T::axiom_add_congruence_left(
                wa.x.mul(n.x).add(wa.y.mul(n.y)), T::zero(),
                wa.z.mul(n.z),
            );
            additive_group_lemmas::lemma_add_congruence_right::<T>(
                T::zero(), wa.z.mul(n.z), T::zero(),
            );
            T::axiom_eqv_transitive(
                wa.x.mul(n.x).add(wa.y.mul(n.y)).add(wa.z.mul(n.z)),
                T::zero().add(wa.z.mul(n.z)),
                T::zero().add(T::zero()),
            );
            T::axiom_eqv_transitive(
                wa.x.mul(n.x).add(wa.y.mul(n.y)).add(wa.z.mul(n.z)),
                T::zero().add(T::zero()),
                T::zero(),
            );
            //  triple(wa,ba,ca) = dot(wa,N) ≡ 0 (Z3 unfolds triple→dot→expression)
            //  orient3d(a,b,c,w) = triple(ba,ca,wa) ≡ triple(wa,ba,ca) ≡ 0
            T::axiom_eqv_transitive(
                triple(ba, ca, wa), triple(wa, ba, ca), T::zero(),
            );
            //  Now orient3d(a,b,c,w).eqv(T::zero()), contradicting precondition.
        }
    }

    //  ---- Part B: u + v + w_bary ≡ 1 (existing lemma) ----
    lemma_barycentric_coords_sum_to_one::<T>(p2, a2, b2, c2);

    //  ---- Part C: u ≥ 0, v ≥ 0, w_bary ≥ 0 ----
    //  From point_in_triangle_on_plane: orient2d signs are consistent (no mixed pos/neg).
    //  Combined with partition_of_unity (sum ≡ d ≢ 0), numerators agree in sign with d.
    let t1 = orient2d(a2, b2, p2);  //  w_bary numerator
    let t2 = orient2d(b2, c2, p2);  //  u numerator
    let t3 = orient2d(c2, a2, p2);  //  v numerator
    //  Partition of unity for raw orient2d values: t2 + t3 + t1 ≡ d
    lemma_barycentric_partition_of_unity::<T>(p2, a2, b2, c2);
    //  d ≢ 0 from Part A. Split on sign of d.
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), d);
    //  Provide ordering facts Z3 needs for orient2d_sign unfolding:
    T::axiom_le_total(T::zero(), t1);
    T::axiom_le_total(T::zero(), t2);
    T::axiom_le_total(T::zero(), t3);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), t1);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), t2);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), t3);
    T::axiom_lt_iff_le_and_not_eqv(t1, T::zero());
    T::axiom_lt_iff_le_and_not_eqv(t2, T::zero());
    T::axiom_lt_iff_le_and_not_eqv(t3, T::zero());
    //  eqv bridge: ti ≡ 0 → both 0 ≤ ti and ti ≤ 0 (for Z3 to derive !ti.eqv(0))
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_le_total(T::zero(), T::zero());
    if t1.eqv(T::zero()) {
        T::axiom_eqv_symmetric(t1, T::zero());
        T::axiom_le_congruence(T::zero(), T::zero(), T::zero(), t1);
        T::axiom_le_congruence(T::zero(), t1, T::zero(), T::zero());
    }
    if T::zero().eqv(t1) { T::axiom_eqv_symmetric(T::zero(), t1); }
    if t2.eqv(T::zero()) {
        T::axiom_eqv_symmetric(t2, T::zero());
        T::axiom_le_congruence(T::zero(), T::zero(), T::zero(), t2);
        T::axiom_le_congruence(T::zero(), t2, T::zero(), T::zero());
    }
    if T::zero().eqv(t2) { T::axiom_eqv_symmetric(T::zero(), t2); }
    if t3.eqv(T::zero()) {
        T::axiom_eqv_symmetric(t3, T::zero());
        T::axiom_le_congruence(T::zero(), T::zero(), T::zero(), t3);
        T::axiom_le_congruence(T::zero(), t3, T::zero(), T::zero());
    }
    if T::zero().eqv(t3) { T::axiom_eqv_symmetric(T::zero(), t3); }
    //  Symmetry for d ≡ 0 (both directions: d.eqv(0) → 0.eqv(d) and 0.eqv(d) → d.eqv(0))
    if d.eqv(T::zero()) { T::axiom_eqv_symmetric(d, T::zero()); }
    if T::zero().eqv(d) { T::axiom_eqv_symmetric(T::zero(), d); }
    //  lt asymmetry: 0 < ti → !(ti < 0) and ti < 0 → !(0 < ti)
    //  Needed for d < 0 case: o_i != Neg gives 0.lt(ti) || !ti.lt(0),
    //  and Z3 needs asymmetry to derive !ti.lt(0) in the 0.lt(ti) case.
    if T::zero().lt(t1) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(T::zero(), t1); }
    if T::zero().lt(t2) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(T::zero(), t2); }
    if T::zero().lt(t3) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(T::zero(), t3); }
    if t1.lt(T::zero()) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(t1, T::zero()); }
    if t2.lt(T::zero()) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(t2, T::zero()); }
    if t3.lt(T::zero()) { ordered_ring_lemmas::lemma_lt_asymmetric::<T>(t3, T::zero()); }
    //  orient2d_sign let-bindings (Z3 unifies with point_in_triangle_on_plane internals)
    let o1 = orient2d_sign(a2, b2, p2);
    let o2 = orient2d_sign(b2, c2, p2);
    let o3 = orient2d_sign(c2, a2, p2);

    if T::zero().lt(d) {
        //  d > 0: show each ti ≥ 0.
        //  If any ti < 0 → orient2d_sign Neg → consistency blocks Pos on others
        //  → all ≤ 0 → sum ≤ 0 → contradiction with sum ≡ d > 0.
        if !T::zero().le(t2) {
            assert(o2 == OrientationSign::Negative);
            assert(o1 != OrientationSign::Positive);
            assert(o3 != OrientationSign::Positive);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t1);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t3);
            //  t2.le(0) from le_total. Sum ≤ 0:
            T::axiom_le_add_monotone(t2, T::zero(), t3);
            additive_group_lemmas::lemma_add_zero_left::<T>(t3);
            T::axiom_eqv_reflexive(t2.add(t3));
            T::axiom_le_congruence(t2.add(t3), t2.add(t3), T::zero().add(t3), t3);
            T::axiom_le_transitive(t2.add(t3), t3, T::zero());
            T::axiom_le_add_monotone(t2.add(t3), T::zero(), t1);
            additive_group_lemmas::lemma_add_zero_left::<T>(t1);
            T::axiom_eqv_reflexive(t2.add(t3).add(t1));
            T::axiom_le_congruence(
                t2.add(t3).add(t1), t2.add(t3).add(t1),
                T::zero().add(t1), t1,
            );
            T::axiom_le_transitive(t2.add(t3).add(t1), t1, T::zero());
            T::axiom_le_congruence(t2.add(t3).add(t1), d, T::zero(), T::zero());
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), d);
            T::axiom_le_antisymmetric(T::zero(), d);
        }
        if !T::zero().le(t3) {
            assert(o3 == OrientationSign::Negative);
            assert(o1 != OrientationSign::Positive);
            assert(o2 != OrientationSign::Positive);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t1);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t2);
            T::axiom_le_add_monotone(t2, T::zero(), t3);
            additive_group_lemmas::lemma_add_zero_left::<T>(t3);
            T::axiom_eqv_reflexive(t2.add(t3));
            T::axiom_le_congruence(t2.add(t3), t2.add(t3), T::zero().add(t3), t3);
            T::axiom_le_transitive(t2.add(t3), t3, T::zero());
            T::axiom_le_add_monotone(t2.add(t3), T::zero(), t1);
            additive_group_lemmas::lemma_add_zero_left::<T>(t1);
            T::axiom_eqv_reflexive(t2.add(t3).add(t1));
            T::axiom_le_congruence(
                t2.add(t3).add(t1), t2.add(t3).add(t1),
                T::zero().add(t1), t1,
            );
            T::axiom_le_transitive(t2.add(t3).add(t1), t1, T::zero());
            T::axiom_le_congruence(t2.add(t3).add(t1), d, T::zero(), T::zero());
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), d);
            T::axiom_le_antisymmetric(T::zero(), d);
        }
        if !T::zero().le(t1) {
            assert(o1 == OrientationSign::Negative);
            assert(o2 != OrientationSign::Positive);
            assert(o3 != OrientationSign::Positive);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t2);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(T::zero(), t3);
            T::axiom_le_add_monotone(t2, T::zero(), t3);
            additive_group_lemmas::lemma_add_zero_left::<T>(t3);
            T::axiom_eqv_reflexive(t2.add(t3));
            T::axiom_le_congruence(t2.add(t3), t2.add(t3), T::zero().add(t3), t3);
            T::axiom_le_transitive(t2.add(t3), t3, T::zero());
            T::axiom_le_add_monotone(t2.add(t3), T::zero(), t1);
            additive_group_lemmas::lemma_add_zero_left::<T>(t1);
            T::axiom_eqv_reflexive(t2.add(t3).add(t1));
            T::axiom_le_congruence(
                t2.add(t3).add(t1), t2.add(t3).add(t1),
                T::zero().add(t1), t1,
            );
            T::axiom_le_transitive(t2.add(t3).add(t1), t1, T::zero());
            T::axiom_le_congruence(t2.add(t3).add(t1), d, T::zero(), T::zero());
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), d);
            T::axiom_le_antisymmetric(T::zero(), d);
        }
        //  Now 0 ≤ t1, 0 ≤ t2, 0 ≤ t3.
        ordered_field_lemmas::lemma_nonneg_div_pos::<T>(t2, d);
        ordered_field_lemmas::lemma_nonneg_div_pos::<T>(t3, d);
        ordered_field_lemmas::lemma_nonneg_div_pos::<T>(t1, d);
    } else {
        //  d < 0: show each ti ≤ 0.
        //  Establish d.lt(0) for le_antisymmetric in contradiction blocks:
        T::axiom_lt_iff_le_and_not_eqv(d, T::zero());
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), d);
        //  If any ti > 0 → orient2d_sign Pos → consistency blocks Neg on others
        //  → all ≥ 0 → sum ≥ 0 → contradiction with sum ≡ d < 0.
        if !t2.le(T::zero()) {
            assert(o2 == OrientationSign::Positive);
            assert(o1 != OrientationSign::Negative);
            assert(o3 != OrientationSign::Negative);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t1, T::zero());
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t3, T::zero());
            //  0.le(t2) from le_total. Sum ≥ 0:
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2, t3);
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2.add(t3), t1);
            T::axiom_le_congruence(T::zero(), T::zero(), t2.add(t3).add(t1), d);
            T::axiom_lt_iff_le_and_not_eqv(d, T::zero());
            T::axiom_le_antisymmetric(d, T::zero());
            T::axiom_eqv_symmetric(d, T::zero());
        }
        if !t3.le(T::zero()) {
            assert(o3 == OrientationSign::Positive);
            assert(o1 != OrientationSign::Negative);
            assert(o2 != OrientationSign::Negative);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t1, T::zero());
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t2, T::zero());
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2, t3);
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2.add(t3), t1);
            T::axiom_le_congruence(T::zero(), T::zero(), t2.add(t3).add(t1), d);
            T::axiom_lt_iff_le_and_not_eqv(d, T::zero());
            T::axiom_le_antisymmetric(d, T::zero());
            T::axiom_eqv_symmetric(d, T::zero());
        }
        if !t1.le(T::zero()) {
            assert(o1 == OrientationSign::Positive);
            assert(o2 != OrientationSign::Negative);
            assert(o3 != OrientationSign::Negative);
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t2, T::zero());
            ordered_ring_lemmas::lemma_not_lt_implies_le::<T>(t3, T::zero());
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2, t3);
            verus_algebra::inequalities::lemma_nonneg_add::<T>(t2.add(t3), t1);
            T::axiom_le_congruence(T::zero(), T::zero(), t2.add(t3).add(t1), d);
            T::axiom_lt_iff_le_and_not_eqv(d, T::zero());
            T::axiom_le_antisymmetric(d, T::zero());
            T::axiom_eqv_symmetric(d, T::zero());
        }
        //  Now t1 ≤ 0, t2 ≤ 0, t3 ≤ 0.
        ordered_field_lemmas::lemma_nonpos_div_neg::<T>(t2, d);
        ordered_field_lemmas::lemma_nonpos_div_neg::<T>(t3, d);
        ordered_field_lemmas::lemma_nonpos_div_neg::<T>(t1, d);
    }

    //  ---- Part D: orient3d(x,y,z,p) ≡ u*oa + v*ob + w_bary*oc ----
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let oc = orient3d(x, y, z, c);
    let ba = sub3(b, a);
    let ca = sub3(c, a);
    let yx = sub3(y, x);
    let zx = sub3(z, x);
    let tba = triple(yx, zx, ba);
    let tca = triple(yx, zx, ca);
    let disp = scale(v, ba).add(scale(w_bary, ca));
    let q = add_vec3(a, disp);

    //  Step D1: orient3d(x,y,z,q) ≡ oa + v*tba + w*tca
    lemma_orient3d_affine_combination::<T>(x, y, z, a, b, c, v, w_bary);
    let oq_xyz = orient3d(x, y, z, q);

    //  Step D2: oa + tba ≡ ob (from linear_last + shift_endpoint)
    lemma_orient3d_linear_last::<T>(x, y, z, a, ba);
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, b);
    let q_ab = orient3d(x, y, z, add_vec3(a, ba));
    T::axiom_eqv_symmetric(q_ab, oa.add(tba));
    T::axiom_eqv_transitive(oa.add(tba), q_ab, ob);
    //  oa.add(tba).eqv(ob)

    //  Step D3: oa + tca ≡ oc (same argument)
    lemma_orient3d_linear_last::<T>(x, y, z, a, ca);
    lemma_orient3d_shift_endpoint::<T>(x, y, z, a, c);
    let q_ac = orient3d(x, y, z, add_vec3(a, ca));
    T::axiom_eqv_symmetric(q_ac, oa.add(tca));
    T::axiom_eqv_transitive(oa.add(tca), q_ac, oc);
    //  oa.add(tca).eqv(oc)

    //  Step D4: oa + v*tba + w*tca ≡ u*oa + v*ob + w*oc (weighted identity)
    lemma_weighted_additive_identity::<T>(oa, tba, tca, ob, oc, u, v, w_bary);

    //  Step D5: Chain: orient3d(x,y,z,q) ≡ u*oa + v*ob + w*oc
    T::axiom_eqv_transitive(
        oq_xyz,
        oa.add(v.mul(tba)).add(w_bary.mul(tca)),
        u.mul(oa).add(v.mul(ob)).add(w_bary.mul(oc))
    );

    //  Step D6: Barycentric reconstruction gives p's projected components
    lemma_barycentric_reconstruction::<T>(p2, a2, b2, c2);

    //  Step D7: Projection injectivity → sub3(p, q) has zero components
    lemma_projection_injectivity_zero::<T>(p, a, b, c, u, v, w_bary, axis);
    let pq = sub3(p, q);
    //  pq.x ≡ 0, pq.y ≡ 0, pq.z ≡ 0

    //  Step D8: orient3d(x,y,z,p) ≡ orient3d(x,y,z,q) via zero displacement
    //  triple(yx, zx, pq) ≡ 0 (zero vector)
    crate::insphere::lemma_triple_zero_third::<T>(yx, zx, pq);
    //  orient3d(x,y,z, add_vec3(q, pq)) = orient3d(x,y,z,q) + triple(yx,zx,pq)
    lemma_orient3d_linear_last::<T>(x, y, z, q, pq);
    //  orient3d(x,y,z, add_vec3(q, pq)) ≡ orient3d(x,y,z,q) + 0
    T::axiom_add_zero_right(oq_xyz);
    T::axiom_eqv_symmetric(oq_xyz.add(T::zero()), oq_xyz);
    T::axiom_eqv_reflexive(oq_xyz);
    additive_group_lemmas::lemma_add_congruence::<T>(
        oq_xyz, oq_xyz, triple(yx, zx, pq), T::zero()
    );
    T::axiom_eqv_transitive(
        oq_xyz.add(triple(yx, zx, pq)), oq_xyz.add(T::zero()), oq_xyz
    );
    //  oq_xyz + triple(yx,zx,pq) ≡ oq_xyz
    //  So: orient3d(x,y,z, add_vec3(q, pq)) ≡ oq_xyz
    let oq_pq = orient3d(x, y, z, add_vec3(q, pq));
    T::axiom_eqv_transitive(oq_pq, oq_xyz.add(triple(yx, zx, pq)), oq_xyz);

    //  orient3d(x,y,z, add_vec3(q, sub3(p,q))) ≡ orient3d(x,y,z, p)
    lemma_orient3d_shift_endpoint::<T>(x, y, z, q, p);
    //  Chain: orient3d(x,y,z,p) ← oq_pq → oq_xyz
    T::axiom_eqv_symmetric(oq_pq, orient3d(x, y, z, p));
    T::axiom_eqv_transitive(orient3d(x, y, z, p), oq_pq, oq_xyz);
    //  orient3d(x,y,z,p) ≡ oq_xyz

    //  Step D9: Final chain: orient3d(x,y,z,p) ≡ u*oa + v*ob + w*oc
    T::axiom_eqv_transitive(
        orient3d(x, y, z, p), oq_xyz,
        u.mul(oa).add(v.mul(ob)).add(w_bary.mul(oc))
    );
}

//  =========================================================================
//  Helper: inside triangle + all above → orient3d positive
//  =========================================================================

///  If point_in_triangle_on_plane(p, a, b, c) holds, orient3d(a,b,c,p) ≡ 0
///  (p is on the plane of the triangle), the triangle is non-degenerate (witnessed
///  by w with orient3d(a,b,c,w) ≢ 0), and orient3d(x,y,z,_) is strictly
///  positive at all three vertices a, b, c, then orient3d(x,y,z,p) > 0.
pub proof fn lemma_inside_triangle_orient3d_positive<T: OrderedField>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    w: Point3<T>,
)
    requires
        point_in_triangle_on_plane(p, a, b, c),
        orient3d(a, b, c, p).eqv(T::zero()),
        !orient3d(a, b, c, w).eqv(T::zero()),
        T::zero().lt(orient3d(x, y, z, a)),
        T::zero().lt(orient3d(x, y, z, b)),
        T::zero().lt(orient3d(x, y, z, c)),
    ensures
        T::zero().lt(orient3d(x, y, z, p)),
{
    //  Get the barycentric decomposition: orient3d at p is a non-negative
    //  weighted sum of orient3d at the vertices.
    let oa = orient3d(x, y, z, a);
    let ob = orient3d(x, y, z, b);
    let oc = orient3d(x, y, z, c);

    lemma_coplanar_in_triangle_orient3d_decomposition::<T>(p, a, b, c, x, y, z, w);

    let axis = triangle_projection_axis(a, b, c);
    let p2 = project_by_axis(p, axis);
    let a2 = project_by_axis(a, axis);
    let b2 = project_by_axis(b, axis);
    let c2 = project_by_axis(c, axis);
    let (u, v, w_bary) = barycentric_coords_2d(p2, a2, b2, c2);
    let weighted = u.mul(oa).add(v.mul(ob)).add(w_bary.mul(oc));

    //  From the helper: u ≥ 0, v ≥ 0, w_bary ≥ 0, u+v+w_bary ≡ 1,
    //  and orient3d(x,y,z,p) ≡ weighted.

    //  Each product is non-negative: u*oa ≥ 0, v*ob ≥ 0, w*oc ≥ 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oa);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), ob);
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), oc);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(u, oa);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(v, ob);
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<T>(w_bary, oc);

    //  At least one weight is positive (since u+v+w ≡ 1 and all ≥ 0).
    //  Case split like in lemma_orient3d_affine_positive.
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), u);
    if T::zero().lt(u) {
        ordered_field_lemmas::lemma_mul_pos_pos::<T>(u, oa);
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(u.mul(oa), v.mul(ob));
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
            u.mul(oa).add(v.mul(ob)), w_bary.mul(oc),
        );
    } else {
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), v);
        if T::zero().lt(v) {
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(v, ob);
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(u.mul(oa), v.mul(ob));
            ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(
                u.mul(oa).add(v.mul(ob)), w_bary.mul(oc),
            );
        } else {
            //  u ≡ 0, v ≡ 0. Since u+v+w ≡ 1 and u ≡ 0, v ≡ 0, we get w ≡ 1.
            //  So w > 0.
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), w_bary);
            if T::zero().eqv(w_bary) {
                //  Contradiction: u+v+w ≡ 0+0+0 ≡ 0, but u+v+w ≡ 1.
                T::axiom_eqv_symmetric(T::zero(), u);
                T::axiom_eqv_symmetric(T::zero(), v);
                T::axiom_eqv_symmetric(T::zero(), w_bary);
                additive_group_lemmas::lemma_add_congruence::<T>(
                    u, T::zero(), v, T::zero(),
                );
                T::axiom_add_zero_right(T::zero());
                T::axiom_eqv_transitive(
                    u.add(v), T::zero().add(T::zero()), T::zero(),
                );
                T::axiom_add_congruence_left(u.add(v), T::zero(), w_bary);
                additive_group_lemmas::lemma_add_congruence_right::<T>(
                    T::zero(), w_bary, T::zero(),
                );
                T::axiom_eqv_transitive(
                    u.add(v).add(w_bary),
                    T::zero().add(w_bary),
                    T::zero().add(T::zero()),
                );
                T::axiom_eqv_transitive(
                    u.add(v).add(w_bary),
                    T::zero().add(T::zero()),
                    T::zero(),
                );
                T::axiom_eqv_symmetric(u.add(v).add(w_bary), T::zero());
                T::axiom_eqv_transitive(
                    T::zero(), u.add(v).add(w_bary), T::one(),
                );
                ordered_ring_lemmas::lemma_zero_lt_one::<T>();
                T::axiom_lt_iff_le_and_not_eqv(T::zero(), T::one());
            }
            ordered_field_lemmas::lemma_mul_pos_pos::<T>(w_bary, oc);
            ordered_ring_lemmas::lemma_le_add_both::<T>(
                T::zero(), u.mul(oa), T::zero(), v.mul(ob),
            );
            T::axiom_add_zero_right(T::zero());
            ordered_ring_lemmas::lemma_le_congruence_left::<T>(
                T::zero().add(T::zero()), T::zero(), u.mul(oa).add(v.mul(ob)),
            );
            ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(
                u.mul(oa).add(v.mul(ob)), w_bary.mul(oc),
            );
        }
    }

    //  Transfer: 0 < weighted and orient3d(x,y,z,p) ≡ weighted → 0 < orient3d(x,y,z,p)
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_symmetric(orient3d(x, y, z, p), weighted);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), weighted, orient3d(x, y, z, p),
    );
}

//  =========================================================================
//  Lemma: single-sided separation → no T2 edge through T1
//  =========================================================================

///  If a T2 edge (d,e) has orient3d(a2,b2,c2,d) ≡ 0 and orient3d(a2,b2,c2,e) ≡ 0
///  (i.e., d,e are coplanar with T2), and all T1 vertices are strictly above
///  the plane of T2, then the segment (d,e) does not strictly intersect T1.
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
    //  Assume for contradiction that segment_triangle_intersects_strict(d,e,a1,b1,c1).
    if segment_triangle_intersects_strict(d, e, a1, b1, c1) {
        let t = segment_plane_intersection_parameter(d, e, a1, b1, c1);
        let p = segment_plane_intersection_point(d, e, a1, b1, c1);

        //  (A) orient3d(a2,b2,c2,p) ≡ 0:
        //      p = add_vec3(d, scale(t, sub3(e,d))), and d,e are coplanar with T2.
        lemma_orient3d_zero_on_coplanar_segment::<T>(a2, b2, c2, d, e, t);

        //  (B) orient3d(a1,b1,c1,p) ≡ 0:
        //      p is on the plane of T1 by construction (intersection point).
        //      This follows from the intersection parameter definition.
        lemma_intersection_on_plane::<T>(d, e, a1, b1, c1);

        //  (C) point_in_triangle_on_plane(p, a1, b1, c1):
        //      from the definition of segment_triangle_intersects_strict.

        //  (D) Triangle (a1,b1,c1) is non-degenerate:
        //      segment_crosses_plane_strict(d,e,a1,b1,c1) implies orient3d(a1,b1,c1,d)
        //      is nonzero (one endpoint above, one below).
        //      Prove !orient3d(a1,b1,c1,d).eqv(T::zero()):
        if orient3d(a1, b1, c1, d).eqv(T::zero()) {
            //  If it were zero, then by point_above/below definitions and lt_iff,
            //  we'd have a contradiction with segment_crosses_plane_strict.
            T::axiom_eqv_symmetric(orient3d(a1, b1, c1, d), T::zero());
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), orient3d(a1, b1, c1, d));
            T::axiom_lt_iff_le_and_not_eqv(orient3d(a1, b1, c1, d), T::zero());
        }

        //  (E) orient3d(a2,b2,c2,p) > 0:
        //      from lemma_inside_triangle_orient3d_positive with d as non-degeneracy witness.
        lemma_inside_triangle_orient3d_positive::<T>(p, a1, b1, c1, a2, b2, c2, d);

        //  Contradiction: orient3d(a2,b2,c2,p) ≡ 0 AND orient3d(a2,b2,c2,p) > 0.
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), orient3d(a2, b2, c2, p));
        T::axiom_eqv_symmetric(orient3d(a2, b2, c2, p), T::zero());
    }
}

///  The intersection point lies on the plane of the triangle.
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

    //  Precondition for orient_cancel: od - oe ≠ 0
    lemma_crossing_denominator_nonzero::<T>(d, e, a, b, c);

    //  (1) orient3d(a,b,c,p) ≡ od + triple(ba,ca,w) by linear_last
    lemma_orient3d_linear_last::<T>(a, b, c, d, w);

    //  (2) triple(ba,ca,w) ≡ t * triple(ba,ca,ed) by triple_scale_third
    lemma_triple_scale_third::<T>(t, ba, ca, ed);

    //  (3) Establish triple(ba,ca,ed) ≡ oe + (-od):
    //      From linear_last: orient3d(a,b,c,d+ed) ≡ od + triple(ba,ca,ed)
    //      From shift_endpoint: orient3d(a,b,c,d+ed) ≡ oe
    //      So: od + triple(ba,ca,ed) ≡ oe
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
    //  Now: od + triple(ba,ca,ed) ≡ oe

    //      Derive: od + (oe + (-od)) ≡ oe
    //      sub_then_add_cancel(oe, od): (oe - od) + od ≡ oe
    //      commutativity: od + (oe - od) ≡ (oe - od) + od ≡ oe
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(oe, od);
    T::axiom_add_commutative(od, oe.sub(od));
    T::axiom_eqv_transitive(
        od.add(oe.sub(od)),
        oe.sub(od).add(od),
        oe,
    );
    //      sub_is_add_neg: oe.sub(od) ≡ oe + (-od)
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
    //  Now: od + (oe + (-od)) ≡ oe

    //      Left cancel: triple(ba,ca,ed) ≡ oe + (-od)
    T::axiom_eqv_symmetric(od.add(oe.add(od.neg())), oe);
    T::axiom_eqv_transitive(
        od.add(triple(ba, ca, ed)),
        oe,
        od.add(oe.add(od.neg())),
    );
    additive_group_lemmas::lemma_add_left_cancel::<T>(triple(ba, ca, ed), oe.add(od.neg()), od);

    //  (4) t * triple(ba,ca,ed) ≡ t * (oe + (-od)) by mul congruence
    ring_lemmas::lemma_mul_congruence_right::<T>(t, triple(ba, ca, ed), oe.add(od.neg()));

    //  (5) od + t*triple ≡ od + t*(oe+(-od)) by add congruence
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        od, t.mul(triple(ba, ca, ed)), t.mul(oe.add(od.neg())),
    );

    //  (6) od + t*(oe+(-od)) ≡ 0 by orient_cancel
    lemma_orient_cancel::<T>(od, oe);

    //  (7) Chain: od + triple(ba,ca,w) ≡ od + t*triple ≡ od + t*(oe+(-od)) ≡ 0
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

    //  (8) Final: orient3d(a,b,c,p) ≡ od + triple(ba,ca,w) ≡ 0
    T::axiom_eqv_transitive(
        orient3d(a, b, c, add_vec3(d, w)),
        od.add(triple(ba, ca, w)),
        T::zero(),
    );
}

//  =========================================================================
//  Lemma: SINGLE-sided separation → no intersection
//  =========================================================================

///  If all vertices of T1 are on the same strict side of plane(T2), then
///  the two triangles do not strictly intersect.
///
///  This strengthens `lemma_both_separated_no_intersection` which requires
///  BOTH planes to separate. Single-sided separation suffices because:
///  - T1 edges can't cross plane(T2) (they're all on one side)
///  - T2 edges that cross plane(T1) would produce intersection points that
///    are both on plane(T2) (from being on a T2 edge) AND strictly above/below
///    plane(T2) (from being inside T1 with all vertices above/below), a
///    contradiction.
pub proof fn lemma_single_sided_separation<T: OrderedField>(
    a1: Point3<T>, b1: Point3<T>, c1: Point3<T>,
    a2: Point3<T>, b2: Point3<T>, c2: Point3<T>,
)
    requires
        all_same_strict_side(a1, b1, c1, a2, b2, c2),
    ensures
        !triangles_intersect_strict(a1, b1, c1, a2, b2, c2),
{
    //  T1 edges through T2: all T1 vertices on same side → no edge crosses plane(T2)
    lemma_t1_separated_no_t1_edges::<T>(a1, b1, c1, a2, b2, c2);

    //  T2 edges through T1: each T2 edge endpoint is a vertex of T2, so coplanar with T2.
    //  orient3d(a2,b2,c2,vertex_of_T2) ≡ 0 by the degenerate lemmas.
    if all_above_plane(a1, b1, c1, a2, b2, c2) {
        //  Edge (a2, b2)
        lemma_orient3d_degenerate_da::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_bd::<T>(a2, b2, c2);
        lemma_coplanar_edge_no_intersection::<T>(a2, b2, a1, b1, c1, a2, b2, c2);

        //  Edge (b2, c2)
        lemma_orient3d_degenerate_cd::<T>(a2, b2, c2);
        lemma_coplanar_edge_no_intersection::<T>(b2, c2, a1, b1, c1, a2, b2, c2);

        //  Edge (c2, a2)
        lemma_coplanar_edge_no_intersection::<T>(c2, a2, a1, b1, c1, a2, b2, c2);
    } else {
        //  all_below_plane case: orient3d(a2,b2,c2,a1) < 0, etc.
        //  The argument is symmetric. We need orient3d(a2,b2,c2,p) < 0 from
        //  all-below, but orient3d(a2,b2,c2,p) ≡ 0 from coplanarity.
        //  For now, prove via negation: -orient3d gives all-above with swapped plane.
        lemma_orient3d_degenerate_da::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_bd::<T>(a2, b2, c2);
        lemma_orient3d_degenerate_cd::<T>(a2, b2, c2);

        //  Need below-plane variant of coplanar_edge_no_intersection.
        lemma_coplanar_edge_no_intersection_below::<T>(a2, b2, a1, b1, c1, a2, b2, c2);
        lemma_coplanar_edge_no_intersection_below::<T>(b2, c2, a1, b1, c1, a2, b2, c2);
        lemma_coplanar_edge_no_intersection_below::<T>(c2, a2, a1, b1, c1, a2, b2, c2);
    }
}

///  Symmetric version for all-below-plane case.
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
    //  Same as coplanar_edge_no_intersection but with orient3d(a2,b2,c2,p) < 0
    //  contradicting orient3d(a2,b2,c2,p) ≡ 0.
    if segment_triangle_intersects_strict(d, e, a1, b1, c1) {
        let t = segment_plane_intersection_parameter(d, e, a1, b1, c1);
        let p = segment_plane_intersection_point(d, e, a1, b1, c1);

        lemma_orient3d_zero_on_coplanar_segment::<T>(a2, b2, c2, d, e, t);
        lemma_intersection_on_plane::<T>(d, e, a1, b1, c1);

        //  Non-degeneracy of (a1,b1,c1): same argument as above variant.
        if orient3d(a1, b1, c1, d).eqv(T::zero()) {
            T::axiom_eqv_symmetric(orient3d(a1, b1, c1, d), T::zero());
            T::axiom_lt_iff_le_and_not_eqv(T::zero(), orient3d(a1, b1, c1, d));
            T::axiom_lt_iff_le_and_not_eqv(orient3d(a1, b1, c1, d), T::zero());
        }

        //  orient3d(a2,b2,c2,p) < 0 from all-below + inside triangle
        //  (uses the negative version of orient3d_affine_positive)
        lemma_inside_triangle_orient3d_negative::<T>(p, a1, b1, c1, a2, b2, c2, d);

        //  Contradiction: orient3d(a2,b2,c2,p) ≡ 0 AND < 0
        T::axiom_lt_iff_le_and_not_eqv(orient3d(a2, b2, c2, p), T::zero());
    }
}

///  Negative version: if all vertices are below the plane, orient3d(x,y,z,p) < 0.
pub proof fn lemma_inside_triangle_orient3d_negative<T: OrderedField>(
    p: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
    x: Point3<T>, y: Point3<T>, z: Point3<T>,
    nondegen: Point3<T>,
)
    requires
        point_in_triangle_on_plane(p, a, b, c),
        orient3d(a, b, c, p).eqv(T::zero()),
        !orient3d(a, b, c, nondegen).eqv(T::zero()),
        orient3d(x, y, z, a).lt(T::zero()),
        orient3d(x, y, z, b).lt(T::zero()),
        orient3d(x, y, z, c).lt(T::zero()),
    ensures
        orient3d(x, y, z, p).lt(T::zero()),
{
    //  Reduce to positive case via swap_bc: orient3d(x,z,y,v) ≡ -orient3d(x,y,z,v).
    //  If orient3d(x,y,z,v) < 0, then 0 < -orient3d(x,y,z,v) ≡ orient3d(x,z,y,v).
    crate::intersection3d::lemma_neg_of_neg_is_pos::<T>(orient3d(x, y, z, a));
    crate::intersection3d::lemma_neg_of_neg_is_pos::<T>(orient3d(x, y, z, b));
    crate::intersection3d::lemma_neg_of_neg_is_pos::<T>(orient3d(x, y, z, c));
    lemma_orient3d_swap_bc::<T>(x, y, z, a);
    lemma_orient3d_swap_bc::<T>(x, y, z, b);
    lemma_orient3d_swap_bc::<T>(x, y, z, c);
    //  Transfer: 0 < -(orient3d(x,y,z,v)) and orient3d(x,z,y,v) ≡ -(orient3d(x,y,z,v))
    //  → 0 < orient3d(x,z,y,v)
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_symmetric(orient3d(x, z, y, a), orient3d(x, y, z, a).neg());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), orient3d(x, y, z, a).neg(), orient3d(x, z, y, a),
    );
    T::axiom_eqv_symmetric(orient3d(x, z, y, b), orient3d(x, y, z, b).neg());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), orient3d(x, y, z, b).neg(), orient3d(x, z, y, b),
    );
    T::axiom_eqv_symmetric(orient3d(x, z, y, c), orient3d(x, y, z, c).neg());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), orient3d(x, y, z, c).neg(), orient3d(x, z, y, c),
    );
    //  Apply positive case with swapped plane (x, z, y)
    lemma_inside_triangle_orient3d_positive::<T>(p, a, b, c, x, z, y, nondegen);
    //  Transfer: 0 < orient3d(x,z,y,p) ≡ -orient3d(x,y,z,p) → 0 < -orient3d(x,y,z,p)
    lemma_orient3d_swap_bc::<T>(x, y, z, p);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero(), T::zero(), orient3d(x, z, y, p), orient3d(x, y, z, p).neg(),
    );
    //  Now: 0 < -orient3d(x,y,z,p). Flip: -(-orient3d(x,y,z,p)) < -0, i.e., orient3d < 0.
    ordered_ring_lemmas::lemma_lt_neg_flip::<T>(T::zero(), orient3d(x, y, z, p).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(orient3d(x, y, z, p));
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_symmetric(T::zero().neg(), T::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        orient3d(x, y, z, p).neg().neg(), orient3d(x, y, z, p),
        T::zero().neg(), T::zero(),
    );
}

} //  verus!
