use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_linalg::vec2::Vec2;
use crate::point2::*;
use crate::orient2d::*;
use crate::convex_polygon::polygon_next_index;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// Cross product of two points treated as position vectors from origin:
/// cross_origin(p, q) = p.x * q.y - p.y * q.x
pub open spec fn cross_origin<T: Ring>(p: Point2<T>, q: Point2<T>) -> T {
    p.x.mul(q.y).sub(p.y.mul(q.x))
}

/// Recursive prefix sum of shoelace terms for edges [0, k).
/// Each term is cross_origin(polygon[i], polygon[(i+1) % n]).
pub open spec fn signed_area_2x_prefix<T: Ring>(
    polygon: Seq<Point2<T>>, k: int,
) -> T
    recommends
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
    decreases k,
{
    if k <= 0 {
        T::zero()
    } else {
        let i = k - 1;
        let j = polygon_next_index(polygon.len() as int, i);
        signed_area_2x_prefix(polygon, i).add(cross_origin(polygon[i], polygon[j]))
    }
}

/// Twice the signed area of a simple polygon (shoelace formula).
/// Positive for CCW winding, negative for CW, zero for degenerate.
pub open spec fn signed_area_2x<T: Ring>(polygon: Seq<Point2<T>>) -> T
    recommends polygon.len() >= 3,
{
    signed_area_2x_prefix(polygon, polygon.len() as int)
}

// ---------------------------------------------------------------------------
// Lemma: cross_origin relates to det2d
// ---------------------------------------------------------------------------

/// cross_origin(p, q) ≡ det2d(Vec2{p.x, p.y}, Vec2{q.x, q.y})
pub proof fn lemma_cross_origin_is_det2d<T: Ring>(p: Point2<T>, q: Point2<T>)
    ensures
        cross_origin(p, q).eqv(
            det2d(Vec2 { x: p.x, y: p.y }, Vec2 { x: q.x, y: q.y })
        ),
{
    // Both expand to p.x.mul(q.y).sub(p.y.mul(q.x))
    T::axiom_eqv_reflexive(cross_origin(p, q));
}

// ---------------------------------------------------------------------------
// Prefix sum unfold (for exec loop invariant)
// ---------------------------------------------------------------------------

/// Adding one more edge term to the prefix sum.
pub proof fn lemma_prefix_unfold<T: Ring>(
    polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 < k <= polygon.len(),
    ensures
        signed_area_2x_prefix(polygon, k) ==
            signed_area_2x_prefix(polygon, k - 1).add(
                cross_origin(
                    polygon[k - 1],
                    polygon[polygon_next_index(polygon.len() as int, k - 1)]
                )
            ),
{
    // Direct from definition
}

/// For a triangle [a, b, c], the shoelace area equals orient2d(a, b, c).
pub proof fn lemma_triangle_area_is_orient2d<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        signed_area_2x(seq![a, b, c]).eqv(orient2d(a, b, c)),
{
    let poly = seq![a, b, c];

    // Help Verus unfold the prefix sum
    assert(poly.len() == 3);
    assert(poly[0] == a);
    assert(poly[1] == b);
    assert(poly[2] == c);
    assert(polygon_next_index(3, 0) == 1);
    assert(polygon_next_index(3, 1) == 2);
    assert(polygon_next_index(3, 2) == 0);

    let co_ab = cross_origin(a, b);
    let co_bc = cross_origin(b, c);
    let co_ca = cross_origin(c, a);

    // Help Verus unfold the recursive prefix sum
    assert(signed_area_2x_prefix(poly, 0) == T::zero());
    assert(signed_area_2x_prefix(poly, 1) == T::zero().add(co_ab));
    assert(signed_area_2x_prefix(poly, 2) == T::zero().add(co_ab).add(co_bc));
    assert(signed_area_2x_prefix(poly, 3) == T::zero().add(co_ab).add(co_bc).add(co_ca));

    let sa = T::zero().add(co_ab).add(co_bc).add(co_ca);
    assert(signed_area_2x(poly) == sa);

    // Vec2 versions for det2d calls
    let a_v = Vec2 { x: a.x, y: a.y };
    let b_v = Vec2 { x: b.x, y: b.y };
    let c_v = Vec2 { x: c.x, y: c.y };

    let ab = det2d(a_v, b_v);
    let bc = det2d(b_v, c_v);
    let ca = det2d(c_v, a_v);
    let ba = det2d(b_v, a_v);
    let ac = det2d(a_v, c_v);

    // === Part 1: signed_area ≡ ab + bc + ca ===

    // cross_origin ≡ det2d
    lemma_cross_origin_is_det2d::<T>(a, b); // co_ab.eqv(ab)
    lemma_cross_origin_is_det2d::<T>(b, c); // co_bc.eqv(bc)
    lemma_cross_origin_is_det2d::<T>(c, a); // co_ca.eqv(ca)

    // 0 + co_ab ≡ co_ab ≡ ab
    additive_group_lemmas::lemma_add_zero_left::<T>(co_ab);
    T::axiom_eqv_transitive(T::zero().add(co_ab), co_ab, ab);

    // sa = ((0+co_ab)+co_bc)+co_ca ≡ (ab+bc)+ca
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().add(co_ab), ab, co_bc, bc,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().add(co_ab).add(co_bc), ab.add(bc), co_ca, ca,
    );
    // → sa.eqv(ab.add(bc).add(ca))

    // === Part 2: orient2d ≡ ab + bc + ca ===

    // orient2d(a,b,c) = det2d(sub2(b,a), sub2(c,a)) ≡ bc - ba - ac
    crate::barycentric::lemma_det2d_expand_vsub_qsub::<T>(a_v, b_v, c_v);

    // Convert subs to add-negs:
    // bc.sub(ba) ≡ bc.add(ba.neg())
    T::axiom_sub_is_add_neg(bc, ba);
    // bc.sub(ba).sub(ac) ≡ bc.sub(ba).add(ac.neg())
    T::axiom_sub_is_add_neg(bc.sub(ba), ac);

    // Propagate: bc.sub(ba).add(ac.neg()) ≡ bc.add(ba.neg()).add(ac.neg())
    T::axiom_eqv_reflexive(ac.neg());
    additive_group_lemmas::lemma_add_congruence::<T>(
        bc.sub(ba), bc.add(ba.neg()), ac.neg(), ac.neg(),
    );
    T::axiom_eqv_transitive(
        bc.sub(ba).sub(ac),
        bc.sub(ba).add(ac.neg()),
        bc.add(ba.neg()).add(ac.neg()),
    );
    // → bc.sub(ba).sub(ac) ≡ bc.add(ba.neg()).add(ac.neg())

    // Antisymmetry: ba.neg() ≡ ab, ac.neg() ≡ ca
    lemma_det2d_antisymmetric::<T>(a_v, b_v); // ab.eqv(ba.neg())
    T::axiom_eqv_symmetric(ab, ba.neg());     // ba.neg().eqv(ab)
    lemma_det2d_antisymmetric::<T>(c_v, a_v); // ca.eqv(ac.neg())
    T::axiom_eqv_symmetric(ca, ac.neg());     // ac.neg().eqv(ca)

    // bc.add(ba.neg()).add(ac.neg()) ≡ bc.add(ab).add(ca)
    T::axiom_eqv_reflexive(bc);
    additive_group_lemmas::lemma_add_congruence::<T>(bc, bc, ba.neg(), ab);
    additive_group_lemmas::lemma_add_congruence::<T>(
        bc.add(ba.neg()), bc.add(ab), ac.neg(), ca,
    );

    // Chain: bc.sub(ba).sub(ac) ≡ bc.add(ab).add(ca)
    T::axiom_eqv_transitive(
        bc.sub(ba).sub(ac),
        bc.add(ba.neg()).add(ac.neg()),
        bc.add(ab).add(ca),
    );

    // Commutativity: bc+ab ≡ ab+bc, so bc+ab+ca ≡ ab+bc+ca
    T::axiom_add_commutative(bc, ab);
    T::axiom_eqv_reflexive(ca);
    additive_group_lemmas::lemma_add_congruence::<T>(
        bc.add(ab), ab.add(bc), ca, ca,
    );

    // Chain: bc.sub(ba).sub(ac) ≡ ab+bc+ca
    T::axiom_eqv_transitive(
        bc.sub(ba).sub(ac),
        bc.add(ab).add(ca),
        ab.add(bc).add(ca),
    );

    // orient2d ≡ bc.sub(ba).sub(ac) ≡ ab+bc+ca
    T::axiom_eqv_transitive(
        orient2d(a, b, c),
        bc.sub(ba).sub(ac),
        ab.add(bc).add(ca),
    );

    // === Part 3: sa ≡ orient2d ===
    // sa ≡ ab+bc+ca, orient2d ≡ ab+bc+ca → ab+bc+ca ≡ orient2d
    T::axiom_eqv_symmetric(orient2d(a, b, c), ab.add(bc).add(ca));
    T::axiom_eqv_transitive(sa, ab.add(bc).add(ca), orient2d(a, b, c));
}

} // verus!
