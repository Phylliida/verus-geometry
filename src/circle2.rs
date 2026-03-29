use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq;
use crate::point2::*;
use crate::voronoi::sq_dist_2d;

verus! {

//  ===========================================================================
//   Circle2 type — center + squared radius
//  ===========================================================================

///  A 2D circle: center + squared radius.
///  A point p is on the circle iff sq_dist(p, center) ≡ radius_sq.
pub struct Circle2<T: Ring> {
    pub center: Point2<T>,
    pub radius_sq: T,
}

//  ===========================================================================
//   Core predicates
//  ===========================================================================

///  A point lies on the circle iff its squared distance to the center equals radius_sq.
pub open spec fn point_on_circle2<T: Ring>(circle: Circle2<T>, p: Point2<T>) -> bool {
    sq_dist_2d(p, circle.center).eqv(circle.radius_sq)
}

///  A point is strictly inside the circle.
pub open spec fn point_inside_circle2<T: OrderedRing>(circle: Circle2<T>, p: Point2<T>) -> bool {
    sq_dist_2d(p, circle.center).lt(circle.radius_sq)
}

///  A point is strictly outside the circle.
pub open spec fn point_outside_circle2<T: OrderedRing>(circle: Circle2<T>, p: Point2<T>) -> bool {
    circle.radius_sq.lt(sq_dist_2d(p, circle.center))
}

//  ===========================================================================
//   Constructors
//  ===========================================================================

///  Circle from center and a point on the circle.
pub open spec fn circle2_from_center_point<T: Ring>(
    center: Point2<T>, on_circle: Point2<T>,
) -> Circle2<T> {
    Circle2 { center, radius_sq: sq_dist_2d(on_circle, center) }
}

///  Circle from center and explicit squared radius.
pub open spec fn circle2_from_center_radius_sq<T: Ring>(
    center: Point2<T>, radius_sq: T,
) -> Circle2<T> {
    Circle2 { center, radius_sq }
}

//  ===========================================================================
//   Lemmas
//  ===========================================================================

///  The point used to construct circle2_from_center_point lies on the circle.
pub proof fn lemma_on_circle_point<T: Ring>(center: Point2<T>, on_circle: Point2<T>)
    ensures
        point_on_circle2(circle2_from_center_point(center, on_circle), on_circle),
{
    T::axiom_eqv_reflexive(sq_dist_2d(on_circle, center));
}

///  norm_sq(neg(v)) ≡ norm_sq(v) — negation doesn't change squared norm.
proof fn lemma_norm_sq_neg<T: Ring>(v: Vec2<T>)
    ensures
        norm_sq(v.neg()).eqv(norm_sq(v)),
{
    //  norm_sq(neg(v)) = (-v.x)*(-v.x) + (-v.y)*(-v.y)
    //  ≡ v.x*v.x + v.y*v.y = norm_sq(v)
    lemma_neg_mul_neg::<T>(v.x, v.x);
    lemma_neg_mul_neg::<T>(v.y, v.y);
    lemma_add_congruence::<T>(v.x.neg().mul(v.x.neg()), v.x.mul(v.x),
                              v.y.neg().mul(v.y.neg()), v.y.mul(v.y));
}

///  Squared distance is symmetric: sq_dist_2d(p, q) ≡ sq_dist_2d(q, p).
pub proof fn lemma_sq_dist_symmetric<T: Ring>(p: Point2<T>, q: Point2<T>)
    ensures
        sq_dist_2d(p, q).eqv(sq_dist_2d(q, p)),
{
    //  sq_dist(p,q) = norm_sq(sub2(p,q))
    //  sub2(p,q) ≡ neg(sub2(q,p))
    lemma_sub2_antisymmetric::<T>(p, q);
    //  norm_sq(sub2(p,q)) ≡ norm_sq(neg(sub2(q,p)))
    use verus_linalg::vec2::ops::lemma_norm_sq_congruence;
    lemma_norm_sq_congruence::<T>(sub2(p, q), sub2(q, p).neg());
    //  norm_sq(neg(sub2(q,p))) ≡ norm_sq(sub2(q,p))
    lemma_norm_sq_neg::<T>(sub2(q, p));
    //  chain
    T::axiom_eqv_transitive(
        norm_sq(sub2(p, q)),
        norm_sq(sub2(q, p).neg()),
        norm_sq(sub2(q, p)),
    );
}

///  Connection to circumcenter: if center is the circumcenter of (a,b,c),
///  then a, b, c all lie on the circle centered at center with radius sq_dist(a, center).
pub proof fn lemma_circumcircle_connection<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        crate::voronoi::is_circumcenter_2d(center, a, b, c),
    ensures
        point_on_circle2(circle2_from_center_point(center, a), b),
        point_on_circle2(circle2_from_center_point(center, a), c),
{
    //  is_circumcenter gives: sq_dist(center, a) ≡ sq_dist(center, b)
    //                      and sq_dist(center, b) ≡ sq_dist(center, c)
    //  point_on_circle2 needs: sq_dist(b, center) ≡ sq_dist(a, center)
    //                      and sq_dist(c, center) ≡ sq_dist(a, center)

    //  Bridge with symmetry: sq_dist(x, y) ≡ sq_dist(y, x)
    lemma_sq_dist_symmetric::<T>(center, a);
    lemma_sq_dist_symmetric::<T>(center, b);
    lemma_sq_dist_symmetric::<T>(center, c);
    lemma_sq_dist_symmetric::<T>(b, center);
    lemma_sq_dist_symmetric::<T>(c, center);

    //  sq_dist(center,a) ≡ sq_dist(center,b) → sq_dist(b,center) ≡ sq_dist(a,center)
    T::axiom_eqv_symmetric(sq_dist_2d(center, a), sq_dist_2d(center, b));
    //  sq_dist(center,b) ≡ sq_dist(center,a)
    //  sq_dist(b,center) ≡ sq_dist(center,b) ≡ sq_dist(center,a) ≡ sq_dist(a,center)
    T::axiom_eqv_transitive(sq_dist_2d(b, center), sq_dist_2d(center, b), sq_dist_2d(center, a));
    T::axiom_eqv_transitive(sq_dist_2d(b, center), sq_dist_2d(center, a), sq_dist_2d(a, center));

    //  sq_dist(center,b) ≡ sq_dist(center,c) → sq_dist(c,center) ≡ sq_dist(a,center)
    T::axiom_eqv_symmetric(sq_dist_2d(center, b), sq_dist_2d(center, c));
    T::axiom_eqv_transitive(sq_dist_2d(c, center), sq_dist_2d(center, c), sq_dist_2d(center, b));
    T::axiom_eqv_transitive(sq_dist_2d(c, center), sq_dist_2d(center, b), sq_dist_2d(center, a));
    T::axiom_eqv_transitive(sq_dist_2d(c, center), sq_dist_2d(center, a), sq_dist_2d(a, center));
}

} //  verus!
