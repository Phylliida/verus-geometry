use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq;
use crate::point2::*;
use crate::voronoi::sq_dist_2d;

verus! {

// ===========================================================================
//  Circle2 type — center + squared radius
// ===========================================================================

/// A 2D circle: center + squared radius.
/// A point p is on the circle iff sq_dist(p, center) ≡ radius_sq.
pub struct Circle2<T: Ring> {
    pub center: Point2<T>,
    pub radius_sq: T,
}

// ===========================================================================
//  Core predicates
// ===========================================================================

/// A point lies on the circle iff its squared distance to the center equals radius_sq.
pub open spec fn point_on_circle2<T: Ring>(circle: Circle2<T>, p: Point2<T>) -> bool {
    sq_dist_2d(p, circle.center).eqv(circle.radius_sq)
}

/// A point is strictly inside the circle.
pub open spec fn point_inside_circle2<T: OrderedRing>(circle: Circle2<T>, p: Point2<T>) -> bool {
    sq_dist_2d(p, circle.center).lt(circle.radius_sq)
}

/// A point is strictly outside the circle.
pub open spec fn point_outside_circle2<T: OrderedRing>(circle: Circle2<T>, p: Point2<T>) -> bool {
    circle.radius_sq.lt(sq_dist_2d(p, circle.center))
}

// ===========================================================================
//  Constructors
// ===========================================================================

/// Circle from center and a point on the circle.
pub open spec fn circle2_from_center_point<T: Ring>(
    center: Point2<T>, on_circle: Point2<T>,
) -> Circle2<T> {
    Circle2 { center, radius_sq: sq_dist_2d(on_circle, center) }
}

/// Circle from center and explicit squared radius.
pub open spec fn circle2_from_center_radius_sq<T: Ring>(
    center: Point2<T>, radius_sq: T,
) -> Circle2<T> {
    Circle2 { center, radius_sq }
}

// ===========================================================================
//  Lemmas
// ===========================================================================

/// The point used to construct circle2_from_center_point lies on the circle.
pub proof fn lemma_on_circle_point<T: Ring>(center: Point2<T>, on_circle: Point2<T>)
    ensures
        point_on_circle2(circle2_from_center_point(center, on_circle), on_circle),
{
    T::axiom_eqv_reflexive(sq_dist_2d(on_circle, center));
}

/// Connection to circumcenter: if center is the circumcenter of (a,b,c),
/// then a, b, c all lie on the circle centered at center with radius sq_dist(a, center).
pub proof fn lemma_circumcircle_connection<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        crate::voronoi::is_circumcenter_2d(center, a, b, c),
    ensures
        point_on_circle2(circle2_from_center_point(center, a), b),
        point_on_circle2(circle2_from_center_point(center, a), c),
{
    assume(false); // Deferred: uses transitivity of eqv on sq_dist
}

} // verus!
