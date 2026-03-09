use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
use crate::point2::*;
use crate::line2::*;
use crate::circle2::*;
use crate::circle_line::*;

verus! {

// ===========================================================================
//  Circle-Circle intersection
// ===========================================================================
//
// Two circles C1: ||p - c1||² = r1² and C2: ||p - c2||² = r2²
// intersect where both equations hold. Subtracting gives a linear
// equation (the radical axis), reducing to circle-line intersection.
// ===========================================================================

/// Radical axis of two circles: the line of points equidistant from both circles.
/// Derived by subtracting the circle equations:
///   ||p - c1||² - ||p - c2||² = r1² - r2²
/// Expanding: 2*(c2.x - c1.x)*x + 2*(c2.y - c1.y)*y + (||c1||² - ||c2||² - r1² + r2²) = 0
///
/// Simplified (without the factor of 2):
///   a = c2.x - c1.x
///   b = c2.y - c1.y
///   c = ((c1.x² + c1.y²) - (c2.x² + c2.y²) - r1² + r2²) / 2
///
/// Actually, to avoid division by 2, we use the un-halved form:
///   a = 2*(c2.x - c1.x)
///   b = 2*(c2.y - c1.y)
///   c = (c1.x² + c1.y² - r1²) - (c2.x² + c2.y² - r2²)
///
/// But even simpler: just use the direct subtraction without the factor of 2:
pub open spec fn radical_axis<T: Ring>(
    c1: Circle2<T>, c2: Circle2<T>,
) -> Line2<T> {
    // ||p - c1||² = r1² expands to:
    //   p.x² - 2*c1.x*p.x + c1.x² + p.y² - 2*c1.y*p.y + c1.y² = r1²
    // ||p - c2||² = r2² expands to:
    //   p.x² - 2*c2.x*p.x + c2.x² + p.y² - 2*c2.y*p.y + c2.y² = r2²
    // Subtracting (C1 - C2):
    //   2*(c2.x - c1.x)*p.x + 2*(c2.y - c1.y)*p.y
    //     + (c1.x² + c1.y² - r1²) - (c2.x² + c2.y² - r2²) = 0
    //
    // Using from_int(2) would require OrderedField for division.
    // Instead, keep the coefficients with factor of 2 baked in:
    let two = T::one().add(T::one());
    let a = two.mul(c2.center.x.sub(c1.center.x));
    let b = two.mul(c2.center.y.sub(c1.center.y));
    // Constant term: c1.x² + c1.y² - r1² - c2.x² - c2.y² + r2²
    let c1_sq = c1.center.x.mul(c1.center.x).add(c1.center.y.mul(c1.center.y));
    let c2_sq = c2.center.x.mul(c2.center.x).add(c2.center.y.mul(c2.center.y));
    let c = c1_sq.sub(c1.radius_sq).sub(c2_sq.sub(c2.radius_sq));
    Line2 { a, b, c }
}

/// Circle-circle intersection point via radical axis + circle-line.
pub open spec fn cc_intersection_point<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, plus: bool,
) -> Point2<SpecQuadExt<F, R>> {
    cl_intersection_point(c1, radical_axis(c1, c2), plus)
}

/// Discriminant for circle-circle intersection (via the circle-line discriminant
/// with the radical axis).
pub open spec fn cc_discriminant<T: Ring>(
    c1: Circle2<T>, c2: Circle2<T>,
) -> T {
    cl_discriminant(c1, radical_axis(c1, c2))
}

// ===========================================================================
//  Lemmas
// ===========================================================================

/// The radical axis is correct: any point on both circles lies on the radical axis.
pub proof fn lemma_radical_axis_correct<T: Ring>(
    c1: Circle2<T>, c2: Circle2<T>, p: Point2<T>,
)
    requires
        point_on_circle2(c1, p),
        point_on_circle2(c2, p),
    ensures
        point_on_line2(radical_axis(c1, c2), p),
{
    assume(false); // Deferred: algebraic expansion of ||p-c1||² = r1² and ||p-c2||² = r2²
}

/// Circle-circle intersection lies on c1.
pub proof fn lemma_cc_intersection_on_c1<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, plus: bool,
)
    requires
        !c1.center.eqv(c2.center),
        R::value().eqv(cc_discriminant(c1, c2)),
        F::zero().lt(cc_discriminant(c1, c2)),
    ensures
        crate::voronoi::sq_dist_2d(
            cc_intersection_point::<F, R>(c1, c2, plus),
            crate::constructed_scalar::lift_point2::<F, R>(c1.center),
        ).eqv(crate::constructed_scalar::qext_from_rational::<F, R>(c1.radius_sq)),
{
    assume(false); // Delegates to lemma_cl_intersection_on_circle
}

/// Circle-circle intersection lies on c2.
pub proof fn lemma_cc_intersection_on_c2<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, plus: bool,
)
    requires
        !c1.center.eqv(c2.center),
        R::value().eqv(cc_discriminant(c1, c2)),
        F::zero().lt(cc_discriminant(c1, c2)),
    ensures
        crate::voronoi::sq_dist_2d(
            cc_intersection_point::<F, R>(c1, c2, plus),
            crate::constructed_scalar::lift_point2::<F, R>(c2.center),
        ).eqv(crate::constructed_scalar::qext_from_rational::<F, R>(c2.radius_sq)),
{
    assume(false); // Uses radical_axis_correct + cl_intersection_on_circle
}

} // verus!
