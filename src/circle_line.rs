use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::field_lemmas::*;
use verus_algebra::quadratic::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
use crate::point2::*;
use crate::line2::*;
use crate::circle2::*;
use crate::voronoi::sq_dist_2d;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq;

verus! {

// ===========================================================================
//  Circle-Line intersection
// ===========================================================================
//
// Given circle C: ||p - center||² = r² and line L: ax + by + c = 0,
// parametrize the line as p(t) = p0 + t * dir where dir = (-b, a)
// and p0 is any point on the line.
//
// Substituting into the circle equation gives a quadratic in t:
//   A*t² + B*t + C_coef = 0
// where A = ||dir||² = a² + b², B and C_coef depend on center, p0, r².
//
// The discriminant D = B² - 4*A*C_coef determines the intersection count.
// Intersection coordinates are in F(sqrt(D)), represented as SpecQuadExt<F, R>.
// ===========================================================================

/// Direction vector along the line ax + by + c = 0: dir = (-b, a).
pub open spec fn line_direction<T: Ring>(line: Line2<T>) -> Vec2<T> {
    Vec2 { x: line.b.neg(), y: line.a }
}

/// Quadratic coefficient A = ||dir||² = a² + b² > 0 for non-degenerate lines.
pub open spec fn cl_quad_a<T: Ring>(line: Line2<T>) -> T {
    line.a.mul(line.a).add(line.b.mul(line.b))
}

/// Signed distance from center to the line (numerator only):
/// a * cx + b * cy + c.
pub open spec fn cl_signed_dist_num<T: Ring>(
    circle: Circle2<T>, line: Line2<T>,
) -> T {
    line.a.mul(circle.center.x).add(line.b.mul(circle.center.y)).add(line.c)
}

/// Discriminant of the circle-line intersection quadratic.
/// D = A * r² - (a*cx + b*cy + c)²
/// where A = a² + b².
///
/// When D > 0: two intersections. D = 0: tangent. D < 0: no intersection.
pub open spec fn cl_discriminant<T: Ring>(
    circle: Circle2<T>, line: Line2<T>,
) -> T {
    let a_coef = cl_quad_a(line);
    let dist_num = cl_signed_dist_num(circle, line);
    a_coef.mul(circle.radius_sq).sub(dist_num.mul(dist_num))
}

/// Number of intersection points.
pub open spec fn cl_intersection_count<T: OrderedRing>(
    circle: Circle2<T>, line: Line2<T>,
) -> int {
    let d = cl_discriminant(circle, line);
    if T::zero().lt(d) { 2 }
    else if d.eqv(T::zero()) { 1 }
    else { 0 }
}

/// Circle-line intersection parameter t (the ± root of the quadratic).
/// t = (-B ± sqrt(D)) / (2A)
/// where B = -2 * (a*(cx - p0x) + b*(cy - p0y)) for a chosen base point p0 on the line.
///
/// Using the direct formula with the signed distance:
/// t_± = (-(a*cx + b*cy + c) ± sqrt(D)) / A
///   ... wait, this isn't right. Let me derive properly.
///
/// Parametrize: p(t) = center + t_perp * n_hat + t_along * dir_hat
/// Actually, for Cramer's rule style, use:
///
/// The t parameter along the line direction from the foot of perpendicular.
/// If we parametrize as p(t) = p0 + t * dir where p0 is the foot of
/// perpendicular from center to line, then:
///   p0 = center - ((a*cx+b*cy+c)/(a²+b²)) * (a, b)
///   t_± = ± sqrt(D) / A
///
/// For the general parametrization from an arbitrary base point on the line,
/// the formula is more complex. Let's use the standard quadratic approach.
///
/// Substituting p(t) = (x0 - b*t, y0 + a*t) into ||p - center||² = r²:
/// (x0 - b*t - cx)² + (y0 + a*t - cy)² = r²
/// Let u = x0 - cx, v = y0 - cy
/// (u - bt)² + (v + at)² = r²
/// u² - 2ubt + b²t² + v² + 2vat + a²t² = r²
/// (a²+b²)t² + 2(va - ub)t + (u²+v² - r²) = 0
///
/// For p0 on the line: a*x0 + b*y0 + c = 0
///
/// We don't fix p0; instead express everything in terms of the line and circle.
/// The intersection points as coordinates in F(sqrt(disc)):

/// Intersection point of a circle and line.
/// Returns coordinates as SpecQuadExt<F, R> where R::value() encodes the discriminant.
///
/// We use the closed-form:
///   x = cx - a*h/A ∓ b*sqrt(D)/A
///   y = cy - b*h/A ± a*sqrt(D)/A
/// where h = a*cx + b*cy + c, A = a²+b², D = A*r² - h².
pub open spec fn cl_intersection_x<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, plus: bool,
) -> SpecQuadExt<F, R> {
    let a_coef = cl_quad_a(line);
    let h = cl_signed_dist_num(circle, line);
    // re part: cx - a*h / A
    let re = circle.center.x.sub(line.a.mul(h).div(a_coef));
    // im part: ∓ b / A  (with sqrt(D) factored into the radicand)
    // The actual sqrt we need is sqrt(cl_discriminant), but R::value() is the radicand.
    // We need: im * sqrt(R::value()) = ∓ b * sqrt(D) / A
    // If R::value() ≡ D, then im = ∓ b / A.
    let im = if plus {
        line.b.neg().div(a_coef)
    } else {
        line.b.div(a_coef)
    };
    qext(re, im)
}

pub open spec fn cl_intersection_y<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, plus: bool,
) -> SpecQuadExt<F, R> {
    let a_coef = cl_quad_a(line);
    let h = cl_signed_dist_num(circle, line);
    // re part: cy - b*h / A
    let re = circle.center.y.sub(line.b.mul(h).div(a_coef));
    // im part: ± a / A
    let im = if plus {
        line.a.div(a_coef)
    } else {
        line.a.neg().div(a_coef)
    };
    qext(re, im)
}

/// Full intersection point.
pub open spec fn cl_intersection_point<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, plus: bool,
) -> Point2<SpecQuadExt<F, R>> {
    Point2 {
        x: cl_intersection_x(circle, line, plus),
        y: cl_intersection_y(circle, line, plus),
    }
}

// ===========================================================================
//  Lemmas
// ===========================================================================

/// The intersection point lies on the line (lifted to SpecQuadExt).
pub proof fn lemma_cl_intersection_on_line<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, plus: bool,
)
    requires
        line2_nondegenerate(line),
        R::value().eqv(cl_discriminant(circle, line)),
        F::zero().lt(cl_discriminant(circle, line)),
    ensures
        point_on_line2(
            crate::constructed_scalar::lift_line2::<F, R>(line),
            cl_intersection_point(circle, line, plus),
        ),
{
    assume(false); // Deferred: algebraic verification
}

/// The intersection point lies on the circle.
pub proof fn lemma_cl_intersection_on_circle<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, plus: bool,
)
    requires
        line2_nondegenerate(line),
        R::value().eqv(cl_discriminant(circle, line)),
        F::zero().lt(cl_discriminant(circle, line)),
    ensures
        // sq_dist(intersection, center) ≡ r² (in SpecQuadExt)
        sq_dist_2d(
            cl_intersection_point::<F, R>(circle, line, plus),
            crate::constructed_scalar::lift_point2::<F, R>(circle.center),
        ).eqv(crate::constructed_scalar::qext_from_rational::<F, R>(circle.radius_sq)),
{
    assume(false); // Deferred: uses quadratic_root_satisfies from Phase 1
}

/// cl_quad_a > 0 for non-degenerate lines.
pub proof fn lemma_cl_quad_a_positive<F: OrderedField>(line: Line2<F>)
    requires
        line2_nondegenerate(line),
    ensures
        F::zero().lt(cl_quad_a(line)),
{
    use verus_algebra::lemmas::ordered_ring_lemmas::*;
    use verus_quadratic_extension::ordered::lemma_square_pos;
    // line2_nondegenerate: !a.eqv(0) || !b.eqv(0)
    // cl_quad_a = a*a + b*b
    if !line.a.eqv(F::zero()) {
        lemma_square_pos::<F>(line.a); // 0 < a*a
        lemma_square_nonneg::<F>(line.b); // 0 <= b*b
        lemma_add_pos_nonneg::<F>(line.a.mul(line.a), line.b.mul(line.b));
    } else {
        lemma_square_nonneg::<F>(line.a); // 0 <= a*a
        lemma_square_pos::<F>(line.b); // 0 < b*b
        lemma_add_nonneg_pos::<F>(line.a.mul(line.a), line.b.mul(line.b));
    }
}

} // verus!
