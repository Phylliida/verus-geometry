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

// ===========================================================================
//  Helpers for on-circle proof (see also circle_line_on_circle.rs)
// ===========================================================================

/// (a - b) - a ≡ -b.
pub proof fn lemma_sub_from_self<T: Ring>(a: T, b: T)
    ensures
        a.sub(b).sub(a).eqv(b.neg()),
{
    // a.sub(b) ≡ a.add(b.neg())
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_eqv_reflexive(a);
    lemma_sub_congruence::<T>(a.sub(b), a.add(b.neg()), a, a);
    // a.add(b.neg()).sub(a) ≡ b.neg()
    crate::segment_distance::lemma_add_sub_cancel_left(a, b.neg());
    T::axiom_eqv_transitive(
        a.sub(b).sub(a), a.add(b.neg()).sub(a), b.neg(),
    );
}

/// a/c + b/c ≡ (a + b)/c for c ≠ 0.
pub proof fn lemma_div_add_same_denom<F: Field>(a: F, b: F, c: F)
    requires
        !c.eqv(F::zero()),
    ensures
        a.div(c).add(b.div(c)).eqv(a.add(b).div(c)),
{
    let r = c.recip();
    // a/c ≡ a*r, b/c ≡ b*r
    F::axiom_div_is_mul_recip(a, c);
    F::axiom_div_is_mul_recip(b, c);
    // a/c + b/c ≡ a*r + b*r
    lemma_add_congruence::<F>(a.div(c), a.mul(r), b.div(c), b.mul(r));
    // a*r + b*r ≡ (a+b)*r  (right distributes, reversed)
    lemma_mul_distributes_right::<F>(a, b, r);
    F::axiom_eqv_symmetric(a.add(b).mul(r), a.mul(r).add(b.mul(r)));
    // (a+b)*r ≡ (a+b)/c
    F::axiom_div_is_mul_recip(a.add(b), c);
    F::axiom_eqv_symmetric(a.add(b).div(c), a.add(b).mul(r));
    // Chain: a/c + b/c ≡ a*r + b*r ≡ (a+b)*r ≡ (a+b)/c
    F::axiom_eqv_transitive(
        a.mul(r).add(b.mul(r)), a.add(b).mul(r), a.add(b).div(c),
    );
    F::axiom_eqv_transitive(
        a.div(c).add(b.div(c)), a.mul(r).add(b.mul(r)), a.add(b).div(c),
    );
}

/// Four fractions with same denominator: a/d + b/d + c/d + e/d ≡ (a+b+c+e)/d.
pub proof fn lemma_four_div_same_denom<F: Field>(a: F, b: F, c: F, e: F, d: F)
    requires
        !d.eqv(F::zero()),
    ensures
        a.div(d).add(b.div(d)).add(c.div(d).add(e.div(d))).eqv(
            a.add(b).add(c.add(e)).div(d),
        ),
{
    // a/d + b/d ≡ (a+b)/d
    lemma_div_add_same_denom(a, b, d);
    // c/d + e/d ≡ (c+e)/d
    lemma_div_add_same_denom(c, e, d);
    // (a+b)/d + (c+e)/d ≡ ((a+b)+(c+e))/d
    lemma_div_add_same_denom(a.add(b), c.add(e), d);
    // Chain: LHS ≡ (a+b)/d + (c+e)/d ≡ ((a+b)+(c+e))/d
    lemma_add_congruence::<F>(
        a.div(d).add(b.div(d)), a.add(b).div(d),
        c.div(d).add(e.div(d)), c.add(e).div(d),
    );
    F::axiom_eqv_transitive(
        a.div(d).add(b.div(d)).add(c.div(d).add(e.div(d))),
        a.add(b).div(d).add(c.add(e).div(d)),
        a.add(b).add(c.add(e)).div(d),
    );
}

// ===========================================================================
//  Helpers for on-line proof
// ===========================================================================

/// (a - b) + (c - d) ≡ (a + c) - (b + d).
proof fn lemma_sub_add_sub<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).add(c.sub(d)).eqv(a.add(c).sub(b.add(d))),
{
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_sub_is_add_neg(c, d);
    lemma_add_congruence::<T>(
        a.sub(b), a.add(b.neg()),
        c.sub(d), c.add(d.neg()),
    );
    lemma_add_rearrange_2x2::<T>(a, b.neg(), c, d.neg());
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(b.neg()).add(c.add(d.neg())),
        a.add(c).add(b.neg().add(d.neg())),
    );
    lemma_neg_add::<T>(b, d);
    T::axiom_eqv_symmetric(b.add(d).neg(), b.neg().add(d.neg()));
    lemma_add_congruence_right::<T>(a.add(c), b.neg().add(d.neg()), b.add(d).neg());
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).add(b.neg().add(d.neg())),
        a.add(c).add(b.add(d).neg()),
    );
    T::axiom_sub_is_add_neg(a.add(c), b.add(d));
    T::axiom_eqv_symmetric(a.add(c).sub(b.add(d)), a.add(c).add(b.add(d).neg()));
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).add(b.add(d).neg()),
        a.add(c).sub(b.add(d)),
    );
}

/// (x - y) + z ≡ (x + z) - y.
proof fn lemma_sub_add_swap<T: Ring>(x: T, y: T, z: T)
    ensures
        x.sub(y).add(z).eqv(x.add(z).sub(y)),
{
    T::axiom_sub_is_add_neg(x, y);
    T::axiom_add_congruence_left(x.sub(y), x.add(y.neg()), z);
    // (x-y)+z ≡ (x+(-y))+z
    T::axiom_add_associative(x, y.neg(), z);
    T::axiom_add_commutative(y.neg(), z);
    lemma_add_congruence_right::<T>(x, y.neg().add(z), z.add(y.neg()));
    T::axiom_eqv_transitive(
        x.add(y.neg()).add(z), x.add(y.neg().add(z)), x.add(z.add(y.neg())),
    );
    T::axiom_add_associative(x, z, y.neg());
    T::axiom_eqv_symmetric(x.add(z).add(y.neg()), x.add(z.add(y.neg())));
    T::axiom_eqv_transitive(
        x.add(y.neg()).add(z), x.add(z.add(y.neg())), x.add(z).add(y.neg()),
    );
    // (x+(-y))+z ≡ (x+z)+(-y)
    T::axiom_eqv_transitive(
        x.sub(y).add(z), x.add(y.neg()).add(z), x.add(z).add(y.neg()),
    );
    T::axiom_sub_is_add_neg(x.add(z), y);
    T::axiom_eqv_symmetric(x.add(z).sub(y), x.add(z).add(y.neg()));
    T::axiom_eqv_transitive(
        x.sub(y).add(z), x.add(z).add(y.neg()), x.add(z).sub(y),
    );
}

/// v - u/d ≡ (v*d - u)/d for d ≠ 0.
proof fn lemma_sub_div_as_frac<F: OrderedField>(v: F, u: F, d: F)
    requires
        !d.eqv(F::zero()),
    ensures
        v.sub(u.div(d)).eqv(v.mul(d).sub(u).div(d)),
{
    // v ≡ v*d/d
    lemma_mul_div_cancel::<F>(v, d);
    F::axiom_eqv_symmetric(v.mul(d).div(d), v);
    // v - u/d ≡ v*d/d - u/d
    F::axiom_eqv_reflexive(u.div(d));
    lemma_sub_congruence::<F>(v, v.mul(d).div(d), u.div(d), u.div(d));
    // v*d/d - u/d ≡ (v*d - u)/d: sub with same denominator
    let r = d.recip();
    F::axiom_div_is_mul_recip(v.mul(d), d);
    F::axiom_div_is_mul_recip(u, d);
    lemma_sub_congruence::<F>(
        v.mul(d).div(d), v.mul(d).mul(r), u.div(d), u.mul(r),
    );
    // r*(vd-u) ≡ r*vd - r*u
    lemma_mul_distributes_over_sub::<F>(r, v.mul(d), u);
    // r*vd ≡ vd*r, r*u ≡ u*r
    F::axiom_mul_commutative(r, v.mul(d));
    F::axiom_mul_commutative(r, u);
    // r*vd - r*u ≡ vd*r - u*r
    lemma_sub_congruence::<F>(r.mul(v.mul(d)), v.mul(d).mul(r), r.mul(u), u.mul(r));
    // r*(vd-u) ≡ vd*r - u*r (transitive)
    F::axiom_eqv_transitive(
        r.mul(v.mul(d).sub(u)),
        r.mul(v.mul(d)).sub(r.mul(u)),
        v.mul(d).mul(r).sub(u.mul(r)),
    );
    // (vd-u)*r ≡ r*(vd-u)
    F::axiom_mul_commutative(v.mul(d).sub(u), r);
    // (vd-u)*r ≡ vd*r - u*r (transitive)
    F::axiom_eqv_transitive(
        v.mul(d).sub(u).mul(r),
        r.mul(v.mul(d).sub(u)),
        v.mul(d).mul(r).sub(u.mul(r)),
    );
    // (vd-u)/d ≡ (vd-u)*r
    F::axiom_div_is_mul_recip(v.mul(d).sub(u), d);
    // (vd-u)/d ≡ vd*r - u*r (transitive)
    F::axiom_eqv_transitive(
        v.mul(d).sub(u).div(d),
        v.mul(d).sub(u).mul(r),
        v.mul(d).mul(r).sub(u.mul(r)),
    );
    // vd*r - u*r ≡ (vd-u)/d (symmetric)
    F::axiom_eqv_symmetric(
        v.mul(d).sub(u).div(d),
        v.mul(d).mul(r).sub(u.mul(r)),
    );
    // vd/d - u/d ≡ (vd-u)/d (transitive via vd*r - u*r)
    F::axiom_eqv_transitive(
        v.mul(d).div(d).sub(u.div(d)),
        v.mul(d).mul(r).sub(u.mul(r)),
        v.mul(d).sub(u).div(d),
    );
    // v - u/d ≡ (vd-u)/d (transitive)
    F::axiom_eqv_transitive(
        v.sub(u.div(d)),
        v.mul(d).div(d).sub(u.div(d)),
        v.mul(d).sub(u).div(d),
    );
}

/// Numerator identity: a*(cx*A - a*h) + b*(cy*A - b*h) + c*A ≡ 0
/// where h = a*cx + b*cy + c and A = a² + b².
proof fn lemma_cl_on_line_numerator<T: Ring>(a: T, b: T, c: T, cx: T, cy: T)
    ensures ({
        let big_a = a.mul(a).add(b.mul(b));
        let h = a.mul(cx).add(b.mul(cy)).add(c);
        let x_num = cx.mul(big_a).sub(a.mul(h));
        let y_num = cy.mul(big_a).sub(b.mul(h));
        a.mul(x_num).add(b.mul(y_num)).add(c.mul(big_a)).eqv(T::zero())
    }),
{
    let big_a = a.mul(a).add(b.mul(b));
    let h = a.mul(cx).add(b.mul(cy)).add(c);
    let x_num = cx.mul(big_a).sub(a.mul(h));
    let y_num = cy.mul(big_a).sub(b.mul(h));
    let e = a.mul(x_num).add(b.mul(y_num)).add(c.mul(big_a));

    // Phase 1: Distribute each outer mul over sub
    lemma_mul_distributes_over_sub::<T>(a, cx.mul(big_a), a.mul(h));
    lemma_mul_distributes_over_sub::<T>(b, cy.mul(big_a), b.mul(h));
    // a*x_num ≡ a*(cx*A) - a*(a*h)
    // b*y_num ≡ b*(cy*A) - b*(b*h)

    // Phase 2: Reassociate products
    T::axiom_mul_associative(a, cx, big_a);
    T::axiom_eqv_symmetric(a.mul(cx).mul(big_a), a.mul(cx.mul(big_a)));
    T::axiom_mul_associative(a, a, h);
    T::axiom_eqv_symmetric(a.mul(a).mul(h), a.mul(a.mul(h)));
    T::axiom_mul_associative(b, cy, big_a);
    T::axiom_eqv_symmetric(b.mul(cy).mul(big_a), b.mul(cy.mul(big_a)));
    T::axiom_mul_associative(b, b, h);
    T::axiom_eqv_symmetric(b.mul(b).mul(h), b.mul(b.mul(h)));

    // a*(cx*A) ≡ (a*cx)*A, a*(a*h) ≡ (a*a)*h, etc.
    // Sub congruence for each distributed pair
    T::axiom_eqv_reflexive(a.mul(cx).mul(big_a));
    lemma_sub_congruence::<T>(
        a.mul(cx.mul(big_a)), a.mul(cx).mul(big_a),
        a.mul(a.mul(h)), a.mul(a).mul(h),
    );
    // a*x_num ≡ (a*cx)*A - (a*a)*h (by transitive with distributes)
    T::axiom_eqv_transitive(
        a.mul(x_num),
        a.mul(cx.mul(big_a)).sub(a.mul(a.mul(h))),
        a.mul(cx).mul(big_a).sub(a.mul(a).mul(h)),
    );

    T::axiom_eqv_reflexive(b.mul(cy).mul(big_a));
    lemma_sub_congruence::<T>(
        b.mul(cy.mul(big_a)), b.mul(cy).mul(big_a),
        b.mul(b.mul(h)), b.mul(b).mul(h),
    );
    T::axiom_eqv_transitive(
        b.mul(y_num),
        b.mul(cy.mul(big_a)).sub(b.mul(b.mul(h))),
        b.mul(cy).mul(big_a).sub(b.mul(b).mul(h)),
    );

    // Phase 3: Rearrange sum using (X-Y)+(Z-W) = (X+Z)-(Y+W)
    lemma_sub_add_sub::<T>(
        a.mul(cx).mul(big_a), a.mul(a).mul(h),
        b.mul(cy).mul(big_a), b.mul(b).mul(h),
    );
    // Add congruence to connect to original expression
    lemma_add_congruence::<T>(
        a.mul(x_num), a.mul(cx).mul(big_a).sub(a.mul(a).mul(h)),
        b.mul(y_num), b.mul(cy).mul(big_a).sub(b.mul(b).mul(h)),
    );
    let pos = a.mul(cx).mul(big_a).add(b.mul(cy).mul(big_a));
    let neg = a.mul(a).mul(h).add(b.mul(b).mul(h));
    T::axiom_eqv_transitive(
        a.mul(x_num).add(b.mul(y_num)),
        a.mul(cx).mul(big_a).sub(a.mul(a).mul(h))
            .add(b.mul(cy).mul(big_a).sub(b.mul(b).mul(h))),
        pos.sub(neg),
    );

    // Phase 4: Swap (pos - neg) + c*A ≡ (pos + c*A) - neg
    lemma_sub_add_swap::<T>(pos, neg, c.mul(big_a));
    T::axiom_add_congruence_left(
        a.mul(x_num).add(b.mul(y_num)), pos.sub(neg), c.mul(big_a),
    );
    T::axiom_eqv_transitive(e, pos.sub(neg).add(c.mul(big_a)), pos.add(c.mul(big_a)).sub(neg));

    // Phase 5: Factor positive: pos + c*A = (a*cx + b*cy + c)*A = h*A
    // (a*cx)*A + (b*cy)*A ≡ (a*cx + b*cy)*A
    lemma_mul_distributes_right::<T>(a.mul(cx), b.mul(cy), big_a);
    T::axiom_eqv_symmetric(
        a.mul(cx).add(b.mul(cy)).mul(big_a),
        a.mul(cx).mul(big_a).add(b.mul(cy).mul(big_a)),
    );
    // ((a*cx + b*cy)*A) + c*A ≡ ((a*cx + b*cy) + c)*A = h*A
    lemma_mul_distributes_right::<T>(a.mul(cx).add(b.mul(cy)), c, big_a);
    T::axiom_eqv_symmetric(
        a.mul(cx).add(b.mul(cy)).add(c).mul(big_a),
        a.mul(cx).add(b.mul(cy)).mul(big_a).add(c.mul(big_a)),
    );
    // Chain: pos + c*A ≡ (a*cx+b*cy)*A + c*A ≡ h*A
    T::axiom_add_congruence_left(pos, a.mul(cx).add(b.mul(cy)).mul(big_a), c.mul(big_a));
    T::axiom_eqv_transitive(
        pos.add(c.mul(big_a)),
        a.mul(cx).add(b.mul(cy)).mul(big_a).add(c.mul(big_a)),
        h.mul(big_a),
    );

    // Phase 6: Factor negative: neg = (a*a + b*b)*h = A*h
    lemma_mul_distributes_right::<T>(a.mul(a), b.mul(b), h);
    T::axiom_eqv_symmetric(big_a.mul(h), neg);

    // Phase 7: h*A - A*h ≡ 0
    T::axiom_mul_commutative(h, big_a);
    lemma_sub_congruence::<T>(
        pos.add(c.mul(big_a)), h.mul(big_a), neg, big_a.mul(h),
    );
    T::axiom_eqv_reflexive(big_a.mul(h));
    lemma_sub_congruence::<T>(h.mul(big_a), big_a.mul(h), big_a.mul(h), big_a.mul(h));
    lemma_sub_self::<T>(big_a.mul(h));
    T::axiom_eqv_transitive(
        h.mul(big_a).sub(big_a.mul(h)), big_a.mul(h).sub(big_a.mul(h)), T::zero(),
    );
    // pos + c*A - neg ≡ h*A - A*h ≡ 0
    T::axiom_eqv_transitive(
        pos.add(c.mul(big_a)).sub(neg),
        h.mul(big_a).sub(big_a.mul(h)),
        T::zero(),
    );
    // e ≡ pos+cA - neg ≡ 0
    T::axiom_eqv_transitive(e, pos.add(c.mul(big_a)).sub(neg), T::zero());
}

// ===========================================================================
//  Main on-line proof
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
    use crate::constructed_scalar::*;
    use crate::line_intersection::{lemma_mul_div_assoc, lemma_ll_eval_from_numerator};

    let a = line.a;
    let b = line.b;
    let c = line.c;
    let cx = circle.center.x;
    let cy = circle.center.y;
    let big_a = cl_quad_a(line);
    let h = cl_signed_dist_num(circle, line);

    // A > 0 hence A ≠ 0
    lemma_cl_quad_a_positive(line);
    assert(!big_a.eqv(F::zero())) by {
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
        if big_a.eqv(F::zero()) {
            F::axiom_eqv_symmetric(big_a, F::zero());
        }
    };

    // Intersection point components
    let px = cl_intersection_x::<F, R>(circle, line, plus);
    let py = cl_intersection_y::<F, R>(circle, line, plus);
    let rx = px.re;
    let ry = py.re;
    let ix = px.im;
    let iy = py.im;

    // === SpecQuadExt: simplify multiplications ===
    let ap = qext_from_rational::<F, R>(a);
    let bp = qext_from_rational::<F, R>(b);
    let cp = qext_from_rational::<F, R>(c);
    lemma_rational_mul_qext::<F, R>(a, rx, ix);
    lemma_rational_mul_qext::<F, R>(b, ry, iy);
    lemma_add_congruence::<SpecQuadExt<F, R>>(
        ap.mul(px), qext::<F, R>(a.mul(rx), a.mul(ix)),
        bp.mul(py), qext::<F, R>(b.mul(ry), b.mul(iy)),
    );
    SpecQuadExt::<F, R>::axiom_add_congruence_left(
        ap.mul(px).add(bp.mul(py)),
        qext::<F, R>(a.mul(rx).add(b.mul(ry)), a.mul(ix).add(b.mul(iy))),
        cp,
    );
    // eval ≡ qext((a*rx+b*ry)+c, (a*ix+b*iy)+0)

    // === Imaginary part ≡ 0 ===
    F::axiom_add_zero_right(a.mul(ix).add(b.mul(iy)));
    let t = a.mul(b).div(big_a);

    if plus {
        // ix = b.neg().div(big_a), iy = a.div(big_a)
        // Show a*ix ≡ -t
        lemma_mul_div_assoc::<F>(a, b.neg(), big_a);
        lemma_mul_neg_right::<F>(a, b);
        F::axiom_eqv_reflexive(big_a);
        lemma_div_congruence::<F>(a.mul(b.neg()), a.mul(b).neg(), big_a, big_a);
        F::axiom_eqv_transitive(
            a.mul(b.neg().div(big_a)), a.mul(b.neg()).div(big_a), a.mul(b).neg().div(big_a),
        );
        lemma_div_neg_numerator::<F>(a.mul(b), big_a);
        F::axiom_eqv_transitive(
            a.mul(b.neg().div(big_a)), a.mul(b).neg().div(big_a), t.neg(),
        );
        // Show b*iy ≡ t
        lemma_mul_div_assoc::<F>(b, a, big_a);
        F::axiom_mul_commutative(b, a);
        lemma_div_congruence::<F>(b.mul(a), a.mul(b), big_a, big_a);
        F::axiom_eqv_transitive(b.mul(a.div(big_a)), b.mul(a).div(big_a), t);
        // -t + t ≡ 0
        lemma_add_congruence::<F>(a.mul(ix), t.neg(), b.mul(iy), t);
        lemma_add_inverse_left::<F>(t);
        F::axiom_eqv_transitive(a.mul(ix).add(b.mul(iy)), t.neg().add(t), F::zero());
    } else {
        // ix = b.div(big_a), iy = a.neg().div(big_a)
        // Show a*ix ≡ t
        lemma_mul_div_assoc::<F>(a, b, big_a);
        // Show b*iy ≡ -t
        lemma_mul_div_assoc::<F>(b, a.neg(), big_a);
        lemma_mul_neg_right::<F>(b, a);
        F::axiom_mul_commutative(b, a);
        lemma_neg_congruence::<F>(b.mul(a), a.mul(b));
        F::axiom_eqv_transitive(b.mul(a.neg()), b.mul(a).neg(), a.mul(b).neg());
        F::axiom_eqv_reflexive(big_a);
        lemma_div_congruence::<F>(b.mul(a.neg()), a.mul(b).neg(), big_a, big_a);
        F::axiom_eqv_transitive(
            b.mul(a.neg().div(big_a)), b.mul(a.neg()).div(big_a), a.mul(b).neg().div(big_a),
        );
        lemma_div_neg_numerator::<F>(a.mul(b), big_a);
        F::axiom_eqv_transitive(b.mul(a.neg().div(big_a)), a.mul(b).neg().div(big_a), t.neg());
        // t + (-t) ≡ 0
        lemma_add_congruence::<F>(a.mul(ix), t, b.mul(iy), t.neg());
        F::axiom_add_inverse_right(t);
        F::axiom_eqv_transitive(a.mul(ix).add(b.mul(iy)), t.add(t.neg()), F::zero());
    }
    // (a*ix + b*iy) + 0 ≡ a*ix + b*iy ≡ 0
    F::axiom_eqv_transitive(
        a.mul(ix).add(b.mul(iy)).add(F::zero()),
        a.mul(ix).add(b.mul(iy)),
        F::zero(),
    );

    // === Real part ≡ 0 ===
    // Use numerator approach: a*x_num + b*y_num + c*A ≡ 0
    let x_num = cx.mul(big_a).sub(a.mul(h));
    let y_num = cy.mul(big_a).sub(b.mul(h));
    lemma_cl_on_line_numerator::<F>(a, b, c, cx, cy);
    lemma_ll_eval_from_numerator::<F>(a, b, c, x_num, y_num, big_a);
    // → a*(x_num/A) + b*(y_num/A) + c ≡ 0

    // Bridge: rx ≡ x_num/A and ry ≡ y_num/A
    lemma_sub_div_as_frac::<F>(cx, a.mul(h), big_a);
    lemma_sub_div_as_frac::<F>(cy, b.mul(h), big_a);
    // Congruence: a*rx ≡ a*(x_num/A), b*ry ≡ b*(y_num/A)
    lemma_mul_congruence_right::<F>(a, rx, x_num.div(big_a));
    lemma_mul_congruence_right::<F>(b, ry, y_num.div(big_a));
    // Chain: a*rx + b*ry + c ≡ a*(x_num/A) + b*(y_num/A) + c ≡ 0
    lemma_add_congruence::<F>(
        a.mul(rx), a.mul(x_num.div(big_a)),
        b.mul(ry), b.mul(y_num.div(big_a)),
    );
    F::axiom_add_congruence_left(
        a.mul(rx).add(b.mul(ry)),
        a.mul(x_num.div(big_a)).add(b.mul(y_num.div(big_a))),
        c,
    );
    F::axiom_eqv_transitive(
        a.mul(rx).add(b.mul(ry)).add(c),
        a.mul(x_num.div(big_a)).add(b.mul(y_num.div(big_a))).add(c),
        F::zero(),
    );

    // === Final: eval ≡ qe_zero ===
    let eval = line2_eval(
        lift_line2::<F, R>(line),
        cl_intersection_point::<F, R>(circle, line, plus),
    );
    let simplified = qext::<F, R>(
        a.mul(rx).add(b.mul(ry)).add(c),
        a.mul(ix).add(b.mul(iy)).add(F::zero()),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(eval, simplified, qe_zero::<F, R>());
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
    use crate::constructed_scalar::*;
    use crate::circle_line_on_circle::*;

    let a = line.a;
    let b = line.b;
    let cx = circle.center.x;
    let cy = circle.center.y;
    let rsq = circle.radius_sq;
    let big_a = cl_quad_a(line);
    let h = cl_signed_dist_num(circle, line);
    let d = R::value();

    // A > 0 hence A ≠ 0
    lemma_cl_quad_a_positive(line);
    assert(!big_a.eqv(F::zero())) by {
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
        if big_a.eqv(F::zero()) {
            F::axiom_eqv_symmetric(big_a, F::zero());
        }
    };

    // Intersection point and lifted center
    let P = cl_intersection_point::<F, R>(circle, line, plus);
    let C = lift_point2::<F, R>(circle.center);
    let px = cl_intersection_x::<F, R>(circle, line, plus);
    let py = cl_intersection_y::<F, R>(circle, line, plus);
    let rx = px.re;
    let ry = py.re;
    let ix = px.im;
    let iy = py.im;

    // Simplified diff components
    let dr = a.mul(h).div(big_a).neg();
    let er = b.mul(h).div(big_a).neg();
    let di = ix;
    let ei = iy;

    // === Phase 1: F-level simplifications of diff components ===
    // rx.sub(cx) ≡ neg(ah/A)
    lemma_sub_from_self::<F>(cx, a.mul(h).div(big_a));
    // ix.sub(0) ≡ ix
    crate::incircle::lemma_sub_zero_right::<F>(ix);
    // ry.sub(cy) ≡ neg(bh/A)
    lemma_sub_from_self::<F>(cy, b.mul(h).div(big_a));
    // iy.sub(0) ≡ iy
    crate::incircle::lemma_sub_zero_right::<F>(iy);

    // === Phase 2: SpecQuadExt-level diff simplification ===
    // Z3 unfolds sub2(P,C).x = qext(rx.sub(cx), ix.sub(0))
    // From Phase 1 component eqvs, Z3 derives:
    //   sub2(P,C).x ≡QE qext(dr, di) = sdx
    //   sub2(P,C).y ≡QE qext(er, ei) = sdy
    let dx = P.x.sub(C.x);
    let dy = P.y.sub(C.y);
    let sdx = qext::<F, R>(dr, di);
    let sdy = qext::<F, R>(er, ei);

    // Help Z3 see the QE-level eqvs from component eqvs
    assert(dx.eqv(sdx));
    assert(dy.eqv(sdy));

    // === Phase 3: Propagate through mul and add at QE level ===
    lemma_mul_congruence::<SpecQuadExt<F, R>>(dx, sdx, dx, sdx);
    lemma_mul_congruence::<SpecQuadExt<F, R>>(dy, sdy, dy, sdy);
    lemma_add_congruence::<SpecQuadExt<F, R>>(
        dx.mul(dx), sdx.mul(sdx),
        dy.mul(dy), sdy.mul(sdy),
    );
    // sq_dist ≡QE sdx.mul(sdx).add(sdy.mul(sdy))

    let sq = sdx.mul(sdx).add(sdy.mul(sdy));
    let target = qext_from_rational::<F, R>(rsq);

    // === Phase 4: Imaginary part ≡ 0 ===
    // sq.im = (dr*di + di*dr) + (er*ei + ei*er)
    if plus {
        lemma_cl_cross_cancel_plus(a, b, h, big_a);
    } else {
        lemma_cl_cross_cancel_minus(a, b, h, big_a);
    }
    lemma_cl_full_im_zero(dr, di, er, ei);
    // Now: sq.im ≡ F::zero() = target.im

    // === Phase 5: Real part ≡ rsq ===
    // sq.re = (dr² + di²*D) + (er² + ei²*D) where D = R::value()
    // big_a ≡ a²+b² (definitional via cl_quad_a)
    F::axiom_eqv_reflexive(big_a);
    lemma_cl_re_with_d(a, b, h, big_a, rsq, d, plus);
    // Now: sq.re ≡ rsq = target.re

    // === Phase 6: Conclude SpecQuadExt eqv ===
    // Z3 sees: sq.re ≡ target.re and sq.im ≡ target.im
    // qe_eqv is component-wise → sq ≡ target
    assert(sq.eqv(target));

    // Chain: sq_dist_2d(P, C) ≡ sq ≡ target
    let sd = sq_dist_2d(P, C);
    SpecQuadExt::<F, R>::axiom_eqv_transitive(sd, sq, target);
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

// ===========================================================================
//  Displacement sign determination
// ===========================================================================

/// The rational expression whose sign determines which circle-line
/// intersection is closer to target Q.
///
/// sign_expr = a·(cy - Qy) - b·(cx - Qx)
///
/// If sign_expr > 0: P_plus (plus=true) is closer to Q.
/// If sign_expr < 0: P_minus (plus=false) is closer to Q.
/// If sign_expr = 0: both are equidistant.
pub open spec fn cl_displacement_sign<F: OrderedField>(
    circle: Circle2<F>, line: Line2<F>, target: Point2<F>,
) -> F {
    line.a.mul(circle.center.y.sub(target.y))
        .sub(line.b.mul(circle.center.x.sub(target.x)))
}

/// k * (a - b) ≡ k*a - k*b (left distribution over subtraction).
proof fn lemma_mul_sub_left<R: Ring>(k: R, a: R, b: R)
    ensures
        k.mul(a.sub(b)).eqv(k.mul(a).sub(k.mul(b))),
{
    // a - b ≡ a + neg(b)
    R::axiom_sub_is_add_neg(a, b);
    R::axiom_mul_congruence_left(a.sub(b), a.add(b.neg()), k);
    // k*(a+neg(b)) ≡ k*a + k*neg(b)
    R::axiom_mul_distributes_left(k, a, b.neg());
    // k*neg(b) ≡ neg(k*b)
    lemma_mul_neg_right::<R>(k, b);
    lemma_add_congruence_right::<R>(k.mul(a), k.mul(b.neg()), k.mul(b).neg());
    // k*a + neg(k*b) ≡ k*a - k*b
    R::axiom_sub_is_add_neg(k.mul(a), k.mul(b));
    R::axiom_eqv_symmetric(k.mul(a).sub(k.mul(b)), k.mul(a).add(k.mul(b).neg()));
    // Chain
    R::axiom_eqv_transitive(k.mul(a.sub(b)), k.mul(a.add(b.neg())), k.mul(a).add(k.mul(b.neg())));
    R::axiom_eqv_transitive(k.mul(a.sub(b)), k.mul(a).add(k.mul(b.neg())), k.mul(a).add(k.mul(b).neg()));
    R::axiom_eqv_transitive(k.mul(a.sub(b)), k.mul(a).add(k.mul(b).neg()), k.mul(a).sub(k.mul(b)));
}

/// The key cancellation: neg(b)·neg(v) + a·neg(w) ≡ 0
/// when v = a·t and w = b·t (so neg(b)·neg(a·t) = b·a·t and a·neg(b·t) = neg(a·b·t),
/// and b·a·t ≡ a·b·t by commutativity, so they cancel).
proof fn lemma_cross_term_cancel<R: Ring>(a: R, b: R, t: R)
    ensures
        b.neg().mul(a.mul(t).neg()).add(a.mul(b.mul(t).neg())).eqv(R::zero()),
{
    // neg(b)*neg(a*t) ≡ b*(a*t) by neg*neg
    lemma_neg_mul_neg::<R>(b, a.mul(t));
    // b*(a*t) ≡ (b*a)*t by associativity
    R::axiom_mul_associative(b, a, t);
    // (b*a)*t ≡ (a*b)*t by commutativity of b*a
    R::axiom_mul_commutative(b, a);
    R::axiom_mul_congruence_left(b.mul(a), a.mul(b), t);
    // (a*b)*t ≡ a*(b*t) by associativity
    R::axiom_mul_associative(a, b, t);
    R::axiom_eqv_symmetric(a.mul(b.mul(t)), a.mul(b).mul(t));
    // Chain: neg(b)*neg(a*t) ≡ b*(a*t) ≡ (b*a)*t ≡ (a*b)*t ≡ a*(b*t)
    R::axiom_eqv_transitive(b.neg().mul(a.mul(t).neg()), b.mul(a.mul(t)), b.mul(a).mul(t));
    R::axiom_eqv_transitive(b.neg().mul(a.mul(t).neg()), b.mul(a).mul(t), a.mul(b).mul(t));
    R::axiom_eqv_transitive(b.neg().mul(a.mul(t).neg()), a.mul(b).mul(t), a.mul(b.mul(t)));

    // a*neg(b*t) ≡ neg(a*(b*t))
    lemma_mul_neg_right::<R>(a, b.mul(t));

    // So LHS = a*(b*t) + neg(a*(b*t)) ≡ 0
    lemma_add_congruence::<R>(
        b.neg().mul(a.mul(t).neg()), a.mul(b.mul(t)),
        a.mul(b.mul(t).neg()), a.mul(b.mul(t)).neg());
    // a*(b*t) + neg(a*(b*t)) ≡ 0
    R::axiom_add_inverse_right(a.mul(b.mul(t)));
    R::axiom_eqv_transitive(
        b.neg().mul(a.mul(t).neg()).add(a.mul(b.mul(t).neg())),
        a.mul(b.mul(t)).add(a.mul(b.mul(t)).neg()),
        R::zero());
}

/// (a - b) - c ≡ (a - c) - b. Rearranges a double subtraction.
proof fn lemma_sub_sub_swap<A: AdditiveGroup>(a: A, b: A, c: A)
    ensures a.sub(b).sub(c).eqv(a.sub(c).sub(b)),
{
    // a-b-c = a+neg(b)+neg(c) = a+neg(c)+neg(b) = a-c-b
    A::axiom_sub_is_add_neg(a, b);
    A::axiom_sub_is_add_neg(a.sub(b), c);
    // a.sub(b).sub(c) ≡ (a+neg(b))+neg(c) = a+(neg(b)+neg(c))
    lemma_add_congruence::<A>(a.sub(b), a.add(b.neg()), c.neg(), c.neg());
    A::axiom_eqv_reflexive(c.neg());
    A::axiom_add_associative(a, b.neg(), c.neg());
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.sub(b).add(c.neg()), a.add(b.neg()).add(c.neg()));
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.add(b.neg()).add(c.neg()), a.add(b.neg().add(c.neg())));
    // Commute neg(b) and neg(c)
    A::axiom_add_commutative(b.neg(), c.neg());
    lemma_add_congruence_right::<A>(a, b.neg().add(c.neg()), c.neg().add(b.neg()));
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.add(b.neg().add(c.neg())), a.add(c.neg().add(b.neg())));
    // Reassociate: a+(neg(c)+neg(b)) = (a+neg(c))+neg(b)
    A::axiom_add_associative(a, c.neg(), b.neg());
    A::axiom_eqv_symmetric(a.add(c.neg()).add(b.neg()), a.add(c.neg().add(b.neg())));
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.add(c.neg().add(b.neg())), a.add(c.neg()).add(b.neg()));
    // a+neg(c) ≡ a-c
    A::axiom_sub_is_add_neg(a, c);
    A::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    A::axiom_add_congruence_left(a.add(c.neg()), a.sub(c), b.neg());
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.add(c.neg()).add(b.neg()), a.sub(c).add(b.neg()));
    // (a-c)+neg(b) ≡ (a-c)-b
    A::axiom_sub_is_add_neg(a.sub(c), b);
    A::axiom_eqv_symmetric(a.sub(c).sub(b), a.sub(c).add(b.neg()));
    A::axiom_eqv_transitive(a.sub(b).sub(c), a.sub(c).add(b.neg()), a.sub(c).sub(b));
}

/// Main displacement sign lemma (inner product form).
///
/// neg(b)·(cx - v - qx) + a·(cy - w - qy) ≡ a·(cy-qy) - b·(cx-qx)
/// when v = a·t and w = b·t (the cross terms cancel).
proof fn lemma_cl_displacement_cancellation<F: OrderedField>(
    a: F, b: F, cx: F, cy: F, qx: F, qy: F, v: F, w: F, t: F,
)
    requires
        v.eqv(a.mul(t)),
        w.eqv(b.mul(t)),
    ensures
        b.neg().mul(cx.sub(v).sub(qx))
            .add(a.mul(cy.sub(w).sub(qy)))
            .eqv(a.mul(cy.sub(qy)).sub(b.mul(cx.sub(qx)))),
{
    // Strategy: use lemma_sub_sub_swap to rearrange, distribute, cancel cross terms.
    let u1 = cx.sub(qx);
    let u2 = cy.sub(qy);

    // Step 1: cx - v - qx ≡ (cx - qx) - v  and  cy - w - qy ≡ (cy - qy) - w
    lemma_sub_sub_swap::<F>(cx, v, qx);
    lemma_sub_sub_swap::<F>(cy, w, qy);

    // Step 2: neg(b)*(cx-v-qx) ≡ neg(b)*(u1-v),  a*(cy-w-qy) ≡ a*(u2-w)
    F::axiom_mul_congruence_left(cx.sub(v).sub(qx), u1.sub(v), b.neg());
    F::axiom_mul_congruence_left(cy.sub(w).sub(qy), u2.sub(w), a);
    lemma_add_congruence::<F>(
        b.neg().mul(cx.sub(v).sub(qx)), b.neg().mul(u1.sub(v)),
        a.mul(cy.sub(w).sub(qy)), a.mul(u2.sub(w)));

    // Step 3: Distribute neg(b)*(u1-v) ≡ neg(b)*u1 - neg(b)*v,  a*(u2-w) ≡ a*u2 - a*w
    lemma_mul_sub_left::<F>(b.neg(), u1, v);
    lemma_mul_sub_left::<F>(a, u2, w);

    let pp = b.neg().mul(u1);
    let qq = b.neg().mul(v);
    let rr = a.mul(u2);
    let ss = a.mul(w);

    lemma_add_congruence::<F>(
        b.neg().mul(u1.sub(v)), pp.sub(qq),
        a.mul(u2.sub(w)), rr.sub(ss));

    // Step 4: Show qq + ss ≡ 0  (the cross-term cancellation)
    // qq = neg(b)*v ≡ neg(b)*(a*t)  and  ss = a*w ≡ a*(b*t)
    F::axiom_mul_congruence_left(v, a.mul(t), b.neg());
    F::axiom_mul_congruence_left(w, b.mul(t), a);

    // neg(b)*(a*t) ≡ neg(b*(a*t))
    lemma_mul_neg_left::<F>(b, a.mul(t));
    // b*(a*t) ≡ a*(b*t)  by assoc + comm
    F::axiom_mul_associative(b, a, t);
    F::axiom_mul_commutative(b, a);
    F::axiom_mul_congruence_left(b.mul(a), a.mul(b), t);
    F::axiom_mul_associative(a, b, t);
    F::axiom_eqv_symmetric(a.mul(b.mul(t)), a.mul(b).mul(t));
    F::axiom_eqv_transitive(b.mul(a.mul(t)), b.mul(a).mul(t), a.mul(b).mul(t));
    F::axiom_eqv_transitive(b.mul(a.mul(t)), a.mul(b).mul(t), a.mul(b.mul(t)));

    // neg(b)*(a*t) ≡ neg(a*(b*t))
    lemma_neg_congruence::<F>(b.mul(a.mul(t)), a.mul(b.mul(t)));
    F::axiom_eqv_transitive(
        b.neg().mul(a.mul(t)), b.mul(a.mul(t)).neg(), a.mul(b.mul(t)).neg());

    // qq ≡ neg(b)*(a*t) ≡ neg(a*(b*t)) = neg(ss_inner)
    // So qq + ss ≡ neg(a*(b*t)) + a*(b*t) ≡ 0
    lemma_add_congruence::<F>(qq, b.neg().mul(a.mul(t)), ss, a.mul(b.mul(t)));
    lemma_add_congruence::<F>(
        b.neg().mul(a.mul(t)), a.mul(b.mul(t)).neg(),
        a.mul(b.mul(t)), a.mul(b.mul(t)));
    F::axiom_eqv_reflexive(a.mul(b.mul(t)));
    lemma_add_inverse_left::<F>(a.mul(b.mul(t)));
    F::axiom_eqv_transitive(qq.add(ss),
        b.neg().mul(a.mul(t)).add(a.mul(b.mul(t))),
        a.mul(b.mul(t)).neg().add(a.mul(b.mul(t))));
    F::axiom_eqv_transitive(qq.add(ss),
        a.mul(b.mul(t)).neg().add(a.mul(b.mul(t))),
        F::zero());

    // Step 5: (P - Q) + (R - S) ≡ P + R  when Q + S ≡ 0
    // Convert subs to add-neg
    F::axiom_sub_is_add_neg(pp, qq);
    F::axiom_sub_is_add_neg(rr, ss);
    lemma_add_congruence::<F>(pp.sub(qq), pp.add(qq.neg()), rr.sub(ss), rr.add(ss.neg()));

    // 4-way exchange: (pp + neg(qq)) + (rr + neg(ss)) ≡ (pp + rr) + (neg(qq) + neg(ss))
    crate::line2::lemma_add_exchange::<F>(pp, qq.neg(), rr, ss.neg());
    F::axiom_eqv_transitive(
        pp.sub(qq).add(rr.sub(ss)),
        pp.add(qq.neg()).add(rr.add(ss.neg())),
        pp.add(rr).add(qq.neg().add(ss.neg())));

    // neg(qq) + neg(ss) ≡ neg(qq + ss) ≡ neg(0) ≡ 0
    lemma_neg_add::<F>(qq, ss);
    lemma_neg_congruence::<F>(qq.add(ss), F::zero());
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_transitive(qq.neg().add(ss.neg()), qq.add(ss).neg(), F::zero().neg());
    F::axiom_eqv_transitive(qq.neg().add(ss.neg()), F::zero().neg(), F::zero());

    // (pp + rr) + 0 ≡ pp + rr
    lemma_add_congruence_right::<F>(pp.add(rr), qq.neg().add(ss.neg()), F::zero());
    F::axiom_add_zero_right(pp.add(rr));
    F::axiom_eqv_transitive(
        pp.add(rr).add(qq.neg().add(ss.neg())), pp.add(rr).add(F::zero()), pp.add(rr));

    // Chain: source ≡ pp.sub(qq).add(rr.sub(ss)) ≡ pp.add(rr)
    F::axiom_eqv_transitive(
        pp.sub(qq).add(rr.sub(ss)),
        pp.add(rr).add(qq.neg().add(ss.neg())),
        pp.add(rr));

    // Step 6: pp + rr = neg(b)*u1 + a*u2 ≡ a*u2 + neg(b)*u1 ≡ a*u2 - b*u1
    F::axiom_add_commutative(pp, rr);
    lemma_mul_neg_left::<F>(b, u1);
    lemma_add_congruence_right::<F>(rr, pp, b.mul(u1).neg());
    F::axiom_sub_is_add_neg(rr, b.mul(u1));
    F::axiom_eqv_symmetric(rr.sub(b.mul(u1)), rr.add(b.mul(u1).neg()));
    F::axiom_eqv_transitive(rr.add(pp), rr.add(b.mul(u1).neg()), rr.sub(b.mul(u1)));
    F::axiom_eqv_transitive(pp.add(rr), rr.add(pp), rr.sub(b.mul(u1)));

    // Step 7: Full chain
    // source ≡ neg(b)*(u1-v) + a*(u2-w)  [Step 2]
    //        ≡ pp.sub(qq) + rr.sub(ss)    [Step 3]
    //        ≡ pp + rr                     [Step 5]
    //        ≡ rr - b*u1                   [Step 6]
    //        = a*(cy-qy) - b*(cx-qx)      [definition]
    F::axiom_eqv_transitive(
        b.neg().mul(u1.sub(v)).add(a.mul(u2.sub(w))),
        pp.sub(qq).add(rr.sub(ss)),
        pp.add(rr));
    F::axiom_eqv_transitive(
        b.neg().mul(u1.sub(v)).add(a.mul(u2.sub(w))),
        pp.add(rr),
        rr.sub(b.mul(u1)));
    F::axiom_eqv_transitive(
        b.neg().mul(cx.sub(v).sub(qx)).add(a.mul(cy.sub(w).sub(qy))),
        b.neg().mul(u1.sub(v)).add(a.mul(u2.sub(w))),
        rr.sub(b.mul(u1)));
}

} // verus!
