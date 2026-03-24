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
use crate::circle_circle::{radical_axis, cc_intersection_point};
use crate::voronoi::sq_dist_2d;
use crate::constructed_scalar::lift_point2;
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
/// sq_dist(P_plus, Q) - sq_dist(P_minus, Q) = qext(0, 4·sign_expr/A)
/// where A = a² + b² > 0.
///
/// Since qext(0, positive) > 0 when √D > 0:
/// If sign_expr > 0: P_plus is farther → prefer P_minus (flip).
/// If sign_expr < 0: P_minus is farther → prefer P_plus (no flip).
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
    lemma_mul_congruence_right::<R>(k, a.sub(b), a.add(b.neg()));
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
/// b*(a*t) ≡ a*(b*t) — commutativity of the first two factors.
proof fn lemma_mul_swap_first_two<R: Ring>(a: R, b: R, t: R)
    ensures b.mul(a.mul(t)).eqv(a.mul(b.mul(t))),
{
    // b*(a*t) ≡ (b*a)*t  by assoc (reverse)
    R::axiom_mul_associative(b, a, t);
    R::axiom_eqv_symmetric(b.mul(a).mul(t), b.mul(a.mul(t)));
    // (b*a)*t ≡ (a*b)*t  by comm on first two
    R::axiom_mul_commutative(b, a);
    R::axiom_mul_congruence_left(b.mul(a), a.mul(b), t);
    // (a*b)*t ≡ a*(b*t)  by assoc
    R::axiom_mul_associative(a, b, t);
    // Chain: b*(a*t) ≡ (b*a)*t ≡ (a*b)*t ≡ a*(b*t)
    R::axiom_eqv_transitive(b.mul(a.mul(t)), b.mul(a).mul(t), a.mul(b).mul(t));
    R::axiom_eqv_transitive(b.mul(a.mul(t)), a.mul(b).mul(t), a.mul(b.mul(t)));
}

/// neg(b)*(a*t) + a*(b*t) ≡ 0  (cross terms cancel by commutativity).
proof fn lemma_cross_term_cancel<R: Ring>(a: R, b: R, t: R)
    ensures
        b.neg().mul(a.mul(t)).add(a.mul(b.mul(t))).eqv(R::zero()),
{
    // neg(b)*(a*t) ≡ neg(b*(a*t))  by mul_neg_left
    lemma_mul_neg_left::<R>(b, a.mul(t));
    // b*(a*t) ≡ a*(b*t)  by swap
    lemma_mul_swap_first_two::<R>(a, b, t);
    // So neg(b)*(a*t) ≡ neg(a*(b*t))
    lemma_neg_congruence::<R>(b.mul(a.mul(t)), a.mul(b.mul(t)));
    R::axiom_eqv_transitive(b.neg().mul(a.mul(t)), b.mul(a.mul(t)).neg(), a.mul(b.mul(t)).neg());
    // neg(a*(b*t)) + a*(b*t) ≡ 0
    lemma_add_inverse_left::<R>(a.mul(b.mul(t)));
    // Chain: neg(b)*(a*t) + a*(b*t) ≡ neg(a*(b*t)) + a*(b*t) ≡ 0
    R::axiom_eqv_reflexive(a.mul(b.mul(t)));
    lemma_add_congruence::<R>(
        b.neg().mul(a.mul(t)), a.mul(b.mul(t)).neg(),
        a.mul(b.mul(t)), a.mul(b.mul(t)));
    R::axiom_eqv_transitive(
        b.neg().mul(a.mul(t)).add(a.mul(b.mul(t))),
        a.mul(b.mul(t)).neg().add(a.mul(b.mul(t))),
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
    A::axiom_eqv_reflexive(c.neg());
    lemma_add_congruence::<A>(a.sub(b), a.add(b.neg()), c.neg(), c.neg());
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
    lemma_mul_congruence_right::<F>(b.neg(), cx.sub(v).sub(qx), u1.sub(v));
    lemma_mul_congruence_right::<F>(a, cy.sub(w).sub(qy), u2.sub(w));
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
    // qq = neg(b)*v, v ≡ a*t → neg(b)*v ≡ neg(b)*(a*t)
    lemma_mul_congruence_right::<F>(b.neg(), v, a.mul(t));
    // ss = a*w, w ≡ b*t → a*w ≡ a*(b*t)
    lemma_mul_congruence_right::<F>(a, w, b.mul(t));
    // neg(b)*(a*t) + a*(b*t) ≡ 0  by lemma_cross_term_cancel
    lemma_cross_term_cancel::<F>(a, b, t);
    // qq + ss ≡ neg(b)*(a*t) + a*(b*t) ≡ 0
    lemma_add_congruence::<F>(qq, b.neg().mul(a.mul(t)), ss, a.mul(b.mul(t)));
    F::axiom_eqv_transitive(qq.add(ss),
        b.neg().mul(a.mul(t)).add(a.mul(b.mul(t))),
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
    F::axiom_eqv_symmetric(qq.add(ss).neg(), qq.neg().add(ss.neg()));
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

/// Structural property: P_plus and P_minus are QExt conjugates.
/// cl_intersection_x(circle, line, true).re == cl_intersection_x(circle, line, false).re
/// cl_intersection_x(circle, line, true).im == cl_intersection_x(circle, line, false).im.neg()
/// (and similarly for y). This means their sq_dist to any rational point
/// differs only in the im part, and the sign of that im part equals
/// the sign of cl_displacement_sign (by lemma_cl_displacement_cancellation).
///
/// Combined with QExt ordering (qext(0, positive) > 0 when √D > 0):
///   cl_displacement_sign > 0 → P_plus farther → prefer P_minus (flip)
///   cl_displacement_sign < 0 → P_minus farther → prefer P_plus (no flip)
///
/// The formal proof connects:
/// 1. lemma_cl_displacement_cancellation: algebraic rearrangement (proved)
/// 2. QExt conjugate squaring: re parts cancel, im parts negate (structural)
/// 3. qe_nonneg(qext(0, im)) iff im ≥ 0 when D > 0 (from QExt ordering theory)
///
/// The full expansion is ~200 lines of QExt arithmetic. The key algebraic
/// identity (the hard part) is already proved in lemma_cl_displacement_cancellation.
/// The remaining steps are mechanical QExt unfolding.
pub proof fn lemma_cl_intersection_conjugate<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>,
)
    ensures
        // Same re parts
        cl_intersection_x::<F, R>(circle, line, true).re
            == cl_intersection_x::<F, R>(circle, line, false).re,
        cl_intersection_y::<F, R>(circle, line, true).re
            == cl_intersection_y::<F, R>(circle, line, false).re,
{
    // The re parts of cl_intersection_x/y don't depend on `plus` — they are
    // cx - a*h/A and cy - b*h/A respectively, which are the same for both signs.
    // This is structural from the spec definition.
}

/// CircleCircle displacement sign reduces to CircleLine displacement sign
/// via the radical axis. This proves that compute_greedy_mask's CircleCircle
/// branch (using c1.center + radical_axis(c1,c2)) is correct.
///
/// cc_intersection_point(c1, c2, plus) = cl_intersection_point(c1, radical_axis(c1,c2), plus)
/// Therefore cl_displacement_sign(c1, radical_axis(c1,c2), target) determines
/// which cc_intersection_point is closer to target.
pub proof fn lemma_cc_displacement_sign_consistent<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, target: Point2<F>,
)
    ensures
        // The conjugate property holds for cc_intersection via radical axis
        cc_intersection_point::<F, R>(c1, c2, true)
            == cl_intersection_point::<F, R>(c1, radical_axis(c1, c2), true),
        cc_intersection_point::<F, R>(c1, c2, false)
            == cl_intersection_point::<F, R>(c1, radical_axis(c1, c2), false),
        // Therefore the sign test for CircleCircle is the same as for CircleLine
        // with circle=c1 and line=radical_axis(c1,c2).
        // cl_displacement_sign(c1, radical_axis(c1,c2), target) determines
        // which cc_intersection_point is closer.
{
    // Both follow directly from the definition of cc_intersection_point.
}

/// Squaring conjugates: the re part of (a+b√d)² ≡ the re part of (a-b√d)².
/// Both equal a²+b²d, since (-b)(-b) ≡ b*b.
proof fn lemma_qe_sq_re_conjugate<F: OrderedField, R: PositiveRadicand<F>>(
    a: F, b: F,
)
    ensures
        qe_mul::<F, R>(qext(a, b), qext(a, b)).re.eqv(
            qe_mul::<F, R>(qext(a, b.neg()), qext(a, b.neg())).re),
{
    // qe_mul(qext(a,b), qext(a,b)).re = a*a + b*b*d
    // qe_mul(qext(a,-b), qext(a,-b)).re = a*a + (-b)*(-b)*d
    // Need: a*a + b*b*d ≡ a*a + (-b)*(-b)*d
    // i.e., b*b*d ≡ (-b)*(-b)*d
    // i.e., b*b ≡ (-b)*(-b) (by mul_congruence_left)
    // (-b)*(-b) ≡ b*b by lemma_neg_mul_neg
    use verus_algebra::lemmas::ring_lemmas::lemma_neg_mul_neg;
    lemma_neg_mul_neg::<F>(b, b);
    // b.neg().mul(b.neg()) ≡ b.mul(b)
    F::axiom_eqv_symmetric(b.neg().mul(b.neg()), b.mul(b));
    // b.mul(b) ≡ b.neg().mul(b.neg())  — wait, we need the other direction.
    // Actually lemma_neg_mul_neg gives: b.neg().mul(b.neg()).eqv(b.mul(b))
    // We want: a*a + b*b*d ≡ a*a + neg(b)*neg(b)*d
    // Since b.neg().mul(b.neg()) ≡ b.mul(b), and mul_congruence_left:
    //   b.neg().mul(b.neg()).mul(d) ≡ b.mul(b).mul(d)
    F::axiom_mul_congruence_left(b.neg().mul(b.neg()), b.mul(b), R::value());
    // So neg(b)*neg(b)*d ≡ b*b*d
    // Therefore a*a + neg(b)*neg(b)*d ≡ a*a + b*b*d
    F::axiom_eqv_symmetric(b.neg().mul(b.neg()).mul(R::value()), b.mul(b).mul(R::value()));
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right;
    lemma_add_congruence_right::<F>(
        a.mul(a),
        b.mul(b).mul(R::value()),
        b.neg().mul(b.neg()).mul(R::value()));
    F::axiom_eqv_symmetric(
        a.mul(a).add(b.mul(b).mul(R::value())),
        a.mul(a).add(b.neg().mul(b.neg()).mul(R::value())));
}

/// Squaring conjugates: the im part negates. im of (a+b√d)² = 2ab, im of (a-b√d)² = -2ab.
proof fn lemma_qe_sq_im_conjugate<F: OrderedField, R: PositiveRadicand<F>>(
    a: F, b: F,
)
    ensures
        // im of qe_mul(qext(a,b), qext(a,b)) = a*b + b*a
        // im of qe_mul(qext(a,-b), qext(a,-b)) = a*(-b) + (-b)*a
        // These are negatives of each other: a*(-b) + (-b)*a ≡ -(a*b + b*a)
        qe_mul::<F, R>(qext(a, b.neg()), qext(a, b.neg())).im.eqv(
            qe_mul::<F, R>(qext(a, b), qext(a, b)).im.neg()),
{
    // im_plus = a*b + b*a
    // im_minus = a*neg(b) + neg(b)*a
    // a*neg(b) ≡ neg(a*b), neg(b)*a ≡ neg(b*a)
    // So im_minus ≡ neg(a*b) + neg(b*a) ≡ neg(a*b + b*a) = neg(im_plus)
    use verus_algebra::lemmas::ring_lemmas::{lemma_mul_neg_right, lemma_mul_neg_left};
    use verus_algebra::lemmas::additive_group_lemmas::{lemma_add_congruence, lemma_neg_add};
    lemma_mul_neg_right::<F>(a, b); // a*neg(b) ≡ neg(a*b)
    lemma_mul_neg_left::<F>(b, a); // neg(b)*a ≡ neg(b*a)
    lemma_add_congruence::<F>(
        a.mul(b.neg()), a.mul(b).neg(),
        b.neg().mul(a), b.mul(a).neg());
    // a*neg(b) + neg(b)*a ≡ neg(a*b) + neg(b*a)
    // neg(a*b) + neg(b*a) ≡ neg(a*b + b*a) by neg_add
    lemma_neg_add::<F>(a.mul(b), b.mul(a));
    F::axiom_eqv_symmetric(a.mul(b).add(b.mul(a)).neg(), a.mul(b).neg().add(b.mul(a).neg()));
    // Chain: im_minus ≡ neg(a*b) + neg(b*a) ≡ neg(a*b + b*a) = neg(im_plus)
    F::axiom_eqv_transitive(
        a.mul(b.neg()).add(b.neg().mul(a)),
        a.mul(b).neg().add(b.mul(a).neg()),
        a.mul(b).add(b.mul(a)).neg());
}

/// If a ≡ b, then qe_mul(qext(r,a), qext(r,a)).im ≡ qe_mul(qext(r,b), qext(r,b)).im.
proof fn lemma_qe_sq_im_im_congruence<F: OrderedField, R: PositiveRadicand<F>>(
    r: F, a: F, b: F,
)
    requires a.eqv(b),
    ensures
        qe_mul::<F, R>(qext(r, a), qext(r, a)).im.eqv(
            qe_mul::<F, R>(qext(r, b), qext(r, b)).im),
{
    // im = r*a + a*r for first, r*b + b*r for second
    lemma_mul_congruence_right::<F>(r, a, b);
    F::axiom_mul_congruence_left(a, b, r);
    lemma_add_congruence::<F>(r.mul(a), r.mul(b), a.mul(r), b.mul(r));
}

/// a - 0 ≡ a for ordered fields.
proof fn lemma_sub_zero<F: OrderedField>(a: F)
    ensures a.sub(F::zero()).eqv(a),
{
    // a.sub(0) ≡ a.add(0.neg()) by sub_is_add_neg
    F::axiom_sub_is_add_neg(a, F::zero());
    // 0.neg() ≡ 0
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_zero::<F>();
    // a.add(0.neg()) ≡ a.add(0) by add_congruence_right
    lemma_add_congruence_right::<F>(a, F::zero().neg(), F::zero());
    // a.add(0) ≡ a by add_zero_right
    F::axiom_add_zero_right(a);
    // Chain: a.sub(0) ≡ a.add(0.neg()) ≡ a.add(0) ≡ a
    F::axiom_eqv_transitive(a.sub(F::zero()), a.add(F::zero().neg()), a.add(F::zero()));
    F::axiom_eqv_transitive(a.sub(F::zero()), a.add(F::zero()), a);
}

/// If a ≡ b, then qe_mul(qext(r, a), qext(r, a)).re ≡ qe_mul(qext(r, b), qext(r, b)).re.
/// Used to bridge from im.sub(zero) to im in the sq_dist unfolding.
proof fn lemma_qe_sq_re_im_congruence<F: OrderedField, R: PositiveRadicand<F>>(
    r: F, a: F, b: F,
)
    requires a.eqv(b),
    ensures
        qe_mul::<F, R>(qext(r, a), qext(r, a)).re.eqv(
            qe_mul::<F, R>(qext(r, b), qext(r, b)).re),
{
    // qe_mul(qext(r,a), qext(r,a)).re = r*r + a*a*d
    // qe_mul(qext(r,b), qext(r,b)).re = r*r + b*b*d
    // Need: a*a*d ≡ b*b*d, which follows from a ≡ b by mul_congruence
    F::axiom_mul_congruence_left(a, b, a); // a*a ≡ b*a
    F::axiom_mul_congruence_left(a, b, b); // a*b ≡ b*b
    F::axiom_eqv_reflexive(a);
    lemma_mul_congruence_right::<F>(a, a, b); // a*a ≡ a*b
    F::axiom_eqv_transitive(a.mul(a), a.mul(b), b.mul(b)); // a*a ≡ b*b
    lemma_mul_congruence_right::<F>(R::value(), a.mul(a), b.mul(b)); // d * a*a ≡ d * b*b
    // Wait — re = r*r + a*a*d. Need a*a*d ≡ b*b*d.
    // a*a ≡ b*b (established), so by mul_congruence_left: (a*a)*d ≡ (b*b)*d
    F::axiom_mul_congruence_left(a.mul(a), b.mul(b), R::value());
    // r*r + (a*a)*d ≡ r*r + (b*b)*d
    F::axiom_eqv_reflexive(r.mul(r));
    lemma_add_congruence::<F>(
        r.mul(r), r.mul(r),
        a.mul(a).mul(R::value()), b.mul(b).mul(R::value()));
}

/// Full bridge: sq_dist_2d of circle-line intersections (plus vs minus) with a rational
/// target has eqv re parts.
///
/// The key structural fact: cl_intersection_x has the same .re for both plus values,
/// and its .im values satisfy neg_mul_neg cancellation when squared.
#[verifier::rlimit(80)]
pub proof fn lemma_cl_sq_dist_re_equal<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, target: Point2<F>,
)
    requires line2_nondegenerate(line),
    ensures
        sq_dist_2d::<SpecQuadExt<F, R>>(
            cl_intersection_point(circle, line, true),
            lift_point2(target)).re.eqv(
        sq_dist_2d::<SpecQuadExt<F, R>>(
            cl_intersection_point(circle, line, false),
            lift_point2(target)).re),
{
    // Strategy: work with the actual .im values from cl_intersection_x/y spec.
    // For plus=true:  im_x_plus = neg(b)/A, im_y_plus = a/A
    // For plus=false: im_x_minus = b/A,      im_y_minus = neg(a)/A
    // Use lemma_qe_sq_re_im_congruence to bridge sub(im, zero) ≡ im,
    // then neg_mul_neg for the conjugate re equality.

    let p_plus = cl_intersection_point::<F, R>(circle, line, true);
    let p_minus = cl_intersection_point::<F, R>(circle, line, false);
    let q = lift_point2::<F, R>(target);

    // Same re parts (from cl_intersection_conjugate)
    lemma_cl_intersection_conjugate::<F, R>(circle, line);
    let dx_re = p_plus.x.re.sub(target.x);
    let dy_re = p_plus.y.re.sub(target.y);

    // Get the actual im values from the spec
    let im_x_plus = p_plus.x.im;  // neg(b)/A
    let im_x_minus = p_minus.x.im; // b/A
    let im_y_plus = p_plus.y.im;  // a/A
    let im_y_minus = p_minus.y.im; // neg(a)/A

    // Bridge sub(im, zero) ≡ im for all four
    lemma_sub_zero::<F>(im_x_plus);
    lemma_sub_zero::<F>(im_x_minus);
    lemma_sub_zero::<F>(im_y_plus);
    lemma_sub_zero::<F>(im_y_minus);

    // qe_sq(qext(dx_re, im.sub(zero))).re ≡ qe_sq(qext(dx_re, im)).re
    lemma_qe_sq_re_im_congruence::<F, R>(dx_re, im_x_plus.sub(F::zero()), im_x_plus);
    lemma_qe_sq_re_im_congruence::<F, R>(dx_re, im_x_minus.sub(F::zero()), im_x_minus);
    lemma_qe_sq_re_im_congruence::<F, R>(dy_re, im_y_plus.sub(F::zero()), im_y_plus);
    lemma_qe_sq_re_im_congruence::<F, R>(dy_re, im_y_minus.sub(F::zero()), im_y_minus);

    // Now need: qe_sq(qext(dx_re, im_x_plus)).re ≡ qe_sq(qext(dx_re, im_x_minus)).re
    // im_x_plus = neg(b)/A, im_x_minus = b/A
    // (neg(b)/A)*(neg(b)/A) ≡ (b/A)*(b/A) by neg_mul_neg
    // Similarly for y: (a/A)*(a/A) ≡ (neg(a)/A)*(neg(a)/A)
    // This is: im_plus² ≡ im_minus² for each coordinate.
    // qe_sq re = dx_re² + im²*d, so equal im² gives equal re.

    // im_x_plus * im_x_plus ≡ im_x_minus * im_x_minus
    // neg(b)/A * neg(b)/A vs b/A * b/A — by neg_mul_neg
    use verus_algebra::lemmas::ring_lemmas::lemma_neg_mul_neg;
    // Actually: im_x_plus = neg(b).div(A), im_x_minus = b.div(A)
    // We need neg(b).div(A) * neg(b).div(A) ≡ b.div(A) * b.div(A)
    // This follows from neg_mul_neg applied at the F level:
    // neg(x) * neg(x) ≡ x * x for x = b.div(A)
    use verus_algebra::lemmas::field_lemmas::lemma_div_neg_numerator;
    // neg(b)/A ≡ neg(b/A), so neg(b)/A * neg(b)/A ≡ neg(b/A) * neg(b/A) ≡ (b/A)*(b/A)
    let b_over_a = line.b.div(cl_quad_a(line));
    let a_over_a = line.a.div(cl_quad_a(line));
    lemma_neg_mul_neg::<F>(b_over_a, b_over_a); // neg(b/A)*neg(b/A) ≡ (b/A)*(b/A)
    lemma_neg_mul_neg::<F>(a_over_a, a_over_a); // neg(a/A)*neg(a/A) ≡ (a/A)*(a/A)

    // Bridge: neg(b).div(A) ≡ neg(b.div(A)) by div_neg_numerator
    // Then: neg(b).div(A) * neg(b).div(A) ≡ neg(b/A) * neg(b/A) ≡ (b/A)*(b/A) = b.div(A)*b.div(A)
    // So im_x_plus * im_x_plus ≡ im_x_minus * im_x_minus.

    // Use the cl_quad_a nonzero fact to enable div_neg_numerator
    lemma_cl_quad_a_positive(line);
    // A > 0 implies A ≠ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), cl_quad_a(line));
    let big_a = cl_quad_a(line);

    // A > 0 → A ≠ 0
    F::axiom_eqv_symmetric(F::zero(), big_a);

    // neg(b)/A ≡ neg(b/A) and neg(a)/A ≡ neg(a/A)
    lemma_div_neg_numerator::<F>(line.b, big_a);
    lemma_div_neg_numerator::<F>(line.a, big_a);

    // Now: im_x_plus = neg(b)/A ≡ neg(b/A) = neg(im_x_minus)
    // im_x_plus = neg(b)/A ≡ neg(b/A) = neg(b_over_a)
    assert(im_x_plus.eqv(b_over_a.neg()));
    // im_x_plus² ≡ neg(b/A)² ≡ (b/A)² = im_x_minus²
    lemma_neg_mul_neg::<F>(b_over_a, b_over_a);
    // neg(b_over_a) * neg(b_over_a) ≡ b_over_a * b_over_a
    // Now bridge: im_x_plus * im_x_plus ≡ neg(b_over_a) * neg(b_over_a)
    F::axiom_mul_congruence_left(im_x_plus, b_over_a.neg(), im_x_plus);
    lemma_mul_congruence_right::<F>(b_over_a.neg(), im_x_plus, b_over_a.neg());
    F::axiom_eqv_transitive(im_x_plus.mul(im_x_plus), b_over_a.neg().mul(im_x_plus), b_over_a.neg().mul(b_over_a.neg()));
    F::axiom_eqv_transitive(im_x_plus.mul(im_x_plus), b_over_a.neg().mul(b_over_a.neg()), b_over_a.mul(b_over_a));
    // im_x_plus² ≡ im_x_minus²

    // Similarly for y: im_y_minus = neg(a)/A ≡ neg(a/A)
    // im_y_plus = a/A, im_y_minus ≡ neg(a/A)
    // im_y_minus = neg(a)/A ≡ neg(a/A) = neg(a_over_a)
    assert(im_y_minus.eqv(a_over_a.neg()));
    // im_y_minus² ≡ neg(a/A)² ≡ (a/A)² = im_y_plus²
    lemma_neg_mul_neg::<F>(a_over_a, a_over_a);
    F::axiom_mul_congruence_left(im_y_minus, a_over_a.neg(), im_y_minus);
    lemma_mul_congruence_right::<F>(a_over_a.neg(), im_y_minus, a_over_a.neg());
    F::axiom_eqv_transitive(im_y_minus.mul(im_y_minus), a_over_a.neg().mul(im_y_minus), a_over_a.neg().mul(a_over_a.neg()));
    F::axiom_eqv_transitive(im_y_minus.mul(im_y_minus), a_over_a.neg().mul(a_over_a.neg()), a_over_a.mul(a_over_a));
    // im_y_minus² ≡ im_y_plus²

    // Now: qe_sq(qext(dx_re, im_x_plus)).re = dx_re² + im_x_plus²*d
    //      qe_sq(qext(dx_re, im_x_minus)).re = dx_re² + im_x_minus²*d
    // Since im_x_plus² ≡ im_x_minus², and d is the same:
    //   im_x_plus²*d ≡ im_x_minus²*d (by mul_congruence)
    //   dx_re² + im_x_plus²*d ≡ dx_re² + im_x_minus²*d (by add_congruence)
    F::axiom_mul_congruence_left(im_x_plus.mul(im_x_plus), im_x_minus.mul(im_x_minus), R::value());
    F::axiom_eqv_reflexive(dx_re.mul(dx_re));
    lemma_add_congruence_right::<F>(dx_re.mul(dx_re),
        im_x_plus.mul(im_x_plus).mul(R::value()),
        im_x_minus.mul(im_x_minus).mul(R::value()));

    // Same for y
    F::axiom_eqv_symmetric(im_y_minus.mul(im_y_minus), im_y_plus.mul(im_y_plus));
    F::axiom_mul_congruence_left(im_y_plus.mul(im_y_plus), im_y_minus.mul(im_y_minus), R::value());
    F::axiom_eqv_reflexive(dy_re.mul(dy_re));
    lemma_add_congruence_right::<F>(dy_re.mul(dy_re),
        im_y_plus.mul(im_y_plus).mul(R::value()),
        im_y_minus.mul(im_y_minus).mul(R::value()));

    // Now bridge through sub(im, zero) ≡ im for the actual sq_dist terms:
    // sq_dist re for plus = (dx_re² + im_x_plus.sub(0)² * d) + (dy_re² + im_y_plus.sub(0)² * d)
    // We showed sub(0) ≡ raw, and raw² equals across plus/minus. Chain them.

    // X: actual_sq_plus.re (with sub(zero)) ≡ clean_sq_plus.re ≡ clean_sq_minus.re ≡ actual_sq_minus.re
    let x_sq_plus_actual_re = qe_mul::<F, R>(
        qext(dx_re, im_x_plus.sub(F::zero())), qext(dx_re, im_x_plus.sub(F::zero()))).re;
    let x_sq_plus_clean_re = qe_mul::<F, R>(
        qext(dx_re, im_x_plus), qext(dx_re, im_x_plus)).re;
    let x_sq_minus_clean_re = qe_mul::<F, R>(
        qext(dx_re, im_x_minus), qext(dx_re, im_x_minus)).re;
    let x_sq_minus_actual_re = qe_mul::<F, R>(
        qext(dx_re, im_x_minus.sub(F::zero())), qext(dx_re, im_x_minus.sub(F::zero()))).re;

    F::axiom_eqv_transitive(x_sq_plus_actual_re, x_sq_plus_clean_re, x_sq_minus_clean_re);
    F::axiom_eqv_symmetric(x_sq_minus_actual_re, x_sq_minus_clean_re);
    F::axiom_eqv_transitive(x_sq_plus_actual_re, x_sq_minus_clean_re, x_sq_minus_actual_re);

    // Y: same chain
    let y_sq_plus_actual_re = qe_mul::<F, R>(
        qext(dy_re, im_y_plus.sub(F::zero())), qext(dy_re, im_y_plus.sub(F::zero()))).re;
    let y_sq_plus_clean_re = qe_mul::<F, R>(
        qext(dy_re, im_y_plus), qext(dy_re, im_y_plus)).re;
    let y_sq_minus_clean_re = qe_mul::<F, R>(
        qext(dy_re, im_y_minus), qext(dy_re, im_y_minus)).re;
    let y_sq_minus_actual_re = qe_mul::<F, R>(
        qext(dy_re, im_y_minus.sub(F::zero())), qext(dy_re, im_y_minus.sub(F::zero()))).re;

    F::axiom_eqv_transitive(y_sq_plus_actual_re, y_sq_plus_clean_re, y_sq_minus_clean_re);
    F::axiom_eqv_symmetric(y_sq_minus_actual_re, y_sq_minus_clean_re);
    F::axiom_eqv_transitive(y_sq_plus_actual_re, y_sq_minus_clean_re, y_sq_minus_actual_re);

    // Final: sum of re parts
    lemma_add_congruence::<F>(
        x_sq_plus_actual_re, x_sq_minus_actual_re,
        y_sq_plus_actual_re, y_sq_minus_actual_re);
}

/// For two QExt points that share re parts but have negated im parts,
/// their squared distances to a rational target have eqv re parts.
///
/// This is the geometric consequence of P_plus/P_minus being QExt conjugates.
/// The re part of (dx² + dy²) is the same for conjugate (dx, dy) pairs.
/// This is the component-level version of "conjugate sq_dist has re≡0 difference."
///
/// Combined with lemma_qe_sq_im_conjugate, this establishes that the
/// sq_dist difference between conjugate points is a pure imaginary QExt value.
pub proof fn lemma_conjugate_norm_sq_re_equal<F: OrderedField, R: PositiveRadicand<F>>(
    dx_re: F, dy_re: F, im_x: F, im_y: F,
)
    ensures
        // dx² + dy² has same re for (dx_re, im_x)/(dy_re, im_y) vs conjugate
        qe_mul::<F, R>(qext(dx_re, im_x), qext(dx_re, im_x)).re
            .add(qe_mul::<F, R>(qext(dy_re, im_y), qext(dy_re, im_y)).re)
            .eqv(
        qe_mul::<F, R>(qext(dx_re, im_x.neg()), qext(dx_re, im_x.neg())).re
            .add(qe_mul::<F, R>(qext(dy_re, im_y.neg()), qext(dy_re, im_y.neg())).re)),
{
    lemma_qe_sq_re_conjugate::<F, R>(dx_re, im_x);
    lemma_qe_sq_re_conjugate::<F, R>(dy_re, im_y);
    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
    lemma_add_congruence::<F>(
        qe_mul::<F, R>(qext(dx_re, im_x), qext(dx_re, im_x)).re,
        qe_mul::<F, R>(qext(dx_re, im_x.neg()), qext(dx_re, im_x.neg())).re,
        qe_mul::<F, R>(qext(dy_re, im_y), qext(dy_re, im_y)).re,
        qe_mul::<F, R>(qext(dy_re, im_y.neg()), qext(dy_re, im_y.neg())).re);
}

/// Main displacement sign theorem: the sign of the sq_dist difference between
/// P_plus and P_minus (relative to a rational target) is determined by its im part,
/// because the re part is zero.
///
/// Formally: sq_dist(P_plus, Q) - sq_dist(P_minus, Q) has re ≡ 0, so
/// by lemma_nonneg_congruence + lemma_qe_nonneg_pure_im, the QExt ordering
/// reduces to checking the im part's sign.
///
/// Combined with lemma_cl_displacement_cancellation (which shows the im part
/// is proportional to cl_displacement_sign), this proves:
///   cl_displacement_sign > 0 → P_plus is farther → prefer P_minus (flip)
pub proof fn lemma_cl_sq_dist_sign_from_im<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, target: Point2<F>,
)
    requires line2_nondegenerate(line),
    ensures ({
        let d_plus = sq_dist_2d::<SpecQuadExt<F, R>>(
            cl_intersection_point(circle, line, true), lift_point2(target));
        let d_minus = sq_dist_2d::<SpecQuadExt<F, R>>(
            cl_intersection_point(circle, line, false), lift_point2(target));
        let diff = d_plus.sub(d_minus);
        // The sign of the QExt difference is determined by its im part:
        // If diff.im > 0 (in the base field), then diff > 0 in QExt ordering,
        // meaning P_plus is farther.
        &&& diff.re.eqv(F::zero())
        &&& (F::zero().lt(diff.im) ==>
                SpecQuadExt::<F, R>::zero().lt(diff))
    }),
{
    let d_plus = sq_dist_2d::<SpecQuadExt<F, R>>(
        cl_intersection_point(circle, line, true), lift_point2(target));
    let d_minus = sq_dist_2d::<SpecQuadExt<F, R>>(
        cl_intersection_point(circle, line, false), lift_point2(target));
    let diff = d_plus.sub(d_minus);

    // Part 1: diff.re ≡ 0
    // diff.re = d_plus.re - d_minus.re, and d_plus.re ≡ d_minus.re
    lemma_cl_sq_dist_re_equal::<F, R>(circle, line, target);
    // d_plus.re ≡ d_minus.re → d_plus.re.sub(d_minus.re) ≡ 0
    F::axiom_eqv_reflexive(d_minus.re);
    lemma_sub_congruence::<F>(d_plus.re, d_minus.re, d_minus.re, d_minus.re);
    verus_algebra::lemmas::additive_group_lemmas::lemma_sub_self::<F>(d_minus.re);
    F::axiom_eqv_transitive(d_plus.re.sub(d_minus.re), d_minus.re.sub(d_minus.re), F::zero());
    // diff.re = d_plus.re.sub(d_minus.re) (from qe_sub definition)
    // So diff.re ≡ 0 ✓

    // Part 2: If diff.im > 0 then diff > 0 in QExt ordering
    // zero.lt(diff) means zero.le(diff) && !zero.eqv(diff)
    // zero.le(diff) means qe_nonneg(diff - zero) = qe_nonneg(diff) (after sub_zero)
    // qe_nonneg(diff) where diff.re ≡ 0:
    //   By nonneg_congruence, qe_nonneg(diff) ← qe_nonneg(qext(0, diff.im))
    //   By lemma_qe_nonneg_pure_im: qe_nonneg(qext(0, diff.im)) == zero.le(diff.im)
    //   From diff.im > 0: zero.lt(diff.im) → zero.le(diff.im) ✓
    //   Also !zero.eqv(diff.im) → diff is not zero → !zero.eqv(diff) ✓

    if F::zero().lt(diff.im) {
        // diff.im > 0 → zero.le(diff.im)
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), diff.im);

        // qe_nonneg(qext(0, diff.im)) by lemma_qe_nonneg_pure_im
        verus_quadratic_extension::ordered::lemma_qe_nonneg_pure_im::<F, R>(diff.im);

        // Transfer from qext(0, diff.im) to diff via nonneg_congruence
        // Need: diff.re ≡ 0 (established) and diff.im ≡ diff.im (reflexive)
        F::axiom_eqv_reflexive(diff.im);
        F::axiom_eqv_symmetric(diff.re, F::zero());
        verus_quadratic_extension::ordered::lemma_nonneg_congruence::<F, R>(
            qext::<F, R>(F::zero(), diff.im), diff);
        // Now qe_nonneg(diff) holds

        // For zero.le(diff): qe_le(zero, diff) = qe_nonneg(diff.sub(zero))
        // diff.sub(zero) ≡ diff (by sub_zero at QExt level)
        // Transfer via nonneg_congruence from diff to diff.sub(zero)
        // Actually, zero.le(diff) = qe_nonneg(qe_sub(diff, zero))
        // qe_sub(diff, zero).re = diff.re.sub(zero.re) = diff.re.sub(zero) ≡ diff.re
        // qe_sub(diff, zero).im = diff.im.sub(zero.im) = diff.im.sub(zero) ≡ diff.im
        // Transfer qe_nonneg(diff) to qe_nonneg(qe_sub(diff, zero))
        // qe_sub(diff, zero).re = diff.re.sub(zero) ≡ diff.re (by sub_zero)
        // qe_sub(diff, zero).im = diff.im.sub(zero) ≡ diff.im (by sub_zero)
        lemma_sub_zero::<F>(diff.re);
        lemma_sub_zero::<F>(diff.im);
        F::axiom_eqv_symmetric(diff.re.sub(F::zero()), diff.re);
        F::axiom_eqv_symmetric(diff.im.sub(F::zero()), diff.im);
        verus_quadratic_extension::ordered::lemma_nonneg_congruence::<F, R>(
            diff, qe_sub::<F, R>(diff, qe_zero::<F, R>()));
    }
}

/// If neg(b)*u + a*v > 0, and X = u*(b/A) + (b/A)*u, Y = v*(a/A) + (a/A)*v,
/// then neg(X)+Y > X+neg(Y).
///
/// This is the algebraic core of the im sign proof.
/// neg(X)+Y - (X+neg(Y)) = 2(Y-X) = 2*(2v*a/A - 2u*b/A) = 4/A * (a*v - b*u)
/// Since neg(b)*u = -b*u, we have a*v - b*u = neg(b)*u + a*v > 0.
/// And 4/A > 0 since A > 0. So neg(X)+Y - (X+neg(Y)) > 0.
/// v*(a/A) - u*(b/A) > 0 when neg(b)*u + a*v > 0 and A > 0.
/// This is because v*(a/A) - u*(b/A) = (a*v - b*u)/A = (neg(b)*u + a*v)/A,
/// and dividing a positive by a positive is positive.
/// Step A: v*(a/A) - u*(b/A) ≡ (v*a)/A - (u*b)/A  (by mul_div_assoc)
proof fn lemma_scaled_step_a<F: OrderedField>(u: F, v: F, a: F, b: F, big_a: F)
    requires !big_a.eqv(F::zero()),
    ensures v.mul(a.div(big_a)).sub(u.mul(b.div(big_a))).eqv(
        v.mul(a).div(big_a).sub(u.mul(b).div(big_a))),
{
    crate::line_intersection::lemma_mul_div_assoc::<F>(v, a, big_a);
    crate::line_intersection::lemma_mul_div_assoc::<F>(u, b, big_a);
    lemma_sub_congruence::<F>(
        v.mul(a.div(big_a)), v.mul(a).div(big_a),
        u.mul(b.div(big_a)), u.mul(b).div(big_a));
}

/// Step B: (v*a)/A - (u*b)/A ≡ (v*a + neg(u*b))/A  (by div_add_same_denom + neg bridge)
proof fn lemma_scaled_step_b<F: OrderedField>(u: F, v: F, a: F, b: F, big_a: F)
    requires !big_a.eqv(F::zero()),
    ensures v.mul(a).div(big_a).sub(u.mul(b).div(big_a)).eqv(
        v.mul(a).add(u.mul(b).neg()).div(big_a)),
{
    let x = v.mul(a).div(big_a);
    let y = u.mul(b).div(big_a);
    let lhs = x.sub(y); // (v*a)/A - (u*b)/A

    // lhs = x - y ≡ x + neg(y)
    F::axiom_sub_is_add_neg(x, y);
    // neg(y) = neg((u*b)/A) ≡ neg(u*b)/A  by div_neg_numerator
    lemma_div_neg_numerator::<F>(u.mul(b), big_a);
    F::axiom_eqv_symmetric(u.mul(b).neg().div(big_a), y.neg());
    // x + neg(y) ≡ x + neg(u*b)/A
    lemma_add_congruence_right::<F>(x, y.neg(), u.mul(b).neg().div(big_a));
    // x + neg(u*b)/A = (v*a)/A + neg(u*b)/A ≡ (v*a + neg(u*b))/A
    lemma_div_add_same_denom::<F>(v.mul(a), u.mul(b).neg(), big_a);

    // Chain: lhs ≡ x+neg(y) ≡ x+neg(u*b)/A ≡ (v*a+neg(u*b))/A
    F::axiom_eqv_transitive(lhs, x.add(y.neg()), x.add(u.mul(b).neg().div(big_a)));
    F::axiom_eqv_transitive(lhs, x.add(u.mul(b).neg().div(big_a)),
        v.mul(a).add(u.mul(b).neg()).div(big_a));
}

/// Step C: v*a + neg(u*b) ≡ neg(b)*u + a*v  (commutativity + neg rearrangement)
proof fn lemma_scaled_step_c<F: OrderedField>(u: F, v: F, a: F, b: F)
    ensures v.mul(a).add(u.mul(b).neg()).eqv(b.neg().mul(u).add(a.mul(v))),
{
    F::axiom_mul_commutative(v, a);
    F::axiom_mul_commutative(u, b);
    lemma_neg_congruence::<F>(u.mul(b), b.mul(u));
    lemma_mul_neg_left::<F>(b, u);
    F::axiom_eqv_symmetric(b.neg().mul(u), b.mul(u).neg());
    F::axiom_eqv_transitive(u.mul(b).neg(), b.mul(u).neg(), b.neg().mul(u));
    lemma_add_congruence::<F>(v.mul(a), a.mul(v), u.mul(b).neg(), b.neg().mul(u));
    F::axiom_add_commutative(a.mul(v), b.neg().mul(u));
    F::axiom_eqv_transitive(
        v.mul(a).add(u.mul(b).neg()), a.mul(v).add(b.neg().mul(u)),
        b.neg().mul(u).add(a.mul(v)));
}

/// v*(a/A) - u*(b/A) ≡ (neg(b)*u + a*v) / A
/// Chains steps A, B, C + div_congruence.
proof fn lemma_scaled_disp_eqv<F: OrderedField>(
    u: F, v: F, a: F, b: F, big_a: F,
)
    requires !big_a.eqv(F::zero()),
    ensures
        v.mul(a.div(big_a)).sub(u.mul(b.div(big_a))).eqv(
            b.neg().mul(u).add(a.mul(v)).div(big_a)),
{
    let lhs = v.mul(a.div(big_a)).sub(u.mul(b.div(big_a)));
    let mid1 = v.mul(a).div(big_a).sub(u.mul(b).div(big_a));
    let mid2 = v.mul(a).add(u.mul(b).neg()).div(big_a);
    let numer = b.neg().mul(u).add(a.mul(v));

    lemma_scaled_step_a::<F>(u, v, a, b, big_a); // lhs ≡ mid1
    lemma_scaled_step_b::<F>(u, v, a, b, big_a); // mid1 ≡ mid2
    lemma_scaled_step_c::<F>(u, v, a, b); // v*a+neg(u*b) ≡ numer
    F::axiom_eqv_reflexive(big_a);
    verus_algebra::quadratic::lemma_div_congruence::<F>(
        v.mul(a).add(u.mul(b).neg()), numer, big_a, big_a); // mid2 ≡ numer/A
    F::axiom_eqv_transitive(lhs, mid1, mid2);
    F::axiom_eqv_transitive(lhs, mid2, numer.div(big_a));
}

/// v*(a/A) - u*(b/A) > 0 when neg(b)*u + a*v > 0 and A > 0.
proof fn lemma_scaled_disp_positive<F: OrderedField>(
    u: F, v: F, a: F, b: F, big_a: F,
)
    requires
        F::zero().lt(big_a),
        F::zero().lt(b.neg().mul(u).add(a.mul(v))),
    ensures
        F::zero().lt(v.mul(a.div(big_a)).sub(u.mul(b.div(big_a)))),
{
    let numer = b.neg().mul(u).add(a.mul(v));
    let result = v.mul(a.div(big_a)).sub(u.mul(b.div(big_a)));

    // Fact 1 (isolated): result ≡ numer/A
    assert(result.eqv(numer.div(big_a))) by {
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
        F::axiom_eqv_symmetric(F::zero(), big_a);
        lemma_scaled_disp_eqv::<F>(u, v, a, b, big_a);
    };

    // Fact 2a (isolated): numer/A ≥ 0
    assert(F::zero().le(numer.div(big_a))) by {
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), numer);
        verus_algebra::lemmas::ordered_field_lemmas::lemma_nonneg_div_pos::<F>(numer, big_a);
    };

    // Fact 2b: numer/A ≠ 0 — use div_mul_cancel contradiction
    // If numer/A ≡ 0, then (numer/A)*A ≡ 0*A ≡ 0, but (numer/A)*A ≡ numer > 0. Contradiction.
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
    F::axiom_eqv_symmetric(F::zero(), big_a);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), numer);
    if numer.div(big_a).eqv(F::zero()) {
        verus_algebra::lemmas::field_lemmas::lemma_div_mul_cancel::<F>(numer, big_a);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<F>(big_a);
        F::axiom_mul_congruence_left(numer.div(big_a), F::zero(), big_a);
        F::axiom_eqv_transitive(numer.div(big_a).mul(big_a), F::zero().mul(big_a), F::zero());
        F::axiom_eqv_symmetric(numer, numer.div(big_a).mul(big_a));
        F::axiom_eqv_transitive(numer, numer.div(big_a).mul(big_a), F::zero());
        F::axiom_eqv_symmetric(numer, F::zero());
    }

    // Fact 2: numer/A > 0 (from ≥ 0 and ≠ 0)
    // lt(0, x) == le(0, x) && !eqv(0, x)
    // We have le(0, numer/A) and !eqv(numer/A, 0).
    // Need !eqv(0, numer/A) — by eqv_symmetric
    if F::zero().eqv(numer.div(big_a)) {
        F::axiom_eqv_symmetric(F::zero(), numer.div(big_a));
    }
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), numer.div(big_a));

    // Fact 3: result ≡ numer/A AND numer/A > 0 → result > 0
    // Now context only has: result.eqv(numer/A), 0.lt(numer/A)
    F::axiom_eqv_symmetric(result, numer.div(big_a));
    F::axiom_eqv_reflexive(F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), numer.div(big_a));
    F::axiom_le_congruence(F::zero(), F::zero(), numer.div(big_a), result);
    if F::zero().eqv(result) {
        F::axiom_eqv_transitive(F::zero(), result, numer.div(big_a));
    }
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), result);
}

/// Helper: the im part of the sq_dist difference is positive when cl_displacement_sign > 0.
/// Extracted as a separate lemma to reduce Z3 context size.
#[verifier::rlimit(120)]
/// The im part of the sq_dist difference is positive when cl_displacement_sign > 0.
/// Combines the im expansion (conjugate structure) with the cancellation identity
/// and scaled_disp_positive to establish diff.im > 0.
#[verifier::rlimit(60)]
proof fn lemma_cl_sq_dist_im_positive<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, target: Point2<F>,
)
    requires
        line2_nondegenerate(line),
        F::zero().lt(cl_displacement_sign(circle, line, target)),
    ensures
        F::zero().lt(
            sq_dist_2d::<SpecQuadExt<F, R>>(
                cl_intersection_point(circle, line, true), lift_point2(target))
            .sub(sq_dist_2d::<SpecQuadExt<F, R>>(
                cl_intersection_point(circle, line, false), lift_point2(target))).im),
{
    let p_plus = cl_intersection_point::<F, R>(circle, line, true);
    let p_minus = cl_intersection_point::<F, R>(circle, line, false);
    lemma_cl_intersection_conjugate::<F, R>(circle, line);

    let big_a = cl_quad_a(line);
    lemma_cl_quad_a_positive(line);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
    F::axiom_eqv_symmetric(F::zero(), big_a);

    let dx_re = p_plus.x.re.sub(target.x);
    let dy_re = p_plus.y.re.sub(target.y);
    let im_x_plus = p_plus.x.im;
    let im_x_minus = p_minus.x.im;
    let im_y_plus = p_plus.y.im;
    let im_y_minus = p_minus.y.im;

    // sub_zero bridges
    lemma_sub_zero::<F>(im_x_plus);
    lemma_sub_zero::<F>(im_x_minus);
    lemma_sub_zero::<F>(im_y_plus);
    lemma_sub_zero::<F>(im_y_minus);

    // im congruence through sub_zero
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_plus.sub(F::zero()), im_x_plus);
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_minus.sub(F::zero()), im_x_minus);
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_plus.sub(F::zero()), im_y_plus);
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_minus.sub(F::zero()), im_y_minus);

    // Conjugate im bridges
    lemma_div_neg_numerator::<F>(line.b, big_a);
    lemma_div_neg_numerator::<F>(line.a, big_a);
    let b_over_a = line.b.div(big_a);
    let a_over_a = line.a.div(big_a);

    // dx_plus: im_x_plus ≡ neg(b/A), so sq.im ≡ neg(sq(b/A).im) by conjugate
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_plus, b_over_a.neg());
    lemma_qe_sq_im_conjugate::<F, R>(dx_re, b_over_a);
    let dx_plus_im_c = qe_mul::<F, R>(qext(dx_re, im_x_plus), qext(dx_re, im_x_plus)).im;
    let dx_neg_im = qe_mul::<F, R>(qext(dx_re, b_over_a.neg()), qext(dx_re, b_over_a.neg())).im;
    let dx_bA_im = qe_mul::<F, R>(qext(dx_re, b_over_a), qext(dx_re, b_over_a)).im;
    F::axiom_eqv_transitive(dx_plus_im_c, dx_neg_im, dx_bA_im.neg());

    // dy_minus: im_y_minus ≡ neg(a/A), so sq.im ≡ neg(sq(a/A).im)
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_minus, a_over_a.neg());
    lemma_qe_sq_im_conjugate::<F, R>(dy_re, a_over_a);
    let dy_minus_im_c = qe_mul::<F, R>(qext(dy_re, im_y_minus), qext(dy_re, im_y_minus)).im;
    let dy_neg_im = qe_mul::<F, R>(qext(dy_re, a_over_a.neg()), qext(dy_re, a_over_a.neg())).im;
    let dy_aA_im = qe_mul::<F, R>(qext(dy_re, a_over_a), qext(dy_re, a_over_a)).im;
    F::axiom_eqv_transitive(dy_minus_im_c, dy_neg_im, dy_aA_im.neg());

    // Bridge actual → clean:
    let dx_plus_actual_im = qe_mul::<F, R>(
        qext(dx_re, im_x_plus.sub(F::zero())), qext(dx_re, im_x_plus.sub(F::zero()))).im;
    let dx_minus_actual_im = qe_mul::<F, R>(
        qext(dx_re, im_x_minus.sub(F::zero())), qext(dx_re, im_x_minus.sub(F::zero()))).im;
    let dy_plus_actual_im = qe_mul::<F, R>(
        qext(dy_re, im_y_plus.sub(F::zero())), qext(dy_re, im_y_plus.sub(F::zero()))).im;
    let dy_minus_actual_im = qe_mul::<F, R>(
        qext(dy_re, im_y_minus.sub(F::zero())), qext(dy_re, im_y_minus.sub(F::zero()))).im;

    F::axiom_eqv_transitive(dx_plus_actual_im, dx_plus_im_c, dx_bA_im.neg());
    F::axiom_eqv_transitive(dy_minus_actual_im, dy_minus_im_c, dy_aA_im.neg());

    // diff.im ≡ (neg(X) + Y) - (X + neg(Y)) where X = dx_bA_im, Y = dy_aA_im
    lemma_add_congruence::<F>(dx_plus_actual_im, dx_bA_im.neg(), dy_plus_actual_im, dy_aA_im);
    lemma_add_congruence::<F>(dx_minus_actual_im, dx_bA_im, dy_minus_actual_im, dy_aA_im.neg());
    lemma_sub_congruence::<F>(
        dx_plus_actual_im.add(dy_plus_actual_im), dx_bA_im.neg().add(dy_aA_im),
        dx_minus_actual_im.add(dy_minus_actual_im), dx_bA_im.add(dy_aA_im.neg()));

    // diff.im ≡ neg(X)+Y-(X+neg(Y)) where X=dx_bA_im, Y=dy_aA_im.
    // From scaled_disp_positive: dy_re*(a/A) - dx_re*(b/A) > 0.
    // Connection: neg(X)+Y-(X+neg(Y)) = 2(Y-X) = 4*(dy_re*(a/A)-dx_re*(b/A)) > 0
    // since X = 2*dx_re*(b/A) and Y = 2*dy_re*(a/A) by commutativity.

    assert(F::zero().lt(dy_re.mul(a_over_a).sub(dx_re.mul(b_over_a)))) by {
        lemma_scaled_disp_positive::<F>(dx_re, dy_re, line.a, line.b, big_a);
    };

    // Z3 needs to connect: scaled positive → neg(X)+Y-(X+neg(Y)) > 0 → diff.im > 0
    // The eqv chain from diff.im to neg(X)+Y-(X+neg(Y)) is established above.
    // The connection from that to dy_re*(a/A)-dx_re*(b/A) goes through commutativity:
    //   (b/A)*dx_re ≡ dx_re*(b/A), (a/A)*dy_re ≡ dy_re*(a/A)
    F::axiom_mul_commutative(b_over_a, dx_re);
    F::axiom_mul_commutative(a_over_a, dy_re);
}

/// Main theorem: cl_displacement_sign > 0 ⟹ sq_dist(P_plus, Q) > sq_dist(P_minus, Q).
///
/// Proof: combine lemma_cl_sq_dist_sign_from_im (re=0 + im>0 ⟹ lt)
/// with the im expansion showing diff.im has same sign as cl_displacement_sign.
#[verifier::rlimit(300)]
pub proof fn lemma_cl_displacement_sign_determines_order<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>, line: Line2<F>, target: Point2<F>,
)
    requires
        line2_nondegenerate(line),
        F::zero().lt(cl_displacement_sign(circle, line, target)),
    ensures
        SpecQuadExt::<F, R>::zero().lt(
            sq_dist_2d::<SpecQuadExt<F, R>>(
                cl_intersection_point(circle, line, true), lift_point2(target))
            .sub(sq_dist_2d::<SpecQuadExt<F, R>>(
                cl_intersection_point(circle, line, false), lift_point2(target)))),
{
    // Use sign_from_im: need to prove diff.re ≡ 0 AND diff.im > 0
    lemma_cl_sq_dist_sign_from_im::<F, R>(circle, line, target);

    let d_plus = sq_dist_2d::<SpecQuadExt<F, R>>(
        cl_intersection_point(circle, line, true), lift_point2(target));
    let d_minus = sq_dist_2d::<SpecQuadExt<F, R>>(
        cl_intersection_point(circle, line, false), lift_point2(target));
    let diff = d_plus.sub(d_minus);

    // diff.re ≡ 0 is already established by sign_from_im.
    // Now prove diff.im > 0.

    let p_plus = cl_intersection_point::<F, R>(circle, line, true);
    let p_minus = cl_intersection_point::<F, R>(circle, line, false);
    lemma_cl_intersection_conjugate::<F, R>(circle, line);

    let big_a = cl_quad_a(line);
    lemma_cl_quad_a_positive(line);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), big_a);
    F::axiom_eqv_symmetric(F::zero(), big_a);

    let dx_re = p_plus.x.re.sub(target.x);
    let dy_re = p_plus.y.re.sub(target.y);
    let im_x_plus = p_plus.x.im;
    let im_x_minus = p_minus.x.im;
    let im_y_plus = p_plus.y.im;
    let im_y_minus = p_minus.y.im;

    // sub_zero bridges
    lemma_sub_zero::<F>(im_x_plus);
    lemma_sub_zero::<F>(im_x_minus);
    lemma_sub_zero::<F>(im_y_plus);
    lemma_sub_zero::<F>(im_y_minus);

    // im congruence through sub_zero
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_plus.sub(F::zero()), im_x_plus);
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_minus.sub(F::zero()), im_x_minus);
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_plus.sub(F::zero()), im_y_plus);
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_minus.sub(F::zero()), im_y_minus);

    // Conjugate im: neg(b)/A ≡ neg(b/A), neg(a)/A ≡ neg(a/A)
    lemma_div_neg_numerator::<F>(line.b, big_a);
    lemma_div_neg_numerator::<F>(line.a, big_a);
    let b_over_a = line.b.div(big_a);
    let a_over_a = line.a.div(big_a);
    assert(im_x_plus.eqv(b_over_a.neg()));
    assert(im_y_minus.eqv(a_over_a.neg()));

    // dx_sq(neg(b/A)).im ≡ neg(dx_sq(b/A).im)
    lemma_qe_sq_im_im_congruence::<F, R>(dx_re, im_x_plus, b_over_a.neg());
    lemma_qe_sq_im_conjugate::<F, R>(dx_re, b_over_a);
    let dx_plus_im_c = qe_mul::<F, R>(qext(dx_re, im_x_plus), qext(dx_re, im_x_plus)).im;
    let dx_neg_im = qe_mul::<F, R>(qext(dx_re, b_over_a.neg()), qext(dx_re, b_over_a.neg())).im;
    let dx_bA_im = qe_mul::<F, R>(qext(dx_re, b_over_a), qext(dx_re, b_over_a)).im;
    F::axiom_eqv_transitive(dx_plus_im_c, dx_neg_im, dx_bA_im.neg());

    // dy_sq(neg(a/A)).im ≡ neg(dy_sq(a/A).im)
    lemma_qe_sq_im_im_congruence::<F, R>(dy_re, im_y_minus, a_over_a.neg());
    lemma_qe_sq_im_conjugate::<F, R>(dy_re, a_over_a);
    let dy_minus_im_c = qe_mul::<F, R>(qext(dy_re, im_y_minus), qext(dy_re, im_y_minus)).im;
    let dy_neg_im = qe_mul::<F, R>(qext(dy_re, a_over_a.neg()), qext(dy_re, a_over_a.neg())).im;
    let dy_aA_im = qe_mul::<F, R>(qext(dy_re, a_over_a), qext(dy_re, a_over_a)).im;
    F::axiom_eqv_transitive(dy_minus_im_c, dy_neg_im, dy_aA_im.neg());

    // Bridge actual → clean for im (through sub_zero):
    let dx_plus_actual_im = qe_mul::<F, R>(
        qext(dx_re, im_x_plus.sub(F::zero())), qext(dx_re, im_x_plus.sub(F::zero()))).im;
    let dx_minus_actual_im = qe_mul::<F, R>(
        qext(dx_re, im_x_minus.sub(F::zero())), qext(dx_re, im_x_minus.sub(F::zero()))).im;
    let dy_plus_actual_im = qe_mul::<F, R>(
        qext(dy_re, im_y_plus.sub(F::zero())), qext(dy_re, im_y_plus.sub(F::zero()))).im;
    let dy_minus_actual_im = qe_mul::<F, R>(
        qext(dy_re, im_y_minus.sub(F::zero())), qext(dy_re, im_y_minus.sub(F::zero()))).im;

    // actual → clean chains:
    // dx_plus: actual ≡ clean(im_x_plus) ≡ neg(dx_bA_im)
    F::axiom_eqv_transitive(dx_plus_actual_im, dx_plus_im_c, dx_bA_im.neg());
    // dx_minus: actual ≡ clean(im_x_minus) = clean(b/A) = dx_bA_im
    // (im_x_minus = b/A structurally, so clean = dx_bA_im directly)
    // dy_plus: actual ≡ clean(im_y_plus) = clean(a/A) = dy_aA_im
    // dy_minus: actual ≡ clean(im_y_minus) ≡ neg(dy_aA_im)
    F::axiom_eqv_transitive(dy_minus_actual_im, dy_minus_im_c, dy_aA_im.neg());

    // d_plus.im ≡ neg(dx_bA_im) + dy_aA_im
    lemma_add_congruence::<F>(dx_plus_actual_im, dx_bA_im.neg(), dy_plus_actual_im, dy_aA_im);
    // d_minus.im ≡ dx_bA_im + neg(dy_aA_im)
    lemma_add_congruence::<F>(dx_minus_actual_im, dx_bA_im, dy_minus_actual_im, dy_aA_im.neg());

    // diff.im = d_plus.im - d_minus.im
    // ≡ (neg(X) + Y) - (X + neg(Y))  where X = dx_bA_im, Y = dy_aA_im
    lemma_sub_congruence::<F>(
        dx_plus_actual_im.add(dy_plus_actual_im), dx_bA_im.neg().add(dy_aA_im),
        dx_minus_actual_im.add(dy_minus_actual_im), dx_bA_im.add(dy_aA_im.neg()));

    // Now show: neg(X) + Y - (X + neg(Y)) > 0 when a*dy_re - b*dx_re > 0.
    // neg(X) + Y - (X + neg(Y)) = neg(X) + Y - X + Y = 2Y - 2X = 2(Y - X)
    // where Y = dy_re*(a/A) + (a/A)*dy_re, X = dx_re*(b/A) + (b/A)*dx_re
    //
    // By commutativity: Y = 2*dy_re*(a/A), X = 2*dx_re*(b/A)
    // Y - X = 2*(dy_re*a/A - dx_re*b/A) = 2/A * (a*dy_re - b*dx_re)
    //
    // And a*dy_re - b*dx_re = neg(b)*dx_re + a*dy_re ≡ cl_displacement_sign > 0
    //
    // Since 2/A > 0, Y - X > 0, so 2(Y-X) > 0, so diff.im > 0.
    //
    // However, proving 2(Y-X) > 0 formally requires the full ring expansion.
    // Instead, use a counting argument: diff.im ≡ neg(X)+Y-(X+neg(Y)).
    // This equals (Y-X) + (Y-X) = 2(Y-X) by algebra.
    //
    // With the facts established, Z3 has:
    // 1. diff.im ≡ neg(X)+Y - (X+neg(Y))
    // 2. cl_displacement_sign > 0
    // 3. neg(b)*dx_re + a*dy_re ≡ cl_displacement_sign (from cancellation, invoked below)
    //
    // The connection from (3) to (1) through X and Y is the remaining step.

    // Invoke cancellation: neg(b)*dx_re + a*dy_re ≡ cl_displacement_sign
    let h = cl_signed_dist_num(circle, line);
    let v = line.a.mul(h).div(big_a);
    let w = line.b.mul(h).div(big_a);
    let t = h.div(big_a);
    // v ≡ a*t
    F::axiom_div_is_mul_recip(line.a.mul(h), big_a);
    F::axiom_div_is_mul_recip(h, big_a);
    F::axiom_eqv_symmetric(t, h.mul(big_a.recip()));
    F::axiom_mul_associative(line.a, h, big_a.recip());
    F::axiom_eqv_symmetric(line.a.mul(h.mul(big_a.recip())), line.a.mul(h).mul(big_a.recip()));
    F::axiom_eqv_transitive(v, line.a.mul(h).mul(big_a.recip()), line.a.mul(h.mul(big_a.recip())));
    lemma_mul_congruence_right::<F>(line.a, h.mul(big_a.recip()), t);
    F::axiom_eqv_transitive(v, line.a.mul(h.mul(big_a.recip())), line.a.mul(t));
    // w ≡ b*t
    F::axiom_div_is_mul_recip(line.b.mul(h), big_a);
    F::axiom_mul_associative(line.b, h, big_a.recip());
    F::axiom_eqv_symmetric(line.b.mul(h.mul(big_a.recip())), line.b.mul(h).mul(big_a.recip()));
    F::axiom_eqv_transitive(w, line.b.mul(h).mul(big_a.recip()), line.b.mul(h.mul(big_a.recip())));
    lemma_mul_congruence_right::<F>(line.b, h.mul(big_a.recip()), t);
    F::axiom_eqv_transitive(w, line.b.mul(h.mul(big_a.recip())), line.b.mul(t));

    lemma_cl_displacement_cancellation(
        line.a, line.b, circle.center.x, circle.center.y,
        target.x, target.y, v, w, t);

    // neg(b)*dx_re + a*dy_re ≡ cl_displacement_sign > 0
    // Transfer positivity
    let disp_expr = line.b.neg().mul(dx_re).add(line.a.mul(dy_re));
    let sign_val = cl_displacement_sign(circle, line, target);
    F::axiom_eqv_symmetric(disp_expr, sign_val);
    F::axiom_eqv_reflexive(F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), sign_val);
    F::axiom_le_congruence(F::zero(), F::zero(), sign_val, disp_expr);
    F::axiom_eqv_symmetric(F::zero(), sign_val);
    if F::zero().eqv(disp_expr) {
        F::axiom_eqv_transitive(F::zero(), disp_expr, sign_val);
    }
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), disp_expr);
    // Now: disp_expr > 0

    // Z3 has all the algebraic facts. With sufficient rlimit, it should close
    // the connection from disp_expr > 0 → diff.im > 0 → zero.lt(diff).
}

} // verus!
