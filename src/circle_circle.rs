use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::convex::two;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
use crate::point2::*;
use crate::line2::*;
use crate::circle2::*;
use crate::circle_line::*;
use crate::circle_circle_proofs::*;
use crate::voronoi::sq_dist_2d;
use crate::constructed_scalar::lift_point2;

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
    // Abbreviations
    let px = p.x;
    let py = p.y;
    let c1x = c1.center.x;
    let c1y = c1.center.y;
    let c2x = c2.center.x;
    let c2y = c2.center.y;
    let r1sq = c1.radius_sq;
    let r2sq = c2.radius_sq;

    // --- The radical axis components ---
    let t = two::<T>();
    let la = t.mul(c2x.sub(c1x));
    let lb = t.mul(c2y.sub(c1y));
    let c1_sq = c1x.mul(c1x).add(c1y.mul(c1y));
    let c2_sq = c2x.mul(c2x).add(c2y.mul(c2y));
    let lc = c1_sq.sub(r1sq).sub(c2_sq.sub(r2sq));

    // --- Component squared differences ---
    let xd1 = px.sub(c1x).mul(px.sub(c1x));  // (px - c1x)²
    let yd1 = py.sub(c1y).mul(py.sub(c1y));  // (py - c1y)²
    let xd2 = px.sub(c2x).mul(px.sub(c2x));  // (px - c2x)²
    let yd2 = py.sub(c2y).mul(py.sub(c2y));  // (py - c2y)²

    // D1 = xd1 + yd1 (definitionally = norm_sq(sub2(p, c1.center)))
    // D2 = xd2 + yd2 (definitionally = norm_sq(sub2(p, c2.center)))
    let d1 = xd1.add(yd1);
    let d2 = xd2.add(yd2);

    // Step 1: D1 - D2 ≡ r1sq - r2sq (from circle conditions + sub_congruence)
    // point_on_circle2 gives: d1 ≡ r1sq, d2 ≡ r2sq
    additive_group_lemmas::lemma_sub_congruence::<T>(d1, r1sq, d2, r2sq);
    // Now: d1.sub(d2).eqv(r1sq.sub(r2sq))

    // Step 2: D1 - D2 ≡ (xd1 - xd2) + (yd1 - yd2)  via sum_sub_rearrange
    lemma_sum_sub_rearrange::<T>(xd1, yd1, xd2, yd2);
    // Now: xd1.add(yd1).sub(xd2.add(yd2)).eqv(xd1.sub(xd2).add(yd1.sub(yd2)))

    // Step 3: Apply sq_diff for x and y components
    // lemma_sq_diff(px, c1x, c2x): (px-c1x)²-(px-c2x)² ≡ two*(c2x-c1x)*px + c1x²-c2x²
    lemma_sq_diff::<T>(px, c1x, c2x);
    let ax = t.mul(c2x.sub(c1x)).mul(px);
    let kx = c1x.mul(c1x).sub(c2x.mul(c2x));

    // lemma_sq_diff(py, c1y, c2y): (py-c1y)²-(py-c2y)² ≡ two*(c2y-c1y)*py + c1y²-c2y²
    lemma_sq_diff::<T>(py, c1y, c2y);
    let by_ = t.mul(c2y.sub(c1y)).mul(py);
    let ky = c1y.mul(c1y).sub(c2y.mul(c2y));

    // Step 4: (xd1-xd2) + (yd1-yd2) ≡ (ax+kx) + (by_+ky)
    additive_group_lemmas::lemma_add_congruence::<T>(
        xd1.sub(xd2), ax.add(kx),
        yd1.sub(yd2), by_.add(ky),
    );

    // Step 5: Rearrange (ax+kx)+(by_+ky) ≡ (ax+by_)+(kx+ky)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(ax, kx, by_, ky);

    // Step 6: kx+ky = (c1x²-c2x²)+(c1y²-c2y²) ≡ (c1x²+c1y²)-(c2x²+c2y²) = c1_sq-c2_sq
    lemma_diff_sum_rearrange::<T>(c1x.mul(c1x), c2x.mul(c2x), c1y.mul(c1y), c2y.mul(c2y));
    // kx.add(ky) ≡ c1_sq.sub(c2_sq)

    // Step 7: (ax+by_)+(kx+ky) ≡ (ax+by_)+(c1_sq-c2_sq)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        ax.add(by_), kx.add(ky), c1_sq.sub(c2_sq),
    );

    // Note: ax = la*px and by_ = lb*py (definitionally), so ax+by_ = la*px + lb*py = E
    let e = la.mul(px).add(lb.mul(py));
    // e == ax.add(by_) definitionally since la = t.mul(c2x.sub(c1x)) and ax = la.mul(px)

    // Chain: D1-D2 ≡ (xd1-xd2)+(yd1-yd2) ≡ (ax+kx)+(by_+ky) ≡ (ax+by_)+(kx+ky) ≡ E+(c1_sq-c2_sq)
    T::axiom_eqv_transitive(
        d1.sub(d2),
        xd1.sub(xd2).add(yd1.sub(yd2)),
        ax.add(kx).add(by_.add(ky)),
    );
    T::axiom_eqv_transitive(
        d1.sub(d2),
        ax.add(kx).add(by_.add(ky)),
        ax.add(by_).add(kx.add(ky)),
    );
    T::axiom_eqv_transitive(
        d1.sub(d2),
        ax.add(by_).add(kx.add(ky)),
        e.add(c1_sq.sub(c2_sq)),
    );
    // Now: d1.sub(d2).eqv(e.add(c1_sq.sub(c2_sq)))

    // Step 8: From Step 1 and the chain: E + (c1_sq-c2_sq) ≡ r1sq-r2sq
    T::axiom_eqv_symmetric(d1.sub(d2), e.add(c1_sq.sub(c2_sq)));
    T::axiom_eqv_transitive(
        e.add(c1_sq.sub(c2_sq)),
        d1.sub(d2),
        r1sq.sub(r2sq),
    );
    // Now: e.add(c1_sq.sub(c2_sq)).eqv(r1sq.sub(r2sq))

    // Step 9: L.c ≡ (c1_sq-c2_sq) - (r1sq-r2sq)  via sub_sub_rearrange
    lemma_sub_sub_rearrange::<T>(c1_sq, r1sq, c2_sq, r2sq);
    // lc = (c1_sq-r1sq)-(c2_sq-r2sq) ≡ (c1_sq-c2_sq)-(r1sq-r2sq)

    // Step 10: E + L.c ≡ E + ((c1_sq-c2_sq)-(r1sq-r2sq))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        e, lc, c1_sq.sub(c2_sq).sub(r1sq.sub(r2sq)),
    );
    // Now: e.add(lc).eqv(e.add(c1_sq.sub(c2_sq).sub(r1sq.sub(r2sq))))

    // Step 11: E + ((c1_sq-c2_sq) - (r1sq-r2sq)) ≡ (E + (c1_sq-c2_sq)) - (r1sq-r2sq)
    lemma_add_sub_assoc::<T>(e, c1_sq.sub(c2_sq), r1sq.sub(r2sq));

    // Chain: E + L.c ≡ (E+(c1_sq-c2_sq)) - (r1sq-r2sq)
    T::axiom_eqv_transitive(
        e.add(lc),
        e.add(c1_sq.sub(c2_sq).sub(r1sq.sub(r2sq))),
        e.add(c1_sq.sub(c2_sq)).sub(r1sq.sub(r2sq)),
    );

    // Step 12: (E+(c1_sq-c2_sq)) ≡ (r1sq-r2sq) from Step 8,
    // so (E+(c1_sq-c2_sq))-(r1sq-r2sq) ≡ (r1sq-r2sq)-(r1sq-r2sq)
    T::axiom_eqv_reflexive(r1sq.sub(r2sq));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        e.add(c1_sq.sub(c2_sq)), r1sq.sub(r2sq),
        r1sq.sub(r2sq), r1sq.sub(r2sq),
    );

    // (r1sq-r2sq) - (r1sq-r2sq) ≡ 0
    additive_group_lemmas::lemma_sub_self::<T>(r1sq.sub(r2sq));

    // Chain: E + L.c ≡ (r1sq-r2sq)-(r1sq-r2sq) ≡ 0
    T::axiom_eqv_transitive(
        e.add(lc),
        e.add(c1_sq.sub(c2_sq)).sub(r1sq.sub(r2sq)),
        r1sq.sub(r2sq).sub(r1sq.sub(r2sq)),
    );
    T::axiom_eqv_transitive(
        e.add(lc),
        r1sq.sub(r2sq).sub(r1sq.sub(r2sq)),
        T::zero(),
    );
    // Now: e.add(lc).eqv(T::zero())
    // Which is: la.mul(px).add(lb.mul(py)).add(lc).eqv(T::zero())
    // = point_on_line2(radical_axis(c1, c2), p)
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
    // cc_intersection_point = cl_intersection_point(c1, radical_axis(c1,c2), plus)
    // cc_discriminant = cl_discriminant(c1, radical_axis(c1,c2))
    // So this delegates directly to lemma_cl_intersection_on_circle with line = radical_axis.
    let line = radical_axis(c1, c2);

    // The radical axis is nondegenerate because centers differ.
    lemma_radical_axis_nondegenerate::<F>(c1, c2);

    // Now apply the circle-line intersection lemma.
    lemma_cl_intersection_on_circle::<F, R>(c1, line, plus);
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
    // Strategy: instantiate lemma_radical_axis_reverse at SpecQuadExt<F,R> level.
    // The intersection point is on c1 (from lemma_cl_intersection_on_circle)
    // and on the radical axis line (from lemma_cl_intersection_on_line).
    // The reverse radical axis lemma then gives point_on_circle2(c2_qe, p_qe),
    // which is the ensures clause.

    let line = radical_axis(c1, c2);

    // Radical axis is nondegenerate
    lemma_radical_axis_nondegenerate::<F>(c1, c2);

    // The intersection point lies on c1
    lemma_cl_intersection_on_circle::<F, R>(c1, line, plus);

    // The intersection point lies on the lifted radical axis line
    lemma_cl_intersection_on_line::<F, R>(c1, line, plus);

    // Bridge: point on lift_line2(radical_axis(c1,c2)) → point on radical_axis(c1_qe, c2_qe)
    let p_qe = cc_intersection_point::<F, R>(c1, c2, plus);
    lemma_lift_radical_axis_bridge::<F, R>(c1, c2, p_qe);

    // Now we have point_on_circle2(c1_qe, p_qe) and point_on_line2(radical_axis(c1_qe, c2_qe), p_qe)
    // Apply lemma_radical_axis_reverse at the SpecQuadExt<F,R> level
    let c1_qe: Circle2<SpecQuadExt<F, R>> = Circle2 {
        center: crate::constructed_scalar::lift_point2::<F, R>(c1.center),
        radius_sq: crate::constructed_scalar::qext_from_rational::<F, R>(c1.radius_sq),
    };
    let c2_qe: Circle2<SpecQuadExt<F, R>> = Circle2 {
        center: crate::constructed_scalar::lift_point2::<F, R>(c2.center),
        radius_sq: crate::constructed_scalar::qext_from_rational::<F, R>(c2.radius_sq),
    };

    lemma_radical_axis_reverse::<SpecQuadExt<F, R>>(c1_qe, c2_qe, p_qe);
    // Now: point_on_circle2(c2_qe, p_qe) which is:
    // sq_dist_2d(p_qe, lift_point2(c2.center)).eqv(qext_from_rational(c2.radius_sq))
}

/// The displacement sign for circle-circle intersection via radical axis.
pub open spec fn cc_displacement_sign<F: OrderedField>(
    c1: Circle2<F>, c2: Circle2<F>, target: Point2<F>,
) -> F {
    cl_displacement_sign(c1, radical_axis(c1, c2), target)
}

/// Circle-circle displacement ordering (positive case):
/// cc_displacement_sign > 0 ⟹ P_plus is farther from target.
///
/// Direct corollary of the circle-line theorem since
/// cc_intersection_point is defined as cl_intersection_point with the radical axis.
pub proof fn lemma_cc_displacement_sign_determines_order<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, target: Point2<F>,
)
    requires
        line2_nondegenerate(radical_axis(c1, c2)),
        F::zero().lt(cc_displacement_sign(c1, c2, target)),
    ensures
        SpecQuadExt::<F, R>::zero().lt(
            sq_dist_2d::<SpecQuadExt<F, R>>(
                cc_intersection_point(c1, c2, true), lift_point2(target))
            .sub(sq_dist_2d::<SpecQuadExt<F, R>>(
                cc_intersection_point(c1, c2, false), lift_point2(target)))),
{
    lemma_cl_displacement_sign_determines_order::<F, R>(c1, radical_axis(c1, c2), target);
}

/// Circle-circle displacement ordering (negative case):
/// cc_displacement_sign < 0 ⟹ P_minus is farther from target.
pub proof fn lemma_cc_displacement_sign_determines_order_negative<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>, target: Point2<F>,
)
    requires
        line2_nondegenerate(radical_axis(c1, c2)),
        cc_displacement_sign(c1, c2, target).lt(F::zero()),
    ensures
        SpecQuadExt::<F, R>::zero().lt(
            sq_dist_2d::<SpecQuadExt<F, R>>(
                cc_intersection_point(c1, c2, false), lift_point2(target))
            .sub(sq_dist_2d::<SpecQuadExt<F, R>>(
                cc_intersection_point(c1, c2, true), lift_point2(target)))),
{
    lemma_cl_displacement_sign_determines_order_negative::<F, R>(c1, radical_axis(c1, c2), target);
}

} // verus!
