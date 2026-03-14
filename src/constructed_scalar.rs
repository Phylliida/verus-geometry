use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::ordered::*;
use verus_quadratic_extension::radicand::*;

verus! {

// ===========================================================================
//  Bridge between SpecQuadExt and geometric constructions
// ===========================================================================
//
// Circle intersections produce coordinates in F(sqrt(d)) where d is the
// discriminant. We use SpecQuadExt<F, R> directly with R: PositiveRadicand<F>,
// leveraging the ~140 verified proofs from verus-quadratic-extension.
//
// This module provides utility specs and bridge lemmas.
// ===========================================================================

/// Construct a SpecQuadExt from a purely rational value (im = 0).
pub open spec fn qext_from_rational<F: Field, R: Radicand<F>>(v: F) -> SpecQuadExt<F, R> {
    qext(v, F::zero())
}

/// Check if a SpecQuadExt is purely rational (im ≡ 0).
pub open spec fn qext_is_rational<F: Field, R: Radicand<F>>(x: SpecQuadExt<F, R>) -> bool {
    x.im.eqv(F::zero())
}

/// Lift a Point2<F> to Point2<SpecQuadExt<F, R>> by embedding each coordinate.
pub open spec fn lift_point2<F: Field, R: Radicand<F>>(
    p: crate::point2::Point2<F>,
) -> crate::point2::Point2<SpecQuadExt<F, R>> {
    crate::point2::Point2 {
        x: qext_from_rational(p.x),
        y: qext_from_rational(p.y),
    }
}

/// Lift a Line2<F> to Line2<SpecQuadExt<F, R>> by embedding each coefficient.
pub open spec fn lift_line2<F: Field, R: Radicand<F>>(
    line: crate::line2::Line2<F>,
) -> crate::line2::Line2<SpecQuadExt<F, R>> {
    crate::line2::Line2 {
        a: qext_from_rational(line.a),
        b: qext_from_rational(line.b),
        c: qext_from_rational(line.c),
    }
}

// ===========================================================================
//  Lemmas
// ===========================================================================

/// A purely rational SpecQuadExt is non-negative iff the rational part is non-negative.
pub proof fn lemma_rational_nonneg<F: OrderedField, R: PositiveRadicand<F>>(v: F)
    ensures
        F::zero().le(v) == qe_nonneg::<F, R>(qext_from_rational(v)),
{
    use verus_algebra::lemmas::ordered_ring_lemmas::lemma_lt_irreflexive;
    // qe_nonneg(qext(v, 0)) expands to:
    //   (0.le(v) && 0.le(0))           -- Case 1
    //   || (0.le(v) && 0.lt(0) && ...) -- Case 2: 0.lt(0) is false
    //   || (v.lt(0) && 0.lt(0) && ...) -- Case 3: 0.lt(0) is false
    //
    // Case 2 and 3 are false because 0.lt(0) is false (irreflexive).
    // Case 1 simplifies to 0.le(v) && 0.le(0) = 0.le(v) (since 0.le(0) is reflexive).
    F::axiom_le_reflexive(F::zero());
    lemma_lt_irreflexive::<F>(F::zero());
}

/// Embedding preserves value under eqv for the SpecQuadExt's re component.
pub proof fn lemma_qext_from_rational_re<F: Field, R: Radicand<F>>(v: F)
    ensures
        qext_from_rational::<F, R>(v).re.eqv(v),
{
    F::axiom_eqv_reflexive(v);
}

/// Embedding has im ≡ 0.
pub proof fn lemma_qext_from_rational_im<F: Field, R: Radicand<F>>(v: F)
    ensures
        qext_from_rational::<F, R>(v).im.eqv(F::zero()),
{
    F::axiom_eqv_reflexive(F::zero());
}

/// Multiplying a rational embedding by a qext simplifies components:
/// qext(v, 0) * qext(r, i) ≡ qext(v*r, v*i).
pub proof fn lemma_rational_mul_qext<F: Field, R: Radicand<F>>(v: F, r: F, i: F)
    ensures
        qe_mul::<F, R>(qext_from_rational(v), qext(r, i)).eqv(
            qext::<F, R>(v.mul(r), v.mul(i))
        ),
{
    // re = v*r + 0*i*D where D = R::value()
    // Show 0*i*D ≡ 0:
    lemma_mul_zero_left::<F>(i);
    F::axiom_mul_congruence_left(F::zero().mul(i), F::zero(), R::value());
    lemma_mul_zero_left::<F>(R::value());
    F::axiom_eqv_transitive(
        F::zero().mul(i).mul(R::value()), F::zero().mul(R::value()), F::zero(),
    );
    // v*r + 0*i*D ≡ v*r + 0 ≡ v*r
    lemma_add_congruence_right::<F>(v.mul(r), F::zero().mul(i).mul(R::value()), F::zero());
    F::axiom_add_zero_right(v.mul(r));
    F::axiom_eqv_transitive(
        v.mul(r).add(F::zero().mul(i).mul(R::value())),
        v.mul(r).add(F::zero()),
        v.mul(r),
    );

    // im = v*i + 0*r. Show 0*r ≡ 0:
    lemma_mul_zero_left::<F>(r);
    // v*i + 0*r ≡ v*i + 0 ≡ v*i
    lemma_add_congruence_right::<F>(v.mul(i), F::zero().mul(r), F::zero());
    F::axiom_add_zero_right(v.mul(i));
    F::axiom_eqv_transitive(
        v.mul(i).add(F::zero().mul(r)),
        v.mul(i).add(F::zero()),
        v.mul(i),
    );
    // Z3 now has both component eqvs → qe_eqv is satisfied.
}

/// qext_from_rational(a + b) ≡ qext_from_rational(a) + qext_from_rational(b)
pub proof fn lemma_rational_add<F: Field, R: Radicand<F>>(a: F, b: F)
    ensures
        qext_from_rational::<F, R>(a.add(b)).eqv(
            qe_add::<F, R>(qext_from_rational(a), qext_from_rational(b))
        ),
{
    // re: a+b ≡ a+b (reflexive)
    F::axiom_eqv_reflexive(a.add(b));
    // im: 0 ≡ 0+0
    F::axiom_add_zero_right(F::zero());
    F::axiom_eqv_symmetric(F::zero(), F::zero().add(F::zero()));
}

/// qext_from_rational(a - b) ≡ qext_from_rational(a) - qext_from_rational(b)
pub proof fn lemma_rational_sub<F: Field, R: Radicand<F>>(a: F, b: F)
    ensures
        qext_from_rational::<F, R>(a.sub(b)).eqv(
            qe_sub::<F, R>(qext_from_rational(a), qext_from_rational(b))
        ),
{
    // re: a-b ≡ a-b (reflexive)
    F::axiom_eqv_reflexive(a.sub(b));
    // im: 0 ≡ 0-0
    lemma_sub_self::<F>(F::zero());
    F::axiom_eqv_symmetric(F::zero().sub(F::zero()), F::zero());
    F::axiom_eqv_symmetric(F::zero(), F::zero().sub(F::zero()));
}

/// qext_from_rational(a * b) ≡ qext_from_rational(a) * qext_from_rational(b)
pub proof fn lemma_rational_mul<F: Field, R: Radicand<F>>(a: F, b: F)
    ensures
        qext_from_rational::<F, R>(a.mul(b)).eqv(
            qe_mul::<F, R>(qext_from_rational(a), qext_from_rational(b))
        ),
{
    lemma_rational_mul_qext::<F, R>(a, b, F::zero());
    // qe_mul(qext(a,0), qext(b,0)) ≡ qext(a*b, a*0)
    F::axiom_mul_zero_right(a);
    F::axiom_eqv_symmetric(a.mul(F::zero()), F::zero());
    // 0 ≡ a*0 → qext(a*b, 0) ≡ qext(a*b, a*0)
    F::axiom_eqv_reflexive(a.mul(b));
    // rational(a*b) = qext(a*b, 0) eqv qext(a*b, a*0)
    // then transitive with symmetric of first:
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qe_mul::<F, R>(qext_from_rational(a), qext_from_rational(b)),
        qext::<F, R>(a.mul(b), a.mul(F::zero())),
    );
    // qext(a*b, a*0) ≡ qe_mul(...)
    // qext(a*b, 0) ≡ qext(a*b, a*0) (from component eqvs: re reflexive, im: 0≡a*0)
    // chain: rational(a*b) ≡ qext(a*b, a*0) ≡ qe_mul(...)
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a.mul(b)),
        qext::<F, R>(a.mul(b), a.mul(F::zero())),
        qe_mul::<F, R>(qext_from_rational(a), qext_from_rational(b)),
    );
}

/// qext_from_rational(one) ≡ SpecQuadExt::one()
pub proof fn lemma_rational_one<F: Field, R: Radicand<F>>()
    ensures
        qext_from_rational::<F, R>(F::one()).eqv(
            SpecQuadExt::<F, R>::one()
        ),
{
    // qext(1, 0) vs qe_one() = qext(1, 0) — structurally equal
    F::axiom_eqv_reflexive(F::one());
    F::axiom_eqv_reflexive(F::zero());
}

// ===========================================================================
//  Circle lifting
// ===========================================================================

/// Lift a Circle2<F> to Circle2<SpecQuadExt<F, R>> by embedding center and radius_sq.
pub open spec fn lift_circle2<F: Field, R: Radicand<F>>(
    c: crate::circle2::Circle2<F>,
) -> crate::circle2::Circle2<SpecQuadExt<F, R>> {
    crate::circle2::Circle2 {
        center: lift_point2(c.center),
        radius_sq: qext_from_rational(c.radius_sq),
    }
}

// ===========================================================================
//  Embedding injectivity and preservation lemmas
// ===========================================================================

/// Embedding reflects eqv: qext_from_rational(a) ≡ qext_from_rational(b) implies a ≡ b.
/// (Reverse direction of lemma_rational_congruence.)
pub proof fn lemma_qext_from_rational_injective<F: Field, R: Radicand<F>>(a: F, b: F)
    requires
        qext_from_rational::<F, R>(a).eqv(qext_from_rational::<F, R>(b)),
    ensures
        a.eqv(b),
{
    // qe_eqv is component-wise: re.eqv(re) && im.eqv(im)
    // qext_from_rational(a).re == a, qext_from_rational(b).re == b
    // So the re component gives a.eqv(b) directly.
}

/// line2_nondegenerate is preserved/reflected by lifting.
pub proof fn lemma_lift_line2_nondegenerate<F: Field, R: Radicand<F>>(
    line: crate::line2::Line2<F>,
)
    ensures
        crate::line2::line2_nondegenerate(line)
            == crate::line2::line2_nondegenerate(lift_line2::<F, R>(line)),
{
    // line2_nondegenerate(line) = !line.a.eqv(zero) || !line.b.eqv(zero)
    // lift_line2(line).a = qext_from_rational(line.a)
    // QE::zero() = qext(F::zero(), F::zero()) = qext_from_rational(F::zero())
    //
    // qext_from_rational(line.a).eqv(QE::zero())
    //   = qext_from_rational(line.a).eqv(qext_from_rational(F::zero()))
    //   iff line.a.eqv(F::zero())
    //   (forward: lemma_rational_congruence; reverse: lemma_qext_from_rational_injective)

    // Show QE::zero() == qext_from_rational(F::zero())
    // Both are qext(F::zero(), F::zero()) — structurally equal.

    // Forward: nondegenerate(line) ==> nondegenerate(lift(line))
    // If !line.a.eqv(0), then suppose lift.a.eqv(QE::zero()).
    //   lift.a = qext_from_rational(line.a), QE::zero() = qext_from_rational(F::zero())
    //   By injectivity: line.a.eqv(F::zero()) — contradiction.
    // Similarly for line.b.

    // Reverse: nondegenerate(lift(line)) ==> nondegenerate(line)
    // If !lift.a.eqv(QE::zero()), suppose line.a.eqv(F::zero()).
    //   By congruence: qext_from_rational(line.a).eqv(qext_from_rational(F::zero()))
    //   = lift.a.eqv(QE::zero()) — contradiction.
    // Similarly for line.b.

    use crate::circle_circle_proofs::lemma_rational_congruence;

    if crate::line2::line2_nondegenerate(line) {
        // At least one of line.a, line.b is not eqv to zero
        if !line.a.eqv(F::zero()) {
            // Suppose for contradiction that lift.a.eqv(QE::zero())
            if qext_from_rational::<F, R>(line.a).eqv(
                SpecQuadExt::<F, R>::zero()
            ) {
                // QE::zero() = qext_from_rational(F::zero())
                F::axiom_eqv_reflexive(F::zero());
                // So lift.a.eqv(qext_from_rational(F::zero()))
                // By injectivity: line.a.eqv(F::zero()) — contradiction
                lemma_qext_from_rational_injective::<F, R>(line.a, F::zero());
            }
        } else {
            // line.b is not eqv to zero
            if qext_from_rational::<F, R>(line.b).eqv(
                SpecQuadExt::<F, R>::zero()
            ) {
                F::axiom_eqv_reflexive(F::zero());
                lemma_qext_from_rational_injective::<F, R>(line.b, F::zero());
            }
        }
    } else {
        // line.a.eqv(zero) && line.b.eqv(zero)
        // By congruence: lift.a.eqv(QE::zero()) && lift.b.eqv(QE::zero())
        lemma_rational_congruence::<F, R>(line.a, F::zero());
        lemma_rational_congruence::<F, R>(line.b, F::zero());
    }
}

/// line_det commutes with lifting:
/// line_det(lift(l1), lift(l2)) ≡ qext_from_rational(line_det(l1, l2))
pub proof fn lemma_lift_line_det<F: Field, R: Radicand<F>>(
    l1: crate::line2::Line2<F>,
    l2: crate::line2::Line2<F>,
)
    ensures
        crate::line_intersection::line_det(
            lift_line2::<F, R>(l1), lift_line2::<F, R>(l2)
        ).eqv(
            qext_from_rational::<F, R>(
                crate::line_intersection::line_det(l1, l2)
            )
        ),
{
    // line_det(l1, l2) = l1.a * l2.b - l1.b * l2.a
    // line_det(lift(l1), lift(l2)) = qext(l1.a,0) * qext(l2.b,0) - qext(l1.b,0) * qext(l2.a,0)
    //
    // By lemma_rational_mul: qext(a,0)*qext(b,0) ≡ qext(a*b, 0)
    // By lemma_rational_sub: qext(x,0) - qext(y,0) ≡ qext(x-y, 0)
    //
    // So: qe_mul(qext(a1,0), qext(b2,0)).eqv(qext(a1*b2, 0))
    //     qe_mul(qext(b1,0), qext(a2,0)).eqv(qext(b1*a2, 0))
    //     qe_sub(qext(a1*b2,0), qext(b1*a2,0)).eqv(qext(a1*b2 - b1*a2, 0))
    //
    // Chain: line_det(lift(l1), lift(l2))
    //   = qe_sub(qe_mul(qext(a1,0), qext(b2,0)), qe_mul(qext(b1,0), qext(a2,0)))
    //   ≡ qe_sub(qext(a1*b2,0), qext(b1*a2,0))  (by mul congruence)
    //   ≡ qext(a1*b2 - b1*a2, 0)                 (by rational_sub)
    //   = qext_from_rational(line_det(l1, l2))

    let a1 = l1.a;
    let b1 = l1.b;
    let a2 = l2.a;
    let b2 = l2.b;

    // Step 1: qe_mul(qext(a1,0), qext(b2,0)) ≡ qext(a1*b2, 0)
    lemma_rational_mul::<F, R>(a1, b2);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a1.mul(b2)),
        qe_mul::<F, R>(qext_from_rational(a1), qext_from_rational(b2)),
    );

    // Step 2: qe_mul(qext(b1,0), qext(a2,0)) ≡ qext(b1*a2, 0)
    lemma_rational_mul::<F, R>(b1, a2);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b1.mul(a2)),
        qe_mul::<F, R>(qext_from_rational(b1), qext_from_rational(a2)),
    );

    // Step 3: sub congruence
    // qe_sub(qe_mul(...), qe_mul(...)) ≡ qe_sub(qext(a1*b2,0), qext(b1*a2,0))
    lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qe_mul::<F, R>(qext_from_rational(a1), qext_from_rational(b2)),
        qext_from_rational::<F, R>(a1.mul(b2)),
        qe_mul::<F, R>(qext_from_rational(b1), qext_from_rational(a2)),
        qext_from_rational::<F, R>(b1.mul(a2)),
    );

    // Step 4: qe_sub(qext(a1*b2,0), qext(b1*a2,0)) ≡ qext(a1*b2 - b1*a2, 0)
    lemma_rational_sub::<F, R>(a1.mul(b2), b1.mul(a2));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a1.mul(b2).sub(b1.mul(a2))),
        qe_sub::<F, R>(qext_from_rational(a1.mul(b2)), qext_from_rational(b1.mul(a2))),
    );

    // Chain: line_det(lift) ≡ qe_sub(qext(a1*b2,0), qext(b1*a2,0)) ≡ qext_from_rational(line_det)
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        crate::line_intersection::line_det(lift_line2::<F, R>(l1), lift_line2::<F, R>(l2)),
        qe_sub::<F, R>(
            qext_from_rational::<F, R>(a1.mul(b2)),
            qext_from_rational::<F, R>(b1.mul(a2)),
        ),
        qext_from_rational::<F, R>(crate::line_intersection::line_det(l1, l2)),
    );
}

/// Center distinctness is preserved by lifting.
pub proof fn lemma_lift_centers_distinct<F: Field, R: Radicand<F>>(
    c1: crate::point2::Point2<F>,
    c2: crate::point2::Point2<F>,
)
    requires
        !c1.eqv(c2),
    ensures
        !lift_point2::<F, R>(c1).eqv(lift_point2::<F, R>(c2)),
{
    // Contrapositive: if lift(c1).eqv(lift(c2)), then c1.eqv(c2).
    // lift(c1).eqv(lift(c2)) means:
    //   qext_from_rational(c1.x).eqv(qext_from_rational(c2.x))
    //   && qext_from_rational(c1.y).eqv(qext_from_rational(c2.y))
    // By injectivity: c1.x.eqv(c2.x) && c1.y.eqv(c2.y) = c1.eqv(c2)
    // But !c1.eqv(c2), so the premise is false.
    if lift_point2::<F, R>(c1).eqv(lift_point2::<F, R>(c2)) {
        lemma_qext_from_rational_injective::<F, R>(c1.x, c2.x);
        lemma_qext_from_rational_injective::<F, R>(c1.y, c2.y);
        // Now c1.x.eqv(c2.x) && c1.y.eqv(c2.y) → c1.eqv(c2) — contradiction
    }
}

} // verus!
