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

} // verus!
