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

} // verus!
