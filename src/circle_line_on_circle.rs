use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::field_lemmas::*;
use verus_algebra::quadratic::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::lemmas::lemma_mul_swap_last_two;
use crate::point2::*;
use crate::line2::*;
use crate::circle2::*;
use crate::voronoi::sq_dist_2d;
use crate::circle_line::*;
use crate::constructed_scalar::*;
use crate::line_intersection::lemma_mul_div_assoc;

verus! {

//  ===========================================================================
//   Helper 1: a*b*c ≡ c*b*a (triple reverse)
//  ===========================================================================

pub proof fn lemma_triple_reverse<F: Field>(a: F, b: F, c: F)
    ensures
        a.mul(b).mul(c).eqv(c.mul(b).mul(a)),
{
    //  a*b*c ≡ a*c*b
    lemma_mul_swap_last_two(a, b, c);
    //  a*c ≡ c*a
    F::axiom_mul_commutative(a, c);
    F::axiom_eqv_reflexive(b);
    lemma_mul_congruence::<F>(a.mul(c), c.mul(a), b, b);
    F::axiom_eqv_transitive(a.mul(b).mul(c), a.mul(c).mul(b), c.mul(a).mul(b));
    //  c*a*b ≡ c*b*a
    lemma_mul_swap_last_two(c, a, b);
    F::axiom_eqv_transitive(a.mul(b).mul(c), c.mul(a).mul(b), c.mul(b).mul(a));
}

//  ===========================================================================
//   Helper 2: neg(x/A) * neg(x/A) ≡ x²/A²
//  ===========================================================================

pub proof fn lemma_neg_div_squared<F: OrderedField>(x: F, big_a: F)
    requires
        !big_a.eqv(F::zero()),
    ensures
        x.div(big_a).neg().mul(x.div(big_a).neg()).eqv(
            x.mul(x).div(big_a.mul(big_a))
        ),
{
    lemma_nonzero_product::<F>(big_a, big_a);
    lemma_neg_mul_neg::<F>(x.div(big_a), x.div(big_a));
    lemma_div_mul_div::<F>(x, big_a, x, big_a);
    F::axiom_eqv_transitive(
        x.div(big_a).neg().mul(x.div(big_a).neg()),
        x.div(big_a).mul(x.div(big_a)),
        x.mul(x).div(big_a.mul(big_a)),
    );
}

pub proof fn lemma_div_squared<F: OrderedField>(x: F, big_a: F)
    requires
        !big_a.eqv(F::zero()),
    ensures
        x.div(big_a).mul(x.div(big_a)).eqv(
            x.mul(x).div(big_a.mul(big_a))
        ),
{
    lemma_nonzero_product::<F>(big_a, big_a);
    lemma_div_mul_div::<F>(x, big_a, x, big_a);
}

//  ===========================================================================
//   Helper 3: Cross-term cancellation (plus case)
//  ===========================================================================

///  dr*di + er*ei ≡ 0 for the plus case.
///  dr = neg(ah/A), di = neg(b)/A, er = neg(bh/A), ei = a/A.
pub proof fn lemma_cl_cross_cancel_plus<F: OrderedField>(
    a: F, b: F, h: F, big_a: F,
)
    requires
        !big_a.eqv(F::zero()),
    ensures ({
        let ah = a.mul(h);
        let bh = b.mul(h);
        let dr = ah.div(big_a).neg();
        let di = b.neg().div(big_a);
        let er = bh.div(big_a).neg();
        let ei = a.div(big_a);
        dr.mul(di).add(er.mul(ei)).eqv(F::zero())
    }),
{
    let ah = a.mul(h);
    let bh = b.mul(h);
    let aa = big_a.mul(big_a);
    let dr = ah.div(big_a).neg();
    let di = b.neg().div(big_a);
    let er = bh.div(big_a).neg();
    let ei = a.div(big_a);

    lemma_nonzero_product::<F>(big_a, big_a);

    //  Bridge: di = b.neg().div(A) ≡ b.div(A).neg()
    lemma_div_neg_numerator::<F>(b, big_a);
    //  dr*di ≡ dr * neg(b/A)  (by congruence on di)
    F::axiom_eqv_reflexive(dr);
    lemma_mul_congruence::<F>(dr, dr, di, b.div(big_a).neg());
    //  neg(ah/A) * neg(b/A) ≡ (ah/A)*(b/A)  (by neg_mul_neg)
    lemma_neg_mul_neg::<F>(ah.div(big_a), b.div(big_a));
    F::axiom_eqv_transitive(
        dr.mul(di), dr.mul(b.div(big_a).neg()), ah.div(big_a).mul(b.div(big_a)),
    );
    //  (ah/A)*(b/A) ≡ ahb/A²
    lemma_div_mul_div::<F>(ah, big_a, b, big_a);
    F::axiom_eqv_transitive(
        dr.mul(di), ah.div(big_a).mul(b.div(big_a)), ah.mul(b).div(aa),
    );

    //  er*ei = neg(bh/A)*(a/A) ≡ neg((bh/A)*(a/A))
    lemma_mul_neg_left::<F>(bh.div(big_a), ei);
    //  (bh/A)*(a/A) ≡ bha/A²
    lemma_div_mul_div::<F>(bh, big_a, a, big_a);
    lemma_neg_congruence::<F>(bh.div(big_a).mul(ei), bh.mul(a).div(aa));
    F::axiom_eqv_transitive(
        er.mul(ei), bh.div(big_a).mul(ei).neg(), bh.mul(a).div(aa).neg(),
    );

    //  ah*b ≡ bh*a (triple reverse: a*h*b ≡ b*h*a)
    lemma_triple_reverse::<F>(a, h, b);
    F::axiom_eqv_reflexive(aa);
    lemma_div_congruence::<F>(ah.mul(b), bh.mul(a), aa, aa);
    //  dr*di ≡ ahb/A² ≡ bha/A²
    F::axiom_eqv_transitive(dr.mul(di), ah.mul(b).div(aa), bh.mul(a).div(aa));

    //  dr*di + er*ei ≡ bha/A² + neg(bha/A²) ≡ 0
    F::axiom_eqv_reflexive(er.mul(ei));
    lemma_add_congruence::<F>(
        dr.mul(di), bh.mul(a).div(aa),
        er.mul(ei), er.mul(ei),
    );
    lemma_add_congruence_right::<F>(
        bh.mul(a).div(aa),
        er.mul(ei), bh.mul(a).div(aa).neg(),
    );
    F::axiom_eqv_transitive(
        dr.mul(di).add(er.mul(ei)),
        bh.mul(a).div(aa).add(er.mul(ei)),
        bh.mul(a).div(aa).add(bh.mul(a).div(aa).neg()),
    );
    F::axiom_add_inverse_right(bh.mul(a).div(aa));
    F::axiom_eqv_transitive(
        dr.mul(di).add(er.mul(ei)),
        bh.mul(a).div(aa).add(bh.mul(a).div(aa).neg()),
        F::zero(),
    );
}

//  ===========================================================================
//   Helper 4: Cross-term cancellation (minus case)
//  ===========================================================================

pub proof fn lemma_cl_cross_cancel_minus<F: OrderedField>(
    a: F, b: F, h: F, big_a: F,
)
    requires
        !big_a.eqv(F::zero()),
    ensures ({
        let ah = a.mul(h);
        let bh = b.mul(h);
        let dr = ah.div(big_a).neg();
        let di = b.div(big_a);
        let er = bh.div(big_a).neg();
        let ei = a.neg().div(big_a);
        dr.mul(di).add(er.mul(ei)).eqv(F::zero())
    }),
{
    let ah = a.mul(h);
    let bh = b.mul(h);
    let aa = big_a.mul(big_a);
    let dr = ah.div(big_a).neg();
    let di = b.div(big_a);
    let er = bh.div(big_a).neg();
    let ei = a.neg().div(big_a);

    lemma_nonzero_product::<F>(big_a, big_a);

    //  dr*di = neg(ah/A)*(b/A) ≡ neg((ah/A)*(b/A)) ≡ neg(ahb/A²)
    lemma_mul_neg_left::<F>(ah.div(big_a), di);
    lemma_div_mul_div::<F>(ah, big_a, b, big_a);
    lemma_neg_congruence::<F>(ah.div(big_a).mul(di), ah.mul(b).div(aa));
    F::axiom_eqv_transitive(
        dr.mul(di), ah.div(big_a).mul(di).neg(), ah.mul(b).div(aa).neg(),
    );

    //  Bridge: ei = a.neg().div(A) ≡ a.div(A).neg()
    lemma_div_neg_numerator::<F>(a, big_a);
    //  er*ei ≡ er * neg(a/A) via congruence
    F::axiom_eqv_reflexive(er);
    lemma_mul_congruence::<F>(er, er, ei, a.div(big_a).neg());
    //  neg(bh/A) * neg(a/A) ≡ (bh/A)*(a/A) via neg_mul_neg
    lemma_neg_mul_neg::<F>(bh.div(big_a), a.div(big_a));
    F::axiom_eqv_transitive(
        er.mul(ei), er.mul(a.div(big_a).neg()), bh.div(big_a).mul(a.div(big_a)),
    );
    //  (bh/A)*(a/A) ≡ bha/A²
    lemma_div_mul_div::<F>(bh, big_a, a, big_a);
    F::axiom_eqv_transitive(
        er.mul(ei), bh.div(big_a).mul(a.div(big_a)), bh.mul(a).div(aa),
    );

    //  ah*b ≡ bh*a by triple reverse
    lemma_triple_reverse::<F>(a, h, b);
    F::axiom_eqv_reflexive(aa);
    lemma_div_congruence::<F>(ah.mul(b), bh.mul(a), aa, aa);
    lemma_neg_congruence::<F>(ah.mul(b).div(aa), bh.mul(a).div(aa));
    //  dr*di ≡ neg(ahb/A²) ≡ neg(bha/A²)
    F::axiom_eqv_transitive(
        dr.mul(di), ah.mul(b).div(aa).neg(), bh.mul(a).div(aa).neg(),
    );

    //  dr*di + er*ei ≡ neg(bha/A²) + bha/A² ≡ 0
    F::axiom_eqv_reflexive(er.mul(ei));
    lemma_add_congruence::<F>(
        dr.mul(di), bh.mul(a).div(aa).neg(),
        er.mul(ei), er.mul(ei),
    );
    lemma_add_congruence_right::<F>(
        bh.mul(a).div(aa).neg(),
        er.mul(ei), bh.mul(a).div(aa),
    );
    F::axiom_eqv_transitive(
        dr.mul(di).add(er.mul(ei)),
        bh.mul(a).div(aa).neg().add(er.mul(ei)),
        bh.mul(a).div(aa).neg().add(bh.mul(a).div(aa)),
    );
    lemma_add_inverse_left::<F>(bh.mul(a).div(aa));
    F::axiom_eqv_transitive(
        dr.mul(di).add(er.mul(ei)),
        bh.mul(a).div(aa).neg().add(bh.mul(a).div(aa)),
        F::zero(),
    );
}

//  ===========================================================================
//   Helper 5: Full imaginary = 0 from cross-cancel
//  ===========================================================================

pub proof fn lemma_cl_full_im_zero<F: OrderedField>(
    dr: F, di: F, er: F, ei: F,
)
    requires
        dr.mul(di).add(er.mul(ei)).eqv(F::zero()),
    ensures
        dr.mul(di).add(di.mul(dr)).add(er.mul(ei).add(ei.mul(er))).eqv(F::zero()),
{
    //  di*dr ≡ dr*di, ei*er ≡ er*ei
    F::axiom_mul_commutative(di, dr);
    F::axiom_mul_commutative(ei, er);

    //  di*dr + ei*er ≡ dr*di + er*ei ≡ 0
    lemma_add_congruence::<F>(di.mul(dr), dr.mul(di), ei.mul(er), er.mul(ei));
    F::axiom_eqv_transitive(
        di.mul(dr).add(ei.mul(er)),
        dr.mul(di).add(er.mul(ei)),
        F::zero(),
    );

    //  Rearrange: (dr*di + di*dr) + (er*ei + ei*er)
    //    ≡ (dr*di + er*ei) + (di*dr + ei*er)
    lemma_add_rearrange_2x2::<F>(dr.mul(di), di.mul(dr), er.mul(ei), ei.mul(er));

    //  Both halves ≡ 0, so 0 + 0 ≡ 0
    lemma_add_congruence::<F>(
        dr.mul(di).add(er.mul(ei)), F::zero(),
        di.mul(dr).add(ei.mul(er)), F::zero(),
    );
    F::axiom_add_zero_right(F::zero());
    F::axiom_eqv_transitive(
        dr.mul(di).add(er.mul(ei)).add(di.mul(dr).add(ei.mul(er))),
        F::zero().add(F::zero()),
        F::zero(),
    );
    //  Chain from rearranged to 0
    F::axiom_eqv_transitive(
        dr.mul(di).add(di.mul(dr)).add(er.mul(ei).add(ei.mul(er))),
        dr.mul(di).add(er.mul(ei)).add(di.mul(dr).add(ei.mul(er))),
        F::zero(),
    );
}

//  ===========================================================================
//   Helper 6: di², ei² ≡ b²/A², a²/A² regardless of ± sign
//  ===========================================================================

pub proof fn lemma_cl_sq_components_plus<F: OrderedField>(
    a: F, b: F, big_a: F,
)
    requires
        !big_a.eqv(F::zero()),
    ensures
        b.neg().div(big_a).mul(b.neg().div(big_a)).eqv(
            b.mul(b).div(big_a.mul(big_a))
        ),
        a.div(big_a).mul(a.div(big_a)).eqv(
            a.mul(a).div(big_a.mul(big_a))
        ),
{
    //  ix = neg(b)/A ≡ neg(b/A) by div_neg_numerator
    lemma_div_neg_numerator::<F>(b, big_a);
    //  ix*ix ≡ neg(b/A)*neg(b/A) ≡ b²/A²
    lemma_mul_congruence::<F>(
        b.neg().div(big_a), b.div(big_a).neg(),
        b.neg().div(big_a), b.div(big_a).neg(),
    );
    lemma_neg_div_squared::<F>(b, big_a);
    F::axiom_eqv_transitive(
        b.neg().div(big_a).mul(b.neg().div(big_a)),
        b.div(big_a).neg().mul(b.div(big_a).neg()),
        b.mul(b).div(big_a.mul(big_a)),
    );
    //  iy = a/A, iy² = (a/A)² ≡ a²/A²
    lemma_div_squared::<F>(a, big_a);
}

pub proof fn lemma_cl_sq_components_minus<F: OrderedField>(
    a: F, b: F, big_a: F,
)
    requires
        !big_a.eqv(F::zero()),
    ensures
        b.div(big_a).mul(b.div(big_a)).eqv(
            b.mul(b).div(big_a.mul(big_a))
        ),
        a.neg().div(big_a).mul(a.neg().div(big_a)).eqv(
            a.mul(a).div(big_a.mul(big_a))
        ),
{
    //  ix = b/A, ix² ≡ b²/A²
    lemma_div_squared::<F>(b, big_a);
    //  iy = neg(a)/A ≡ neg(a/A), iy² ≡ a²/A²
    lemma_div_neg_numerator::<F>(a, big_a);
    lemma_mul_congruence::<F>(
        a.neg().div(big_a), a.div(big_a).neg(),
        a.neg().div(big_a), a.div(big_a).neg(),
    );
    lemma_neg_div_squared::<F>(a, big_a);
    F::axiom_eqv_transitive(
        a.neg().div(big_a).mul(a.neg().div(big_a)),
        a.div(big_a).neg().mul(a.div(big_a).neg()),
        a.mul(a).div(big_a.mul(big_a)),
    );
}

//  ===========================================================================
//   Helper 7: Real part = rsq
//  ===========================================================================

///  The real part of sq_dist equals rsq.
///  All four squared terms are expressed as fractions over A², combined, and simplified.
pub proof fn lemma_cl_re_eq_rsq<F: OrderedField>(
    a: F, b: F, h: F, big_a: F, rsq: F,
)
    requires
        !big_a.eqv(F::zero()),
        big_a.eqv(a.mul(a).add(b.mul(b))),
    ensures ({
        let aa = big_a.mul(big_a);
        let disc = big_a.mul(rsq).sub(h.mul(h));
        let dr_sq = a.mul(h).mul(a.mul(h)).div(aa);
        let er_sq = b.mul(h).mul(b.mul(h)).div(aa);
        let di_sq = b.mul(b).div(aa);
        let ei_sq = a.mul(a).div(aa);
        dr_sq.add(di_sq.mul(disc)).add(er_sq.add(ei_sq.mul(disc))).eqv(rsq)
    }),
{
    let aa = big_a.mul(big_a);
    let disc = big_a.mul(rsq).sub(h.mul(h));
    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let h2 = h.mul(h);
    let dr_sq = a.mul(h).mul(a.mul(h)).div(aa);
    let er_sq = b.mul(h).mul(b.mul(h)).div(aa);
    let di_sq = b2.div(aa);
    let ei_sq = a2.div(aa);

    lemma_nonzero_product::<F>(big_a, big_a);

    //  === Step 1: (ah)² ≡ a²h² and (bh)² ≡ b²h² ===
    lemma_square_product::<F>(a, h);
    F::axiom_eqv_reflexive(aa);
    lemma_div_congruence::<F>(a.mul(h).mul(a.mul(h)), a2.mul(h2), aa, aa);

    lemma_square_product::<F>(b, h);
    lemma_div_congruence::<F>(b.mul(h).mul(b.mul(h)), b2.mul(h2), aa, aa);

    //  === Step 2: di_sq*D ≡ b²D/A² and ei_sq*D ≡ a²D/A² ===
    //  (b²/A²)*D ≡ D*(b²/A²) ≡ D*b²/A² ≡ b²*D/A²
    F::axiom_mul_commutative(di_sq, disc);
    lemma_mul_div_assoc::<F>(disc, b2, aa);
    F::axiom_eqv_transitive(di_sq.mul(disc), disc.mul(di_sq), disc.mul(b2).div(aa));
    F::axiom_mul_commutative(disc, b2);
    lemma_div_congruence::<F>(disc.mul(b2), b2.mul(disc), aa, aa);
    F::axiom_eqv_transitive(di_sq.mul(disc), disc.mul(b2).div(aa), b2.mul(disc).div(aa));

    //  Same for ei_sq*D
    F::axiom_mul_commutative(ei_sq, disc);
    lemma_mul_div_assoc::<F>(disc, a2, aa);
    F::axiom_eqv_transitive(ei_sq.mul(disc), disc.mul(ei_sq), disc.mul(a2).div(aa));
    F::axiom_mul_commutative(disc, a2);
    lemma_div_congruence::<F>(disc.mul(a2), a2.mul(disc), aa, aa);
    F::axiom_eqv_transitive(ei_sq.mul(disc), disc.mul(a2).div(aa), a2.mul(disc).div(aa));

    //  === Step 3: Combine four fractions ===
    lemma_add_congruence::<F>(
        dr_sq, a2.mul(h2).div(aa),
        di_sq.mul(disc), b2.mul(disc).div(aa),
    );
    lemma_add_congruence::<F>(
        er_sq, b2.mul(h2).div(aa),
        ei_sq.mul(disc), a2.mul(disc).div(aa),
    );
    lemma_add_congruence::<F>(
        dr_sq.add(di_sq.mul(disc)), a2.mul(h2).div(aa).add(b2.mul(disc).div(aa)),
        er_sq.add(ei_sq.mul(disc)), b2.mul(h2).div(aa).add(a2.mul(disc).div(aa)),
    );
    lemma_four_div_same_denom::<F>(a2.mul(h2), b2.mul(disc), b2.mul(h2), a2.mul(disc), aa);
    F::axiom_eqv_transitive(
        dr_sq.add(di_sq.mul(disc)).add(er_sq.add(ei_sq.mul(disc))),
        a2.mul(h2).div(aa).add(b2.mul(disc).div(aa)).add(
            b2.mul(h2).div(aa).add(a2.mul(disc).div(aa))
        ),
        a2.mul(h2).add(b2.mul(disc)).add(b2.mul(h2).add(a2.mul(disc))).div(aa),
    );

    //  === Step 4: Rearrange numerator ===
    //  (a²h² + b²D) + (b²h² + a²D) ≡ (a²h² + b²h²) + (b²D + a²D)
    lemma_add_rearrange_2x2::<F>(a2.mul(h2), b2.mul(disc), b2.mul(h2), a2.mul(disc));
    lemma_div_congruence::<F>(
        a2.mul(h2).add(b2.mul(disc)).add(b2.mul(h2).add(a2.mul(disc))),
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))),
        aa, aa,
    );
    F::axiom_eqv_transitive(
        dr_sq.add(di_sq.mul(disc)).add(er_sq.add(ei_sq.mul(disc))),
        a2.mul(h2).add(b2.mul(disc)).add(b2.mul(h2).add(a2.mul(disc))).div(aa),
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))).div(aa),
    );

    //  === Step 5: Factor (a²+b²)*h² and (b²+a²)*D ===
    //  big_a ≡ a²+b² (from requires)
    F::axiom_eqv_symmetric(big_a, a2.add(b2));
    //  a²+b² ≡ big_a

    //  (a²h² + b²h²) = (a²+b²)*h² ≡ A*h²
    lemma_mul_distributes_right::<F>(a2, b2, h2);
    F::axiom_eqv_symmetric(a2.add(b2).mul(h2), a2.mul(h2).add(b2.mul(h2)));
    //  a2.add(b2) ≡ big_a, so (a²+b²)*h² ≡ A*h²
    F::axiom_eqv_reflexive(h2);
    lemma_mul_congruence::<F>(a2.add(b2), big_a, h2, h2);
    F::axiom_eqv_transitive(
        a2.mul(h2).add(b2.mul(h2)),
        a2.add(b2).mul(h2),
        big_a.mul(h2),
    );

    //  (b²D + a²D) = (b²+a²)*D ≡ A*D
    lemma_mul_distributes_right::<F>(b2, a2, disc);
    F::axiom_eqv_symmetric(b2.add(a2).mul(disc), b2.mul(disc).add(a2.mul(disc)));
    //  b²+a² ≡ a²+b² ≡ big_a
    F::axiom_add_commutative(b2, a2);
    F::axiom_eqv_transitive(b2.add(a2), a2.add(b2), big_a);
    F::axiom_eqv_reflexive(disc);
    lemma_mul_congruence::<F>(b2.add(a2), big_a, disc, disc);
    F::axiom_eqv_transitive(
        b2.mul(disc).add(a2.mul(disc)),
        b2.add(a2).mul(disc),
        big_a.mul(disc),
    );

    //  Combine: A*h² + A*D
    lemma_add_congruence::<F>(
        a2.mul(h2).add(b2.mul(h2)), big_a.mul(h2),
        b2.mul(disc).add(a2.mul(disc)), big_a.mul(disc),
    );

    //  === Step 6: A*h² + A*D = A*(h²+D) ===
    F::axiom_mul_distributes_left(big_a, h2, disc);
    F::axiom_eqv_symmetric(big_a.mul(h2.add(disc)), big_a.mul(h2).add(big_a.mul(disc)));
    F::axiom_eqv_transitive(
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))),
        big_a.mul(h2).add(big_a.mul(disc)),
        big_a.mul(h2.add(disc)),
    );

    //  === Step 7: h²+D = A*rsq ===
    //  D = A*rsq - h², so h² + D = h² + (A*rsq - h²) = A*rsq
    F::axiom_add_commutative(h2, disc);
    lemma_sub_then_add_cancel::<F>(big_a.mul(rsq), h2);
    F::axiom_eqv_transitive(h2.add(disc), disc.add(h2), big_a.mul(rsq));

    //  A*(h²+D) ≡ A*(A*rsq) ≡ A²*rsq
    lemma_mul_congruence_right::<F>(big_a, h2.add(disc), big_a.mul(rsq));
    F::axiom_mul_associative(big_a, big_a, rsq);
    F::axiom_eqv_symmetric(aa.mul(rsq), big_a.mul(big_a.mul(rsq)));
    F::axiom_eqv_transitive(
        big_a.mul(h2.add(disc)), big_a.mul(big_a.mul(rsq)), aa.mul(rsq),
    );

    //  === Step 8: Chain numerator to A²*rsq ===
    F::axiom_eqv_transitive(
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))),
        big_a.mul(h2.add(disc)),
        aa.mul(rsq),
    );

    //  === Step 9: numerator/A² = A²*rsq/A² ≡ rsq ===
    lemma_div_congruence::<F>(
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))),
        aa.mul(rsq),
        aa, aa,
    );
    //  aa*rsq ≡ rsq*aa by commutativity
    F::axiom_mul_commutative(aa, rsq);
    lemma_div_congruence::<F>(aa.mul(rsq), rsq.mul(aa), aa, aa);
    //  rsq*aa / aa ≡ rsq by mul_div_cancel
    lemma_mul_div_cancel::<F>(rsq, aa);
    //  Chain: num/A² ≡ aa*rsq/A² ≡ rsq*aa/A² ≡ rsq
    F::axiom_eqv_transitive(
        aa.mul(rsq).div(aa), rsq.mul(aa).div(aa), rsq,
    );
    F::axiom_eqv_transitive(
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))).div(aa),
        aa.mul(rsq).div(aa),
        rsq,
    );

    //  Final chain
    F::axiom_eqv_transitive(
        dr_sq.add(di_sq.mul(disc)).add(er_sq.add(ei_sq.mul(disc))),
        a2.mul(h2).add(b2.mul(h2)).add(b2.mul(disc).add(a2.mul(disc))).div(aa),
        rsq,
    );
}

//  ===========================================================================
//   Helper 8: Real part bridge (replaces abstract D with disc, then uses re_eq_rsq)
//  ===========================================================================

///  Proves the real part identity with an abstract D (like R::value()).
pub proof fn lemma_cl_re_with_d<F: OrderedField>(
    a: F, b: F, h: F, big_a: F, rsq: F, d: F, plus: bool,
)
    requires
        !big_a.eqv(F::zero()),
        big_a.eqv(a.mul(a).add(b.mul(b))),
        d.eqv(big_a.mul(rsq).sub(h.mul(h))),
    ensures ({
        let dr = a.mul(h).div(big_a).neg();
        let er = b.mul(h).div(big_a).neg();
        let (di, ei) = if plus {
            (b.neg().div(big_a), a.div(big_a))
        } else {
            (b.div(big_a), a.neg().div(big_a))
        };
        dr.mul(dr).add(di.mul(di).mul(d)).add(
            er.mul(er).add(ei.mul(ei).mul(d))
        ).eqv(rsq)
    }),
{
    let disc = big_a.mul(rsq).sub(h.mul(h));
    let aa = big_a.mul(big_a);
    let dr = a.mul(h).div(big_a).neg();
    let er = b.mul(h).div(big_a).neg();
    let (di, ei) = if plus {
        (b.neg().div(big_a), a.div(big_a))
    } else {
        (b.div(big_a), a.neg().div(big_a))
    };

    lemma_nonzero_product::<F>(big_a, big_a);

    //  Replace d with disc via congruence (d ≡ disc from requires)
    lemma_mul_congruence_right::<F>(di.mul(di), d, disc);
    lemma_mul_congruence_right::<F>(ei.mul(ei), d, disc);

    F::axiom_eqv_reflexive(dr.mul(dr));
    lemma_add_congruence::<F>(
        dr.mul(dr), dr.mul(dr),
        di.mul(di).mul(d), di.mul(di).mul(disc),
    );
    F::axiom_eqv_reflexive(er.mul(er));
    lemma_add_congruence::<F>(
        er.mul(er), er.mul(er),
        ei.mul(ei).mul(d), ei.mul(ei).mul(disc),
    );
    lemma_add_congruence::<F>(
        dr.mul(dr).add(di.mul(di).mul(d)),
        dr.mul(dr).add(di.mul(di).mul(disc)),
        er.mul(er).add(ei.mul(ei).mul(d)),
        er.mul(er).add(ei.mul(ei).mul(disc)),
    );
    //  sum_with_d ≡ sum_with_disc

    //  Replace dr², di², er², ei² with fraction forms
    lemma_neg_div_squared(a.mul(h), big_a);
    lemma_neg_div_squared(b.mul(h), big_a);
    if plus {
        lemma_cl_sq_components_plus(a, b, big_a);
    } else {
        lemma_cl_sq_components_minus(a, b, big_a);
    }

    //  di²*disc ≡ (b²/A²)*disc, ei²*disc ≡ (a²/A²)*disc
    F::axiom_eqv_reflexive(disc);
    lemma_mul_congruence::<F>(di.mul(di), b.mul(b).div(aa), disc, disc);
    lemma_mul_congruence::<F>(ei.mul(ei), a.mul(a).div(aa), disc, disc);

    //  Build fraction form
    lemma_add_congruence::<F>(
        dr.mul(dr), a.mul(h).mul(a.mul(h)).div(aa),
        di.mul(di).mul(disc), b.mul(b).div(aa).mul(disc),
    );
    lemma_add_congruence::<F>(
        er.mul(er), b.mul(h).mul(b.mul(h)).div(aa),
        ei.mul(ei).mul(disc), a.mul(a).div(aa).mul(disc),
    );
    lemma_add_congruence::<F>(
        dr.mul(dr).add(di.mul(di).mul(disc)),
        a.mul(h).mul(a.mul(h)).div(aa).add(b.mul(b).div(aa).mul(disc)),
        er.mul(er).add(ei.mul(ei).mul(disc)),
        b.mul(h).mul(b.mul(h)).div(aa).add(a.mul(a).div(aa).mul(disc)),
    );

    //  Apply re_eq_rsq
    lemma_cl_re_eq_rsq(a, b, h, big_a, rsq);

    //  Chain: sum_with_disc ≡ fraction_form ≡ rsq
    F::axiom_eqv_transitive(
        dr.mul(dr).add(di.mul(di).mul(disc)).add(
            er.mul(er).add(ei.mul(ei).mul(disc))
        ),
        a.mul(h).mul(a.mul(h)).div(aa).add(b.mul(b).div(aa).mul(disc)).add(
            b.mul(h).mul(b.mul(h)).div(aa).add(a.mul(a).div(aa).mul(disc))
        ),
        rsq,
    );
    //  Chain: sum_with_d ≡ sum_with_disc ≡ rsq
    F::axiom_eqv_transitive(
        dr.mul(dr).add(di.mul(di).mul(d)).add(
            er.mul(er).add(ei.mul(ei).mul(d))
        ),
        dr.mul(dr).add(di.mul(di).mul(disc)).add(
            er.mul(er).add(ei.mul(ei).mul(disc))
        ),
        rsq,
    );
}

} //  verus!
