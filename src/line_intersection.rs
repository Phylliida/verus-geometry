use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::field_lemmas::*;
use crate::line2::*;
use crate::point2::*;

verus! {

//  ===========================================================================
//   Line-line intersection via Cramer's rule
//  ===========================================================================

///  Determinant of the normal vectors: a1*b2 - a2*b1.
///  Non-zero iff the lines are not parallel.
pub open spec fn line_det<T: Ring>(l1: Line2<T>, l2: Line2<T>) -> T {
    l1.a.mul(l2.b).sub(l1.b.mul(l2.a))
}

///  Intersection point of two non-parallel lines via Cramer's rule:
///    x = (b1*c2 - b2*c1) / det
///    y = (a2*c1 - a1*c2) / det
pub open spec fn line_line_intersection_2d<F: OrderedField>(
    l1: Line2<F>, l2: Line2<F>,
) -> Point2<F> {
    let det = line_det(l1, l2);
    Point2 {
        x: l1.b.mul(l2.c).sub(l2.b.mul(l1.c)).div(det),
        y: l2.a.mul(l1.c).sub(l1.a.mul(l2.c)).div(det),
    }
}

//  ===========================================================================
//   Helper: a * (b / c) ≡ (a*b) / c
//  ===========================================================================

pub proof fn lemma_mul_div_assoc<F: OrderedField>(a: F, b: F, c: F)
    requires
        !c.eqv(F::zero()),
    ensures
        a.mul(b.div(c)).eqv(a.mul(b).div(c)),
{
    //  b/c ≡ b * recip(c)
    F::axiom_div_is_mul_recip(b, c);
    lemma_mul_congruence_right::<F>(a, b.div(c), b.mul(c.recip()));
    //  a * (b * recip(c)) ≡ (a*b) * recip(c)
    F::axiom_mul_associative(a, b, c.recip());
    F::axiom_eqv_symmetric(a.mul(b).mul(c.recip()), a.mul(b.mul(c.recip())));
    F::axiom_eqv_transitive(a.mul(b.div(c)), a.mul(b.mul(c.recip())), a.mul(b).mul(c.recip()));
    //  (a*b) * recip(c) ≡ (a*b) / c
    F::axiom_div_is_mul_recip(a.mul(b), c);
    F::axiom_eqv_symmetric(a.mul(b).div(c), a.mul(b).mul(c.recip()));
    F::axiom_eqv_transitive(a.mul(b.div(c)), a.mul(b).mul(c.recip()), a.mul(b).div(c));
}

//  ===========================================================================
//   Numerator identity helpers
//  ===========================================================================

///  The key ring identity for l1: a1*x_num + b1*y_num + c1*det ≡ 0.
///
///  After distributing and applying commutativity, the 6 terms form three
///  cancelling pairs via the telescoping identity (α-β)+(β-γ)+(γ-α) = 0.
proof fn lemma_ll_numerator_l1<T: Ring>(
    a1: T, b1: T, c1: T, a2: T, b2: T, c2: T,
)
    ensures ({
        let x_num = b1.mul(c2).sub(b2.mul(c1));
        let y_num = a2.mul(c1).sub(a1.mul(c2));
        let det = a1.mul(b2).sub(a2.mul(b1));
        a1.mul(x_num).add(b1.mul(y_num)).add(c1.mul(det)).eqv(T::zero())
    }),
{
    let x_num = b1.mul(c2).sub(b2.mul(c1));
    let y_num = a2.mul(c1).sub(a1.mul(c2));
    let det = a1.mul(b2).sub(a2.mul(b1));

    //  Distribute each outer mul over sub:
    lemma_mul_distributes_over_sub::<T>(a1, b1.mul(c2), b2.mul(c1));
    //  a1*x_num ≡ a1*(b1*c2) - a1*(b2*c1)
    lemma_mul_distributes_over_sub::<T>(b1, a2.mul(c1), a1.mul(c2));
    //  b1*y_num ≡ b1*(a2*c1) - b1*(a1*c2)
    lemma_mul_distributes_over_sub::<T>(c1, a1.mul(b2), a2.mul(b1));
    //  c1*det   ≡ c1*(a1*b2) - c1*(a2*b1)

    //  Now identify α, β, γ for telescoping.
    //  We need commutativity to show these match:
    //    α = b1*(a1*c2): from a1*(b1*c2) ≡ α by assoc+comm
    //    β = c1*(a1*b2): from a1*(b2*c1) ≡ β by assoc+comm
    //    γ = c1*(a2*b1): from b1*(a2*c1) ≡ γ by assoc+comm

    let alpha = b1.mul(a1.mul(c2));
    let beta = c1.mul(a1.mul(b2));
    let gamma = c1.mul(a2.mul(b1));

    //  a1*(b1*c2) ≡ α = b1*(a1*c2)
    T::axiom_mul_associative(a1, b1, c2);
    T::axiom_eqv_symmetric(a1.mul(b1).mul(c2), a1.mul(b1.mul(c2)));
    T::axiom_mul_commutative(a1, b1);
    T::axiom_mul_congruence_left(a1.mul(b1), b1.mul(a1), c2);
    T::axiom_mul_associative(b1, a1, c2);
    T::axiom_eqv_transitive(a1.mul(b1).mul(c2), b1.mul(a1).mul(c2), alpha);
    T::axiom_eqv_transitive(a1.mul(b1.mul(c2)), a1.mul(b1).mul(c2), alpha);

    //  a1*(b2*c1) ≡ β = c1*(a1*b2)
    T::axiom_mul_associative(a1, b2, c1);
    T::axiom_eqv_symmetric(a1.mul(b2).mul(c1), a1.mul(b2.mul(c1)));
    T::axiom_mul_commutative(a1.mul(b2), c1);
    T::axiom_eqv_transitive(a1.mul(b2.mul(c1)), a1.mul(b2).mul(c1), beta);

    //  b1*(a2*c1) ≡ γ = c1*(a2*b1)
    T::axiom_mul_associative(b1, a2, c1);
    T::axiom_eqv_symmetric(b1.mul(a2).mul(c1), b1.mul(a2.mul(c1)));
    T::axiom_mul_commutative(b1, a2);
    T::axiom_mul_congruence_left(b1.mul(a2), a2.mul(b1), c1);
    T::axiom_mul_commutative(a2.mul(b1), c1);
    T::axiom_eqv_transitive(b1.mul(a2).mul(c1), a2.mul(b1).mul(c1), gamma);
    T::axiom_eqv_transitive(b1.mul(a2.mul(c1)), b1.mul(a2).mul(c1), gamma);

    //  b1*(a1*c2) is already alpha (definitional)
    T::axiom_eqv_reflexive(alpha);
    //  c1*(a1*b2) is already beta (definitional)
    T::axiom_eqv_reflexive(beta);
    //  c1*(a2*b1) is already gamma (definitional)
    T::axiom_eqv_reflexive(gamma);

    //  Now apply sub_congruence to get:
    //  a1*x_num ≡ α - β
    lemma_sub_congruence::<T>(a1.mul(b1.mul(c2)), alpha, a1.mul(b2.mul(c1)), beta);
    T::axiom_eqv_transitive(a1.mul(x_num), a1.mul(b1.mul(c2)).sub(a1.mul(b2.mul(c1))), alpha.sub(beta));

    //  b1*y_num ≡ γ - α
    lemma_sub_congruence::<T>(b1.mul(a2.mul(c1)), gamma, b1.mul(a1.mul(c2)), alpha);
    T::axiom_eqv_transitive(b1.mul(y_num), b1.mul(a2.mul(c1)).sub(b1.mul(a1.mul(c2))), gamma.sub(alpha));

    //  c1*det ≡ β - γ
    lemma_sub_congruence::<T>(c1.mul(a1.mul(b2)), beta, c1.mul(a2.mul(b1)), gamma);
    T::axiom_eqv_transitive(c1.mul(det), c1.mul(a1.mul(b2)).sub(c1.mul(a2.mul(b1))), beta.sub(gamma));

    //  Telescope: (α-β) + (γ-α) + (β-γ) ≡ 0
    //  Reorder to use lemma_sub_telescope_triple(α, β, γ) which gives (α-β)+(β-γ)+(γ-α)=0
    //  We have (α-β) + (γ-α) + (β-γ), need to reorder the last two.

    //  First: a1*x_num + b1*y_num ≡ (α-β) + (γ-α)
    lemma_add_congruence::<T>(a1.mul(x_num), alpha.sub(beta), b1.mul(y_num), gamma.sub(alpha));

    //  (α-β) + (γ-α) ≡ γ-β  by lemma_sub_add_sub(α, β, ...) wait, wrong order
    //  Actually: (x-y) + (z-x) → use sub_add_sub reordered.
    //  lemma_sub_add_sub(γ, α, β) gives (γ-α)+(α-β) ≡ γ-β
    //  We have (α-β)+(γ-α). By commutativity of add:
    T::axiom_add_commutative(alpha.sub(beta), gamma.sub(alpha));
    lemma_sub_add_sub::<T>(gamma, alpha, beta);
    T::axiom_eqv_transitive(
        alpha.sub(beta).add(gamma.sub(alpha)),
        gamma.sub(alpha).add(alpha.sub(beta)),
        gamma.sub(beta),
    );

    //  a1*x_num + b1*y_num ≡ γ - β
    T::axiom_eqv_transitive(
        a1.mul(x_num).add(b1.mul(y_num)),
        alpha.sub(beta).add(gamma.sub(alpha)),
        gamma.sub(beta),
    );

    //  (a1*x_num + b1*y_num) + c1*det ≡ (γ-β) + (β-γ)
    lemma_add_congruence::<T>(
        a1.mul(x_num).add(b1.mul(y_num)), gamma.sub(beta),
        c1.mul(det), beta.sub(gamma),
    );

    //  (γ-β) + (β-γ) ≡ 0 by sub + neg_sub + inverse
    lemma_neg_sub::<T>(gamma, beta);
    //  -(γ-β) ≡ β-γ, so β-γ ≡ -(γ-β)
    T::axiom_eqv_symmetric(gamma.sub(beta).neg(), beta.sub(gamma));
    lemma_add_congruence_right::<T>(gamma.sub(beta), beta.sub(gamma), gamma.sub(beta).neg());
    T::axiom_add_inverse_right(gamma.sub(beta));
    T::axiom_eqv_transitive(
        gamma.sub(beta).add(beta.sub(gamma)),
        gamma.sub(beta).add(gamma.sub(beta).neg()),
        T::zero(),
    );

    //  Final chain
    T::axiom_eqv_transitive(
        a1.mul(x_num).add(b1.mul(y_num)).add(c1.mul(det)),
        gamma.sub(beta).add(beta.sub(gamma)),
        T::zero(),
    );
}

///  Same identity for l2: a2*x_num + b2*y_num + c2*det ≡ 0.
proof fn lemma_ll_numerator_l2<T: Ring>(
    a1: T, b1: T, c1: T, a2: T, b2: T, c2: T,
)
    ensures ({
        let x_num = b1.mul(c2).sub(b2.mul(c1));
        let y_num = a2.mul(c1).sub(a1.mul(c2));
        let det = a1.mul(b2).sub(a2.mul(b1));
        a2.mul(x_num).add(b2.mul(y_num)).add(c2.mul(det)).eqv(T::zero())
    }),
{
    let x_num = b1.mul(c2).sub(b2.mul(c1));
    let y_num = a2.mul(c1).sub(a1.mul(c2));
    let det = a1.mul(b2).sub(a2.mul(b1));

    //  Distribute
    lemma_mul_distributes_over_sub::<T>(a2, b1.mul(c2), b2.mul(c1));
    lemma_mul_distributes_over_sub::<T>(b2, a2.mul(c1), a1.mul(c2));
    lemma_mul_distributes_over_sub::<T>(c2, a1.mul(b2), a2.mul(b1));

    //  Commutativity identities for telescoping with α, β, γ:
    //    α = c2*(a2*b1): a2*(b1*c2) ≡ α via assoc+comm
    //    β = b2*(a2*c1): a2*(b2*c1) ≡ β via assoc+comm
    //    γ = b2*(a1*c2): from c2*(a1*b2) ≡ γ via assoc+comm

    let alpha = c2.mul(a2.mul(b1));
    let beta = b2.mul(a2.mul(c1));
    let gamma = b2.mul(a1.mul(c2));

    //  a2*(b1*c2) ≡ α = c2*(a2*b1)
    T::axiom_mul_associative(a2, b1, c2);
    T::axiom_eqv_symmetric(a2.mul(b1).mul(c2), a2.mul(b1.mul(c2)));
    T::axiom_mul_commutative(a2.mul(b1), c2);
    T::axiom_eqv_transitive(a2.mul(b1.mul(c2)), a2.mul(b1).mul(c2), alpha);

    //  a2*(b2*c1) ≡ β = b2*(a2*c1)
    T::axiom_mul_associative(a2, b2, c1);
    T::axiom_eqv_symmetric(a2.mul(b2).mul(c1), a2.mul(b2.mul(c1)));
    T::axiom_mul_commutative(a2, b2);
    T::axiom_mul_congruence_left(a2.mul(b2), b2.mul(a2), c1);
    T::axiom_mul_associative(b2, a2, c1);
    T::axiom_eqv_transitive(a2.mul(b2).mul(c1), b2.mul(a2).mul(c1), beta);
    T::axiom_eqv_transitive(a2.mul(b2.mul(c1)), a2.mul(b2).mul(c1), beta);

    //  b2*(a1*c2) is already γ (definitional)
    T::axiom_eqv_reflexive(gamma);

    //  c2*(a1*b2) ≡ γ = b2*(a1*c2)
    T::axiom_mul_associative(c2, a1, b2);
    T::axiom_eqv_symmetric(c2.mul(a1).mul(b2), c2.mul(a1.mul(b2)));
    T::axiom_mul_commutative(c2, a1);
    T::axiom_mul_congruence_left(c2.mul(a1), a1.mul(c2), b2);
    T::axiom_mul_commutative(a1.mul(c2), b2);
    T::axiom_eqv_transitive(c2.mul(a1).mul(b2), a1.mul(c2).mul(b2), gamma);
    T::axiom_eqv_transitive(c2.mul(a1.mul(b2)), c2.mul(a1).mul(b2), gamma);

    //  c2*(a2*b1) is already α (definitional)
    T::axiom_eqv_reflexive(alpha);

    //  a2*x_num ≡ α - β
    lemma_sub_congruence::<T>(a2.mul(b1.mul(c2)), alpha, a2.mul(b2.mul(c1)), beta);
    T::axiom_eqv_transitive(a2.mul(x_num), a2.mul(b1.mul(c2)).sub(a2.mul(b2.mul(c1))), alpha.sub(beta));

    //  b2*y_num ≡ β - γ
    T::axiom_eqv_reflexive(beta);
    lemma_sub_congruence::<T>(b2.mul(a2.mul(c1)), beta, b2.mul(a1.mul(c2)), gamma);
    T::axiom_eqv_transitive(b2.mul(y_num), b2.mul(a2.mul(c1)).sub(b2.mul(a1.mul(c2))), beta.sub(gamma));

    //  c2*det ≡ γ - α
    lemma_sub_congruence::<T>(c2.mul(a1.mul(b2)), gamma, c2.mul(a2.mul(b1)), alpha);
    T::axiom_eqv_transitive(c2.mul(det), c2.mul(a1.mul(b2)).sub(c2.mul(a2.mul(b1))), gamma.sub(alpha));

    //  Telescope: (α-β) + (β-γ) + (γ-α) ≡ 0
    lemma_sub_telescope_triple::<T>(alpha, beta, gamma);

    //  a2*x_num + b2*y_num ≡ (α-β) + (β-γ) ≡ α-γ
    lemma_add_congruence::<T>(a2.mul(x_num), alpha.sub(beta), b2.mul(y_num), beta.sub(gamma));
    lemma_sub_add_sub::<T>(alpha, beta, gamma);
    T::axiom_eqv_transitive(
        a2.mul(x_num).add(b2.mul(y_num)),
        alpha.sub(beta).add(beta.sub(gamma)),
        alpha.sub(gamma),
    );

    //  + c2*det ≡ (α-γ) + (γ-α) ≡ 0
    lemma_add_congruence::<T>(
        a2.mul(x_num).add(b2.mul(y_num)), alpha.sub(gamma),
        c2.mul(det), gamma.sub(alpha),
    );
    lemma_neg_sub::<T>(alpha, gamma);
    T::axiom_eqv_symmetric(alpha.sub(gamma).neg(), gamma.sub(alpha));
    lemma_add_congruence_right::<T>(alpha.sub(gamma), gamma.sub(alpha), alpha.sub(gamma).neg());
    T::axiom_add_inverse_right(alpha.sub(gamma));
    T::axiom_eqv_transitive(
        alpha.sub(gamma).add(gamma.sub(alpha)),
        alpha.sub(gamma).add(alpha.sub(gamma).neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        a2.mul(x_num).add(b2.mul(y_num)).add(c2.mul(det)),
        alpha.sub(gamma).add(gamma.sub(alpha)),
        T::zero(),
    );
}

//  ===========================================================================
//   Helper: from numerator identity to line eval = 0
//  ===========================================================================

///  Common proof structure: given a*x_num + b*y_num + c*det ≡ 0 and det ≠ 0,
///  show a*(x_num/det) + b*(y_num/det) + c ≡ 0.
pub proof fn lemma_ll_eval_from_numerator<F: OrderedField>(
    a_coef: F, b_coef: F, c_coef: F, x_num: F, y_num: F, det: F,
)
    requires
        !det.eqv(F::zero()),
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det)).eqv(F::zero()),
    ensures
        a_coef.mul(x_num.div(det)).add(b_coef.mul(y_num.div(det))).add(c_coef).eqv(F::zero()),
{
    //  a*(x_num/det) ≡ (a*x_num)/det
    lemma_mul_div_assoc::<F>(a_coef, x_num, det);
    //  b*(y_num/det) ≡ (b*y_num)/det
    lemma_mul_div_assoc::<F>(b_coef, y_num, det);

    //  sum of first two terms: (a*x_num)/det + (b*y_num)/det ≡ (a*x_num + b*y_num)/det
    lemma_add_congruence::<F>(
        a_coef.mul(x_num.div(det)), a_coef.mul(x_num).div(det),
        b_coef.mul(y_num.div(det)), b_coef.mul(y_num).div(det),
    );
    lemma_div_distributes_over_add::<F>(a_coef.mul(x_num), b_coef.mul(y_num), det);
    F::axiom_eqv_symmetric(
        a_coef.mul(x_num).add(b_coef.mul(y_num)).div(det),
        a_coef.mul(x_num).div(det).add(b_coef.mul(y_num).div(det)),
    );
    F::axiom_eqv_transitive(
        a_coef.mul(x_num.div(det)).add(b_coef.mul(y_num.div(det))),
        a_coef.mul(x_num).div(det).add(b_coef.mul(y_num).div(det)),
        a_coef.mul(x_num).add(b_coef.mul(y_num)).div(det),
    );

    //  From numerator ≡ 0: c*det ≡ neg(numer), then derive numer ≡ neg(c*det)
    let numer = a_coef.mul(x_num).add(b_coef.mul(y_num));
    lemma_neg_unique::<F>(numer, c_coef.mul(det));
    //  c*det ≡ neg(numer) → neg(c*det) ≡ neg(neg(numer)) ≡ numer
    F::axiom_neg_congruence(c_coef.mul(det), numer.neg());
    lemma_neg_involution::<F>(numer);
    F::axiom_eqv_transitive(c_coef.mul(det).neg(), numer.neg().neg(), numer);
    F::axiom_eqv_symmetric(c_coef.mul(det).neg(), numer);

    //  numer/det ≡ (-(c*det))/det
    F::axiom_eqv_reflexive(det);
    verus_algebra::quadratic::lemma_div_congruence::<F>(numer, c_coef.mul(det).neg(), det, det);
    //  (-(c*det))/det ≡ -((c*det)/det)
    lemma_div_neg_numerator::<F>(c_coef.mul(det), det);
    //  (c*det)/det ≡ c
    lemma_mul_div_cancel::<F>(c_coef, det);
    //  -((c*det)/det) ≡ -c
    F::axiom_neg_congruence(c_coef.mul(det).div(det), c_coef);
    F::axiom_eqv_transitive(
        c_coef.mul(det).neg().div(det),
        c_coef.mul(det).div(det).neg(),
        c_coef.neg(),
    );
    F::axiom_eqv_transitive(numer.div(det), c_coef.mul(det).neg().div(det), c_coef.neg());

    //  a*px + b*py ≡ -c
    F::axiom_eqv_transitive(
        a_coef.mul(x_num.div(det)).add(b_coef.mul(y_num.div(det))),
        numer.div(det),
        c_coef.neg(),
    );

    //  a*px + b*py + c ≡ -c + c ≡ 0
    F::axiom_eqv_reflexive(c_coef);
    lemma_add_congruence::<F>(
        a_coef.mul(x_num.div(det)).add(b_coef.mul(y_num.div(det))), c_coef.neg(),
        c_coef, c_coef,
    );
    lemma_add_inverse_left::<F>(c_coef);
    F::axiom_eqv_transitive(
        a_coef.mul(x_num.div(det)).add(b_coef.mul(y_num.div(det))).add(c_coef),
        c_coef.neg().add(c_coef),
        F::zero(),
    );
}

//  ===========================================================================
//   Main lemmas
//  ===========================================================================

///  Bridge: a*b - c*d ≡ a*b - d*c when c*d ≡ d*c (by commutativity).
///  This converts between the numerator lemma's det (a1*b2 - a2*b1) and
///  line_det's det (a1*b2 - b1*a2).
proof fn lemma_det_commute_bridge<F: OrderedField>(a1: F, b1: F, a2: F, b2: F)
    ensures
        a1.mul(b2).sub(a2.mul(b1)).eqv(a1.mul(b2).sub(b1.mul(a2))),
{
    F::axiom_mul_commutative(a2, b1);
    F::axiom_eqv_reflexive(a1.mul(b2));
    lemma_sub_congruence::<F>(a1.mul(b2), a1.mul(b2), a2.mul(b1), b1.mul(a2));
}

///  Bridge a numerator identity from det_alt to det via congruence.
proof fn lemma_numerator_bridge<F: OrderedField>(
    a_coef: F, b_coef: F, c_coef: F, x_num: F, y_num: F, det_alt: F, det: F,
)
    requires
        det_alt.eqv(det),
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det_alt)).eqv(F::zero()),
    ensures
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det)).eqv(F::zero()),
{
    lemma_mul_congruence_right::<F>(c_coef, det_alt, det);
    F::axiom_eqv_reflexive(a_coef.mul(x_num).add(b_coef.mul(y_num)));
    lemma_add_congruence::<F>(
        a_coef.mul(x_num).add(b_coef.mul(y_num)),
        a_coef.mul(x_num).add(b_coef.mul(y_num)),
        c_coef.mul(det_alt),
        c_coef.mul(det),
    );
    F::axiom_eqv_symmetric(
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det)),
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det_alt)),
    );
    F::axiom_eqv_transitive(
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det)),
        a_coef.mul(x_num).add(b_coef.mul(y_num)).add(c_coef.mul(det_alt)),
        F::zero(),
    );
}

///  The intersection point lies on l1.
pub proof fn lemma_ll_intersection_on_l1<F: OrderedField>(l1: Line2<F>, l2: Line2<F>)
    requires
        !line_det(l1, l2).eqv(F::zero()),
    ensures
        point_on_line2(l1, line_line_intersection_2d(l1, l2)),
{
    let det = line_det(l1, l2);
    let x_num = l1.b.mul(l2.c).sub(l2.b.mul(l1.c));
    let y_num = l2.a.mul(l1.c).sub(l1.a.mul(l2.c));
    let det_alt = l1.a.mul(l2.b).sub(l2.a.mul(l1.b));

    lemma_ll_numerator_l1::<F>(l1.a, l1.b, l1.c, l2.a, l2.b, l2.c);
    lemma_det_commute_bridge::<F>(l1.a, l1.b, l2.a, l2.b);
    lemma_numerator_bridge::<F>(l1.a, l1.b, l1.c, x_num, y_num, det_alt, det);
    lemma_ll_eval_from_numerator::<F>(l1.a, l1.b, l1.c, x_num, y_num, det);
}

///  The intersection point lies on l2.
pub proof fn lemma_ll_intersection_on_l2<F: OrderedField>(l1: Line2<F>, l2: Line2<F>)
    requires
        !line_det(l1, l2).eqv(F::zero()),
    ensures
        point_on_line2(l2, line_line_intersection_2d(l1, l2)),
{
    let det = line_det(l1, l2);
    let x_num = l1.b.mul(l2.c).sub(l2.b.mul(l1.c));
    let y_num = l2.a.mul(l1.c).sub(l1.a.mul(l2.c));
    let det_alt = l1.a.mul(l2.b).sub(l2.a.mul(l1.b));

    lemma_ll_numerator_l2::<F>(l1.a, l1.b, l1.c, l2.a, l2.b, l2.c);
    lemma_det_commute_bridge::<F>(l1.a, l1.b, l2.a, l2.b);
    lemma_numerator_bridge::<F>(l2.a, l2.b, l2.c, x_num, y_num, det_alt, det);
    lemma_ll_eval_from_numerator::<F>(l2.a, l2.b, l2.c, x_num, y_num, det);
}

///  Parallel lines have zero determinant (and vice versa).
pub proof fn lemma_parallel_iff_zero_det<T: Ring>(l1: Line2<T>, l2: Line2<T>)
    ensures
        lines_parallel(l1, l2) == line_det(l1, l2).eqv(T::zero()),
{
    //  lines_parallel and line_det are definitionally the same expression.
}

} //  verus!
