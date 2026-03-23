/// Symmetric decomposition: perp + midpoint-on-axis ⟹ q ≡ reflect(p, a, b).
///
/// This module proves the backward direction of the symmetric constraint
/// decomposition: if q-p is perpendicular to b-a and the midpoint of p,q
/// lies on line(a,b), then q equals the reflection of p across line(a,b).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use crate::point2::*;
use crate::line2::*;
use crate::line2::{
    lemma_add_sub_cancel_common,
    lemma_add_exchange,
    lemma_2x2_trivial_solution,
    lemma_reflect_satisfies_perp,
    lemma_reflect_midpoint_on_axis,
};

verus! {

/// Symmetric decomposition backward direction:
/// If dot(q-p, d) ≡ 0 (perpendicularity) and midpoint(p,q) on line(a,b) (midpoint-on-axis),
/// and dot(d,d) ≢ 0 (non-degenerate), then q ≡ reflect(p, a, b).
///
/// Proof: reflect(p,a,b) satisfies both conditions (forward lemmas in line2.rs).
/// The difference q - reflect satisfies a 2×2 linear system with det = dot(d,d) ≠ 0.
/// By uniqueness (lemma_2x2_trivial_solution), q ≡ reflect.
pub proof fn lemma_symmetric_decomposition_backward<F: OrderedField>(
    p: Point2<F>, q: Point2<F>, a: Point2<F>, b: Point2<F>,
)
    requires ({
        let d = sub2(b, a);
        let dot_dd = d.x.mul(d.x).add(d.y.mul(d.y));
        let line = line2_from_points(a, b);
        let two = F::one().add(F::one());
        // Non-degeneracy
        &&& !dot_dd.eqv(F::zero())
        // Perpendicularity: dot(q - p, d) ≡ 0
        &&& sub2(q, p).x.mul(d.x).add(sub2(q, p).y.mul(d.y)).eqv(F::zero())
        // Midpoint on axis (scaled by 2)
        &&& line.a.mul(p.x.add(q.x)).add(line.b.mul(p.y.add(q.y))).add(two.mul(line.c)).eqv(F::zero())
    }),
    ensures
        q.eqv(reflect_point_across_line(p, a, b)),
{
    let d = sub2(b, a);
    let dx = d.x;
    let dy = d.y;
    let r = reflect_point_across_line(p, a, b);
    let line = line2_from_points(a, b);
    let two = F::one().add(F::one());
    let la = line.a;
    let lb = line.b;

    // Forward lemmas: r satisfies both conditions
    lemma_reflect_satisfies_perp::<F>(p, a, b);
    lemma_reflect_midpoint_on_axis::<F>(p, a, b);

    let u = q.x.sub(r.x);
    let v = q.y.sub(r.y);

    let perp_q = sub2(q, p).x.mul(dx).add(sub2(q, p).y.mul(dy));
    let perp_r = sub2(r, p).x.mul(dx).add(sub2(r, p).y.mul(dy));

    // perp_q ≡ 0 and perp_r ≡ 0 → perp_q - perp_r ≡ 0
    lemma_sub_congruence::<F>(perp_q, F::zero(), perp_r, F::zero());
    lemma_sub_self::<F>(F::zero());
    F::axiom_eqv_transitive(perp_q.sub(perp_r), F::zero().sub(F::zero()), F::zero());

    // === Equation 1: dx*u + dy*v ≡ 0 ===

    // (qx-px)-(rx-px) ≡ qx-rx = u
    // (qx-px) ≡ qx+(-px) by sub_is_add_neg. Similarly (rx-px) ≡ rx+(-px).
    // (qx+(-px)) - (rx+(-px)) ≡ qx - rx = u by add_sub_cancel_common.
    // Chain: sub2(q,p).x - sub2(r,p).x ≡ (qx+(-px)) - (rx+(-px)) ≡ u.
    assert(sub2(q, p).x.sub(sub2(r, p).x).eqv(u)) by {
        F::axiom_sub_is_add_neg(q.x, p.x);
        F::axiom_sub_is_add_neg(r.x, p.x);
        lemma_add_sub_cancel_common::<F>(q.x, r.x, p.x.neg());
        // sub_congruence: sub2(q,p).x ≡ qx+(-px) and sub2(r,p).x ≡ rx+(-px)
        // so sub2(q,p).x - sub2(r,p).x ≡ (qx+(-px)) - (rx+(-px)) ≡ u
        F::axiom_eqv_reflexive(sub2(r, p).x);
        lemma_sub_congruence::<F>(sub2(q, p).x, q.x.add(p.x.neg()), sub2(r, p).x, r.x.add(p.x.neg()));
        F::axiom_eqv_transitive(
            sub2(q, p).x.sub(sub2(r, p).x),
            q.x.add(p.x.neg()).sub(r.x.add(p.x.neg())),
            u);
    };
    assert(sub2(q, p).y.sub(sub2(r, p).y).eqv(v)) by {
        F::axiom_sub_is_add_neg(q.y, p.y);
        F::axiom_sub_is_add_neg(r.y, p.y);
        lemma_add_sub_cancel_common::<F>(q.y, r.y, p.y.neg());
        F::axiom_eqv_reflexive(sub2(r, p).y);
        lemma_sub_congruence::<F>(sub2(q, p).y, q.y.add(p.y.neg()), sub2(r, p).y, r.y.add(p.y.neg()));
        F::axiom_eqv_transitive(
            sub2(q, p).y.sub(sub2(r, p).y),
            q.y.add(p.y.neg()).sub(r.y.add(p.y.neg())),
            v);
    };

    // (A_q - A_r)*dx = ((qx-px)-(rx-px))*dx ≡ u*dx
    // A_q*dx - A_r*dx: use (A-B)*C ≡ A*C - B*C (distributes_right reversed)
    // But need: sub(A,B)*C first. sub(A,B) ≡ add(A, neg(B)), so (A+neg(B))*C ≡ A*C + neg(B)*C = A*C - B*C
    // sub(A,B)*C ≡ (A+neg(B))*C ≡ A*C + neg(B)*C ≡ A*C - B*C = sub(A*C, B*C)
    assert(sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)).eqv(u.mul(dx))) by {
        // (sub2(q,p).x - sub2(r,p).x) * dx ≡ u * dx by mul_congruence_left
        F::axiom_mul_congruence_left(sub2(q, p).x.sub(sub2(r, p).x), u, dx);
        // sub2(q,p).x.mul(dx) - sub2(r,p).x.mul(dx):
        // = sub2(q,p).x.mul(dx) + (-(sub2(r,p).x.mul(dx)))
        F::axiom_sub_is_add_neg(sub2(q, p).x.mul(dx), sub2(r, p).x.mul(dx));
        // (sub2(q,p).x - sub2(r,p).x) * dx = (sub2(q,p).x + (-sub2(r,p).x)) * dx
        F::axiom_sub_is_add_neg(sub2(q, p).x, sub2(r, p).x);
        // = sub2(q,p).x*dx + (-sub2(r,p).x)*dx [distributes_right]
        lemma_mul_distributes_right::<F>(sub2(q, p).x, sub2(r, p).x.neg(), dx);
        // (-sub2(r,p).x)*dx ≡ -(sub2(r,p).x*dx) [mul_neg_left]
        lemma_mul_neg_left::<F>(sub2(r, p).x, dx);
        // Chain: sub(A_q*dx, A_r*dx) ≡ add(A_q*dx, -(A_r*dx))
        //        (sub2(q,p).x.sub(sub2(r,p).x))*dx ≡ add(sub2(q,p).x*dx, neg(sub2(r,p).x)*dx)
        //                                          ≡ add(sub2(q,p).x*dx, -(sub2(r,p).x*dx))
        //                                          ≡ sub(sub2(q,p).x*dx, sub2(r,p).x*dx)
        // And (sub2(q,p).x-sub2(r,p).x)*dx ≡ u*dx.
        // Connect: sub(A_q*dx, A_r*dx) ≡ (sub2(q,p).x.add(sub2(r,p).x.neg()))*dx
        F::axiom_mul_congruence_left(sub2(q, p).x.sub(sub2(r, p).x),
            sub2(q, p).x.add(sub2(r, p).x.neg()), dx);
        lemma_add_congruence_right::<F>(sub2(q, p).x.mul(dx),
            sub2(r, p).x.neg().mul(dx), sub2(r, p).x.mul(dx).neg());
        F::axiom_eqv_transitive(
            sub2(q, p).x.add(sub2(r, p).x.neg()).mul(dx),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.neg().mul(dx)),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()));
        // sub2(q,p).x.sub(sub2(r,p).x) ≡ sub2(q,p).x.add(sub2(r,p).x.neg())
        F::axiom_eqv_transitive(
            sub2(q, p).x.sub(sub2(r, p).x).mul(dx),
            sub2(q, p).x.add(sub2(r, p).x.neg()).mul(dx),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()));
        // Chain: sub(A_q*dx, A_r*dx) ≡ add(A_q*dx, -(A_r*dx)) ≡ (sub(A_q,A_r))*dx ≡ u*dx
        F::axiom_eqv_symmetric(
            sub2(q, p).x.sub(sub2(r, p).x).mul(dx),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()));
        F::axiom_eqv_transitive(
            sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()),
            sub2(q, p).x.sub(sub2(r, p).x).mul(dx));
        F::axiom_eqv_transitive(
            sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)),
            sub2(q, p).x.sub(sub2(r, p).x).mul(dx),
            u.mul(dx));
    };
    assert(sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)).eqv(v.mul(dy))) by {
        F::axiom_mul_congruence_left(sub2(q, p).y.sub(sub2(r, p).y), v, dy);
        F::axiom_sub_is_add_neg(sub2(q, p).y.mul(dy), sub2(r, p).y.mul(dy));
        F::axiom_sub_is_add_neg(sub2(q, p).y, sub2(r, p).y);
        lemma_mul_distributes_right::<F>(sub2(q, p).y, sub2(r, p).y.neg(), dy);
        lemma_mul_neg_left::<F>(sub2(r, p).y, dy);
        F::axiom_mul_congruence_left(sub2(q, p).y.sub(sub2(r, p).y),
            sub2(q, p).y.add(sub2(r, p).y.neg()), dy);
        lemma_add_congruence_right::<F>(sub2(q, p).y.mul(dy),
            sub2(r, p).y.neg().mul(dy), sub2(r, p).y.mul(dy).neg());
        F::axiom_eqv_transitive(
            sub2(q, p).y.add(sub2(r, p).y.neg()).mul(dy),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.neg().mul(dy)),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()));
        F::axiom_eqv_transitive(
            sub2(q, p).y.sub(sub2(r, p).y).mul(dy),
            sub2(q, p).y.add(sub2(r, p).y.neg()).mul(dy),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()));
        F::axiom_eqv_symmetric(
            sub2(q, p).y.sub(sub2(r, p).y).mul(dy),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()));
        F::axiom_eqv_transitive(
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()),
            sub2(q, p).y.sub(sub2(r, p).y).mul(dy));
        F::axiom_eqv_transitive(
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)),
            sub2(q, p).y.sub(sub2(r, p).y).mul(dy),
            v.mul(dy));
    };

    // (A_q+C_q) - (A_r+C_r) ≡ (A_q-A_r) + (C_q-C_r) by neg_add + exchange
    // perp_q - perp_r ≡ (A_q - A_r) + (C_q - C_r)
    // = (sub2(q,p).x*dx - sub2(r,p).x*dx) + (sub2(q,p).y*dy - sub2(r,p).y*dy)
    // Proof: perp_q - perp_r = perp_q + (-perp_r)
    //   = (A_q + C_q) + (-(A_r + C_r))
    //   = (A_q + C_q) + (-A_r + -C_r)  [neg_add]
    //   = (A_q + -A_r) + (C_q + -C_r)  [exchange]
    //   = (A_q - A_r) + (C_q - C_r)    [sub_is_add_neg reversed]
    assert(perp_q.sub(perp_r).eqv(
        sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)).add(
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy))))) by {
        F::axiom_sub_is_add_neg(perp_q, perp_r);
        lemma_neg_add::<F>(sub2(r, p).x.mul(dx), sub2(r, p).y.mul(dy));
        lemma_add_congruence_right::<F>(perp_q, perp_r.neg(),
            sub2(r, p).x.mul(dx).neg().add(sub2(r, p).y.mul(dy).neg()));
        // perp_q + neg(perp_r) ≡ perp_q + (-A_r + -C_r)
        // Exchange: (A_q + C_q) + (-A_r + -C_r) = (A_q + -A_r) + (C_q + -C_r)
        lemma_add_exchange::<F>(
            sub2(q, p).x.mul(dx), sub2(q, p).y.mul(dy),
            sub2(r, p).x.mul(dx).neg(), sub2(r, p).y.mul(dy).neg());
        // Convert add+neg back to sub:
        F::axiom_sub_is_add_neg(sub2(q, p).x.mul(dx), sub2(r, p).x.mul(dx));
        F::axiom_sub_is_add_neg(sub2(q, p).y.mul(dy), sub2(r, p).y.mul(dy));
        // (A_q + -A_r) ≡ sub(A_q, A_r) and (C_q + -C_r) ≡ sub(C_q, C_r) (reverse sub_is_add_neg)
        F::axiom_eqv_symmetric(
            sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()));
        F::axiom_eqv_symmetric(
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()));
        lemma_add_congruence::<F>(
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()),
            sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)),
            sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg()),
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)));
        // Chain: perp_q - perp_r ≡ ... ≡ (A_q-A_r) + (C_q-C_r)
        F::axiom_eqv_transitive(
            perp_q.sub(perp_r),
            perp_q.add(perp_r.neg()),
            perp_q.add(sub2(r, p).x.mul(dx).neg().add(sub2(r, p).y.mul(dy).neg())));
        F::axiom_eqv_transitive(
            perp_q.sub(perp_r),
            perp_q.add(sub2(r, p).x.mul(dx).neg().add(sub2(r, p).y.mul(dy).neg())),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()).add(
                sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg())));
        F::axiom_eqv_transitive(
            perp_q.sub(perp_r),
            sub2(q, p).x.mul(dx).add(sub2(r, p).x.mul(dx).neg()).add(
                sub2(q, p).y.mul(dy).add(sub2(r, p).y.mul(dy).neg())),
            sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)).add(
                sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy))));
    };

    // Chain: perp_q - perp_r ≡ (A_q-A_r)+(C_q-C_r) ≡ u*dx + v*dy
    lemma_add_congruence::<F>(
        sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)), u.mul(dx),
        sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy)), v.mul(dy));
    F::axiom_eqv_transitive(
        perp_q.sub(perp_r),
        sub2(q, p).x.mul(dx).sub(sub2(r, p).x.mul(dx)).add(
            sub2(q, p).y.mul(dy).sub(sub2(r, p).y.mul(dy))),
        u.mul(dx).add(v.mul(dy)));

    // u*dx + v*dy ≡ perp_q - perp_r ≡ 0
    F::axiom_eqv_symmetric(perp_q.sub(perp_r), u.mul(dx).add(v.mul(dy)));
    F::axiom_eqv_transitive(u.mul(dx).add(v.mul(dy)), perp_q.sub(perp_r), F::zero());

    // dx*u + dy*v ≡ u*dx + v*dy ≡ 0 by commutativity
    F::axiom_mul_commutative(dx, u);
    F::axiom_mul_commutative(dy, v);
    lemma_add_congruence::<F>(dx.mul(u), u.mul(dx), dy.mul(v), v.mul(dy));
    F::axiom_eqv_transitive(dx.mul(u).add(dy.mul(v)), u.mul(dx).add(v.mul(dy)), F::zero());

    // === Equation 2: -dy*u + dx*v ≡ 0 ===
    // Same approach using midpoint equations.
    let mid_q = la.mul(p.x.add(q.x)).add(lb.mul(p.y.add(q.y))).add(two.mul(line.c));
    let mid_r = la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y))).add(two.mul(line.c));

    // mid_q ≡ 0 and mid_r ≡ 0 → mid_q - mid_r ≡ 0
    lemma_sub_congruence::<F>(mid_q, F::zero(), mid_r, F::zero());
    lemma_sub_self::<F>(F::zero());
    F::axiom_eqv_transitive(mid_q.sub(mid_r), F::zero().sub(F::zero()), F::zero());

    // Cancel 2*lc: mid_q - mid_r ≡ (la*(px+qx)+lb*(py+qy)) - (la*(px+rx)+lb*(py+ry))
    let mid_inner_q = la.mul(p.x.add(q.x)).add(lb.mul(p.y.add(q.y)));
    let mid_inner_r = la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y)));
    lemma_add_sub_cancel_common::<F>(mid_inner_q, mid_inner_r, two.mul(line.c));
    // mid_q.sub(mid_r) ≡ mid_inner_q.sub(mid_inner_r) ≡ ... ≡ 0
    // add_sub_cancel_common gives: (mid_inner_q + 2lc) - (mid_inner_r + 2lc) ≡ mid_inner_q - mid_inner_r
    // i.e. mid_q - mid_r ≡ mid_inner_q - mid_inner_r
    // Chain: mid_inner_q - mid_inner_r ≡ mid_q - mid_r ≡ 0
    F::axiom_eqv_symmetric(mid_q.sub(mid_r), mid_inner_q.sub(mid_inner_r));
    F::axiom_eqv_transitive(mid_inner_q.sub(mid_inner_r), mid_q.sub(mid_r), F::zero());

    // mid_inner_q - mid_inner_r:
    // = (la*(px+qx) + lb*(py+qy)) - (la*(px+rx) + lb*(py+ry))
    // = (la*(px+qx) - la*(px+rx)) + (lb*(py+qy) - lb*(py+ry))  [neg_add + exchange]
    // la*(px+qx) - la*(px+rx) = la*((px+qx)-(px+rx)) = la*(qx-rx) = la*u  [distributes + cancel]
    // lb*(py+qy) - lb*(py+ry) = lb*(qy-ry) = lb*v

    // (px+qx) - (px+rx) ≡ qx - rx = u by add_sub_cancel_common
    assert(p.x.add(q.x).sub(p.x.add(r.x)).eqv(u)) by {
        // (qx+px) - (rx+px) ≡ qx - rx by add_sub_cancel_common
        lemma_add_sub_cancel_common::<F>(q.x, r.x, p.x);
        // px+qx ≡ qx+px and px+rx ≡ rx+px by commutativity
        F::axiom_add_commutative(p.x, q.x);
        F::axiom_add_commutative(p.x, r.x);
        lemma_sub_congruence::<F>(p.x.add(q.x), q.x.add(p.x), p.x.add(r.x), r.x.add(p.x));
        F::axiom_eqv_transitive(p.x.add(q.x).sub(p.x.add(r.x)),
            q.x.add(p.x).sub(r.x.add(p.x)), u);
    };
    assert(p.y.add(q.y).sub(p.y.add(r.y)).eqv(v)) by {
        lemma_add_sub_cancel_common::<F>(q.y, r.y, p.y);
        F::axiom_add_commutative(p.y, q.y);
        F::axiom_add_commutative(p.y, r.y);
        lemma_sub_congruence::<F>(p.y.add(q.y), q.y.add(p.y), p.y.add(r.y), r.y.add(p.y));
        F::axiom_eqv_transitive(p.y.add(q.y).sub(p.y.add(r.y)),
            q.y.add(p.y).sub(r.y.add(p.y)), v);
    };

    // la*(px+qx) - la*(px+rx) ≡ la*u by distributes_left on sub
    // la*X - la*Y ≡ la*(X-Y): same chain as before (sub_is_add_neg + distributes + neg_right)
    assert(la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))).eqv(la.mul(u))) by {
        F::axiom_sub_is_add_neg(p.x.add(q.x), p.x.add(r.x));
        F::axiom_mul_distributes_left(la, p.x.add(q.x), p.x.add(r.x).neg());
        lemma_mul_neg_right::<F>(la, p.x.add(r.x));
        F::axiom_sub_is_add_neg(la.mul(p.x.add(q.x)), la.mul(p.x.add(r.x)));
        // la*(X+neg(Y)) ≡ la*X + la*neg(Y) ≡ la*X + neg(la*Y)
        lemma_add_congruence_right::<F>(la.mul(p.x.add(q.x)),
            la.mul(p.x.add(r.x).neg()), la.mul(p.x.add(r.x)).neg());
        F::axiom_eqv_transitive(
            la.mul(p.x.add(q.x).add(p.x.add(r.x).neg())),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x).neg())),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()));
        // la*(X-Y) ≡ la*(X+neg(Y))
        lemma_mul_congruence_right::<F>(la, p.x.add(q.x).sub(p.x.add(r.x)),
            p.x.add(q.x).add(p.x.add(r.x).neg()));
        F::axiom_eqv_transitive(
            la.mul(p.x.add(q.x).sub(p.x.add(r.x))),
            la.mul(p.x.add(q.x).add(p.x.add(r.x).neg())),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()));
        // Chain: la*X - la*Y ≡ la*X+neg(la*Y) [sub_is_add_neg] ≡ la*(X-Y) [above]
        F::axiom_eqv_symmetric(
            la.mul(p.x.add(q.x).sub(p.x.add(r.x))),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()));
        F::axiom_eqv_transitive(
            la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()),
            la.mul(p.x.add(q.x).sub(p.x.add(r.x))));
        lemma_mul_congruence_right::<F>(la, p.x.add(q.x).sub(p.x.add(r.x)), u);
        F::axiom_eqv_transitive(
            la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))),
            la.mul(p.x.add(q.x).sub(p.x.add(r.x))),
            la.mul(u));
    };
    assert(lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))).eqv(lb.mul(v))) by {
        F::axiom_sub_is_add_neg(p.y.add(q.y), p.y.add(r.y));
        F::axiom_mul_distributes_left(lb, p.y.add(q.y), p.y.add(r.y).neg());
        lemma_mul_neg_right::<F>(lb, p.y.add(r.y));
        F::axiom_sub_is_add_neg(lb.mul(p.y.add(q.y)), lb.mul(p.y.add(r.y)));
        lemma_add_congruence_right::<F>(lb.mul(p.y.add(q.y)),
            lb.mul(p.y.add(r.y).neg()), lb.mul(p.y.add(r.y)).neg());
        F::axiom_eqv_transitive(
            lb.mul(p.y.add(q.y).add(p.y.add(r.y).neg())),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y).neg())),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()));
        lemma_mul_congruence_right::<F>(lb, p.y.add(q.y).sub(p.y.add(r.y)),
            p.y.add(q.y).add(p.y.add(r.y).neg()));
        F::axiom_eqv_transitive(
            lb.mul(p.y.add(q.y).sub(p.y.add(r.y))),
            lb.mul(p.y.add(q.y).add(p.y.add(r.y).neg())),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()));
        F::axiom_eqv_symmetric(
            lb.mul(p.y.add(q.y).sub(p.y.add(r.y))),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()));
        F::axiom_eqv_transitive(
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()),
            lb.mul(p.y.add(q.y).sub(p.y.add(r.y))));
        lemma_mul_congruence_right::<F>(lb, p.y.add(q.y).sub(p.y.add(r.y)), v);
        F::axiom_eqv_transitive(
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))),
            lb.mul(p.y.add(q.y).sub(p.y.add(r.y))),
            lb.mul(v));
    };

    // mid_inner_q - mid_inner_r ≡ (la*(px+qx)-la*(px+rx)) + (lb*(py+qy)-lb*(py+ry))
    assert(mid_inner_q.sub(mid_inner_r).eqv(
        la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))).add(
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y)))))) by {
        F::axiom_sub_is_add_neg(mid_inner_q, mid_inner_r);
        lemma_neg_add::<F>(la.mul(p.x.add(r.x)), lb.mul(p.y.add(r.y)));
        lemma_add_congruence_right::<F>(mid_inner_q, mid_inner_r.neg(),
            la.mul(p.x.add(r.x)).neg().add(lb.mul(p.y.add(r.y)).neg()));
        lemma_add_exchange::<F>(
            la.mul(p.x.add(q.x)), lb.mul(p.y.add(q.y)),
            la.mul(p.x.add(r.x)).neg(), lb.mul(p.y.add(r.y)).neg());
        F::axiom_sub_is_add_neg(la.mul(p.x.add(q.x)), la.mul(p.x.add(r.x)));
        F::axiom_sub_is_add_neg(lb.mul(p.y.add(q.y)), lb.mul(p.y.add(r.y)));
        // Convert add+neg to sub form
        F::axiom_eqv_symmetric(
            la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()));
        F::axiom_eqv_symmetric(
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()));
        lemma_add_congruence::<F>(
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()),
            la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))),
            lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg()),
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))));
        // Chain
        F::axiom_eqv_transitive(
            mid_inner_q.sub(mid_inner_r),
            mid_inner_q.add(mid_inner_r.neg()),
            mid_inner_q.add(la.mul(p.x.add(r.x)).neg().add(lb.mul(p.y.add(r.y)).neg())));
        F::axiom_eqv_transitive(
            mid_inner_q.sub(mid_inner_r),
            mid_inner_q.add(la.mul(p.x.add(r.x)).neg().add(lb.mul(p.y.add(r.y)).neg())),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()).add(
                lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg())));
        F::axiom_eqv_transitive(
            mid_inner_q.sub(mid_inner_r),
            la.mul(p.x.add(q.x)).add(la.mul(p.x.add(r.x)).neg()).add(
                lb.mul(p.y.add(q.y)).add(lb.mul(p.y.add(r.y)).neg())),
            la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))).add(
                lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y)))));
    };

    // ≡ la*u + lb*v
    lemma_add_congruence::<F>(
        la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))), la.mul(u),
        lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y))), lb.mul(v));
    F::axiom_eqv_transitive(
        mid_inner_q.sub(mid_inner_r),
        la.mul(p.x.add(q.x)).sub(la.mul(p.x.add(r.x))).add(
            lb.mul(p.y.add(q.y)).sub(lb.mul(p.y.add(r.y)))),
        la.mul(u).add(lb.mul(v)));

    // la*u + lb*v ≡ mid_inner_q - mid_inner_r ≡ 0
    F::axiom_eqv_symmetric(mid_inner_q.sub(mid_inner_r), la.mul(u).add(lb.mul(v)));
    F::axiom_eqv_transitive(la.mul(u).add(lb.mul(v)), mid_inner_q.sub(mid_inner_r), F::zero());
    // la = -dy, lb = dx structurally, so la*u + lb*v = (-dy)*u + dx*v = dy.neg().mul(u) + dx.mul(v)

    // === Apply uniqueness ===
    lemma_2x2_trivial_solution::<F>(dx, dy, u, v);
    // u ≡ 0 and v ≡ 0
    // qx - rx ≡ 0 → qx ≡ rx
    crate::collinearity::lemma_sub_zero_implies_eqv::<F>(q.x, r.x);
    // qy - ry ≡ 0 → qy ≡ ry
    crate::collinearity::lemma_sub_zero_implies_eqv::<F>(q.y, r.y);
    // q.eqv(r)
}

} // verus!
