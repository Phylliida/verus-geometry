use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::convex::{two, lemma_two_nonzero};
use crate::point2::*;
use crate::line2::*;
use crate::circle2::*;
use crate::circle_circle::*;

verus! {

// ===========================================================================
//  Algebraic helpers for circle-circle intersection proofs
// ===========================================================================

/// (X-Y)-(X-Z) ≡ Z-Y  (cancellation of common minuend)
pub proof fn lemma_sub_cancel_common<T: Ring>(x: T, y: T, z: T)
    ensures
        x.sub(y).sub(x.sub(z)).eqv(z.sub(y)),
{
    // Strategy: show (X-Y)+(Z-X) ≡ Z-Y via telescope, then bridge from (X-Y)-(X-Z)

    // Step 1: (X-Y)-(X-Z) ≡ (X-Y)+(-(X-Z))
    T::axiom_sub_is_add_neg(x.sub(y), x.sub(z));

    // Step 2: -(X-Z) ≡ Z-X
    additive_group_lemmas::lemma_neg_sub::<T>(x, z);

    // Step 3: (X-Y)+(-(X-Z)) ≡ (X-Y)+(Z-X)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        x.sub(y), x.sub(z).neg(), z.sub(x),
    );

    // Step 4: chain: (X-Y)-(X-Z) ≡ (X-Y)+(Z-X)
    T::axiom_eqv_transitive(
        x.sub(y).sub(x.sub(z)),
        x.sub(y).add(x.sub(z).neg()),
        x.sub(y).add(z.sub(x)),
    );

    // Step 5: commute: (X-Y)+(Z-X) ≡ (Z-X)+(X-Y)
    T::axiom_add_commutative(x.sub(y), z.sub(x));

    // Now show (Z-X)+(X-Y) ≡ Z-Y via telescope:

    // Step 6: X-Y ≡ X+(-Y)
    T::axiom_sub_is_add_neg(x, y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        z.sub(x), x.sub(y), x.add(y.neg()),
    );

    // Step 7: assoc: (Z-X)+(X+(-Y)) ≡ ((Z-X)+X)+(-Y)
    T::axiom_add_associative(z.sub(x), x, y.neg());
    T::axiom_eqv_symmetric(
        z.sub(x).add(x).add(y.neg()),
        z.sub(x).add(x.add(y.neg())),
    );

    // Step 8: (Z-X)+X ≡ Z
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(z, x);

    // Step 9: ((Z-X)+X)+(-Y) ≡ Z+(-Y)
    T::axiom_add_congruence_left(z.sub(x).add(x), z, y.neg());

    // Step 10: chain: (Z-X)+(X+(-Y)) ≡ Z+(-Y)
    T::axiom_eqv_transitive(
        z.sub(x).add(x.add(y.neg())),
        z.sub(x).add(x).add(y.neg()),
        z.add(y.neg()),
    );

    // Step 11: (Z-X)+(X-Y) ≡ Z+(-Y)
    T::axiom_eqv_transitive(
        z.sub(x).add(x.sub(y)),
        z.sub(x).add(x.add(y.neg())),
        z.add(y.neg()),
    );

    // Step 12: Z+(-Y) ≡ Z-Y
    T::axiom_sub_is_add_neg(z, y);
    T::axiom_eqv_symmetric(z.sub(y), z.add(y.neg()));
    T::axiom_eqv_transitive(
        z.sub(x).add(x.sub(y)),
        z.add(y.neg()),
        z.sub(y),
    );

    // Step 13: chain: (X-Y)+(Z-X) ≡ (Z-X)+(X-Y) ≡ Z-Y
    T::axiom_eqv_transitive(
        x.sub(y).add(z.sub(x)),
        z.sub(x).add(x.sub(y)),
        z.sub(y),
    );

    // Step 14: final: (X-Y)-(X-Z) ≡ (X-Y)+(Z-X) ≡ Z-Y
    T::axiom_eqv_transitive(
        x.sub(y).sub(x.sub(z)),
        x.sub(y).add(z.sub(x)),
        z.sub(y),
    );
}

/// (a-b)² - (a-c)² ≡ two*(c-b)*a + b²-c²
///
/// Key identity for the radical axis proof. Uses difference-of-squares
/// factoring: A²-B² = (A-B)(A+B), then distributes and simplifies.
pub proof fn lemma_sq_diff<T: Ring>(a: T, b: T, c: T)
    ensures
        a.sub(b).mul(a.sub(b)).sub(a.sub(c).mul(a.sub(c)))
            .eqv(two::<T>().mul(c.sub(b)).mul(a).add(b.mul(b).sub(c.mul(c)))),
{
    let t = two::<T>();
    let ab = a.sub(b);
    let ac = a.sub(c);
    let cb = c.sub(b);
    let bb = b.mul(b);
    let cc = c.mul(c);
    let x = cb.mul(a);  // (c-b)*a
    let y = cb.mul(b);  // (c-b)*b
    let z = cb.mul(c);  // (c-b)*c

    // Part 1: A²-B² ≡ (A-B)*(A+B)
    ring_lemmas::lemma_square_sub::<T>(ab, ac);
    T::axiom_eqv_symmetric(ab.sub(ac).mul(ab.add(ac)), ab.mul(ab).sub(ac.mul(ac)));
    // LHS ≡ (A-B)*(A+B)

    // Part 2: A-B ≡ c-b
    lemma_sub_cancel_common::<T>(a, b, c);

    // Part 3: (A-B)*(A+B) ≡ (c-b)*(A+B)
    T::axiom_mul_congruence_left(ab.sub(ac), cb, ab.add(ac));
    T::axiom_eqv_transitive(
        ab.mul(ab).sub(ac.mul(ac)),
        ab.sub(ac).mul(ab.add(ac)),
        cb.mul(ab.add(ac)),
    );

    // Part 4: distribute (c-b)*((a-b)+(a-c)) ≡ (c-b)*(a-b) + (c-b)*(a-c)
    T::axiom_mul_distributes_left(cb, ab, ac);
    T::axiom_eqv_transitive(
        ab.mul(ab).sub(ac.mul(ac)),
        cb.mul(ab.add(ac)),
        cb.mul(ab).add(cb.mul(ac)),
    );

    // Part 5: (c-b)*(a-b) ≡ x-y and (c-b)*(a-c) ≡ x-z
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(cb, a, b);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(cb, a, c);

    // Part 6: sum ≡ (x-y)+(x-z)
    additive_group_lemmas::lemma_add_congruence::<T>(
        cb.mul(ab), x.sub(y),
        cb.mul(ac), x.sub(z),
    );
    T::axiom_eqv_transitive(
        ab.mul(ab).sub(ac.mul(ac)),
        cb.mul(ab).add(cb.mul(ac)),
        x.sub(y).add(x.sub(z)),
    );

    // Part 7: rearrange (x-y)+(x-z) ≡ (x+x)+((-y)+(-z))
    T::axiom_sub_is_add_neg(x, y);
    T::axiom_sub_is_add_neg(x, z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        x.sub(y), x.add(y.neg()),
        x.sub(z), x.add(z.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(x, y.neg(), x, z.neg());
    T::axiom_eqv_transitive(
        x.sub(y).add(x.sub(z)),
        x.add(y.neg()).add(x.add(z.neg())),
        x.add(x).add(y.neg().add(z.neg())),
    );
    T::axiom_eqv_transitive(
        ab.mul(ab).sub(ac.mul(ac)),
        x.sub(y).add(x.sub(z)),
        x.add(x).add(y.neg().add(z.neg())),
    );

    // Part 8: x+x ≡ two*x ≡ two*(c-b)*a
    ring_lemmas::lemma_mul_two::<T>(x);
    T::axiom_mul_associative(t, cb, a);
    T::axiom_eqv_symmetric(t.mul(cb).mul(a), t.mul(cb.mul(a)));
    T::axiom_eqv_transitive(x.add(x), t.mul(x), t.mul(cb).mul(a));

    // Part 9: (-y)+(-z) ≡ b²-c²
    // neg_add gives -(y+z) ≡ (-y)+(-z), reversed:
    additive_group_lemmas::lemma_neg_add::<T>(y, z);
    T::axiom_eqv_symmetric(y.add(z).neg(), y.neg().add(z.neg()));

    // y+z ≡ (c-b)*(b+c) by distributes reversed
    T::axiom_mul_distributes_left(cb, b, c);
    T::axiom_eqv_symmetric(cb.mul(b.add(c)), cb.mul(b).add(cb.mul(c)));

    // (c-b)*(b+c) ≡ (c-b)*(c+b) ≡ c²-b² by square_sub
    T::axiom_add_commutative(b, c);
    ring_lemmas::lemma_mul_congruence_right::<T>(cb, b.add(c), c.add(b));
    ring_lemmas::lemma_square_sub::<T>(c, b);
    T::axiom_eqv_transitive(cb.mul(b.add(c)), cb.mul(c.add(b)), cc.sub(bb));

    // y+z ≡ c²-b²
    T::axiom_eqv_transitive(y.add(z), cb.mul(b.add(c)), cc.sub(bb));

    // -(y+z) ≡ -(c²-b²) ≡ b²-c²
    additive_group_lemmas::lemma_neg_congruence::<T>(y.add(z), cc.sub(bb));
    additive_group_lemmas::lemma_neg_sub::<T>(cc, bb);

    // (-y)+(-z) ≡ -(y+z) ≡ -(c²-b²) ≡ b²-c²
    T::axiom_eqv_transitive(y.neg().add(z.neg()), y.add(z).neg(), cc.sub(bb).neg());
    T::axiom_eqv_transitive(y.neg().add(z.neg()), cc.sub(bb).neg(), bb.sub(cc));

    // Part 10: combine: (x+x)+((-y)+(-z)) ≡ two*(c-b)*a + (b²-c²)
    additive_group_lemmas::lemma_add_congruence::<T>(
        x.add(x), t.mul(cb).mul(a),
        y.neg().add(z.neg()), bb.sub(cc),
    );

    // Final chain
    T::axiom_eqv_transitive(
        ab.mul(ab).sub(ac.mul(ac)),
        x.add(x).add(y.neg().add(z.neg())),
        t.mul(cb).mul(a).add(bb.sub(cc)),
    );
}

/// (A+B)-(C+D) ≡ (A-C)+(B-D)
pub proof fn lemma_sum_sub_rearrange<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.add(b).sub(c.add(d)).eqv(a.sub(c).add(b.sub(d))),
{
    // (A+B)-(C+D) = (A+B)+(-(C+D))
    T::axiom_sub_is_add_neg(a.add(b), c.add(d));

    // -(C+D) ≡ (-C)+(-D)
    additive_group_lemmas::lemma_neg_add::<T>(c, d);

    // (A+B)+(-(C+D)) ≡ (A+B)+((-C)+(-D))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(b), c.add(d).neg(), c.neg().add(d.neg()),
    );

    // (A+B)+((-C)+(-D)) ≡ (A+(-C))+(B+(-D)) by rearrange
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, c.neg(), d.neg());

    // A+(-C) ≡ A-C and B+(-D) ≡ B-D
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    T::axiom_sub_is_add_neg(b, d);
    T::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(c.neg()), a.sub(c),
        b.add(d.neg()), b.sub(d),
    );

    // Chain: (A+B)-(C+D) ≡ (A+(-C))+(B+(-D)) ≡ (A-C)+(B-D)
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );
}

/// (A-B)+(C-D) ≡ (A+C)-(B+D)
pub proof fn lemma_diff_sum_rearrange<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).add(c.sub(d)).eqv(a.add(c).sub(b.add(d))),
{
    // Convert subs to add form
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_sub_is_add_neg(c, d);

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b), a.add(b.neg()),
        c.sub(d), c.add(d.neg()),
    );

    // (A+(-B))+(C+(-D)) ≡ (A+C)+((-B)+(-D)) by rearrange
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b.neg(), c, d.neg());

    // (-B)+(-D) ≡ -(B+D)
    additive_group_lemmas::lemma_neg_add::<T>(b, d);
    T::axiom_eqv_symmetric(b.add(d).neg(), b.neg().add(d.neg()));

    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(c), b.neg().add(d.neg()), b.add(d).neg(),
    );

    // (A+C)+(-(B+D)) ≡ (A+C)-(B+D)
    T::axiom_sub_is_add_neg(a.add(c), b.add(d));
    T::axiom_eqv_symmetric(a.add(c).sub(b.add(d)), a.add(c).add(b.add(d).neg()));

    // Chain
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(b.neg()).add(c.add(d.neg())),
        a.add(c).add(b.neg().add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).add(b.neg().add(d.neg())),
        a.add(c).add(b.add(d).neg()),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).add(b.add(d).neg()),
        a.add(c).sub(b.add(d)),
    );
}

/// Centers not equivalent + OrderedField → radical axis is nondegenerate.
pub proof fn lemma_radical_axis_nondegenerate<F: OrderedField>(
    c1: Circle2<F>, c2: Circle2<F>,
)
    requires
        !c1.center.eqv(c2.center),
    ensures
        line2_nondegenerate(radical_axis(c1, c2)),
{
    let l = radical_axis(c1, c2);
    let c1x = c1.center.x;
    let c1y = c1.center.y;
    let c2x = c2.center.x;
    let c2y = c2.center.y;

    lemma_two_nonzero::<F>();

    // line2_nondegenerate = !l.a.eqv(zero) || !l.b.eqv(zero)
    // If l.a.eqv(zero), show !l.b.eqv(zero) to satisfy the disjunction.
    if l.a.eqv(F::zero()) {
        // l.a = two*(c2x-c1x) ≡ 0 and two ≢ 0 → c2x-c1x ≡ 0
        if !c2x.sub(c1x).eqv(F::zero()) {
            field_lemmas::lemma_nonzero_product::<F>(two::<F>(), c2x.sub(c1x));
            // two*(c2x-c1x) ≢ 0, contradicts l.a ≡ 0
        }
        // c2x-c1x ≡ 0 → c2x ≡ c1x
        crate::collinearity::lemma_sub_zero_implies_eqv::<F>(c2x, c1x);
        F::axiom_eqv_symmetric(c2x, c1x);

        // Since !c1.center.eqv(c2.center) and c1x≡c2x, must have c1y≢c2y
        // If c2y-c1y ≡ 0, then c2y ≡ c1y, giving c1.center ≡ c2.center — contradiction
        if c2y.sub(c1y).eqv(F::zero()) {
            crate::collinearity::lemma_sub_zero_implies_eqv::<F>(c2y, c1y);
            F::axiom_eqv_symmetric(c2y, c1y);
            // Now c1x≡c2x and c1y≡c2y → c1.center.eqv(c2.center) — contradiction
        }
        // c2y-c1y ≢ 0 and two ≢ 0 → two*(c2y-c1y) ≢ 0 → !l.b.eqv(zero)
        field_lemmas::lemma_nonzero_product::<F>(two::<F>(), c2y.sub(c1y));
    }
    // Otherwise !l.a.eqv(zero) satisfies the disjunction directly
}

/// (A-B)-(C-D) ≡ (A-C)-(B-D)  (subtraction rearrangement)
pub proof fn lemma_sub_sub_rearrange<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).sub(c.sub(d)).eqv(a.sub(c).sub(b.sub(d))),
{
    // (A-B)-(C-D) = (A-B)+D-C via -(C-D) = D-C
    // Convert subs to add+neg form
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_sub_is_add_neg(c, d);

    // -(C-D) ≡ D-C
    additive_group_lemmas::lemma_neg_sub::<T>(c, d);

    // (A-B)-(C-D) ≡ (A-B)+(D-C)
    T::axiom_sub_is_add_neg(a.sub(b), c.sub(d));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.sub(b), c.sub(d).neg(), d.sub(c),
    );
    T::axiom_eqv_transitive(
        a.sub(b).sub(c.sub(d)),
        a.sub(b).add(c.sub(d).neg()),
        a.sub(b).add(d.sub(c)),
    );

    // Similarly: -(B-D) ≡ D-B
    additive_group_lemmas::lemma_neg_sub::<T>(b, d);

    // (A-C)-(B-D) ≡ (A-C)+(D-B)
    T::axiom_sub_is_add_neg(a.sub(c), b.sub(d));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.sub(c), b.sub(d).neg(), d.sub(b),
    );
    T::axiom_eqv_transitive(
        a.sub(c).sub(b.sub(d)),
        a.sub(c).add(b.sub(d).neg()),
        a.sub(c).add(d.sub(b)),
    );

    // Now show (A-B)+(D-C) ≡ (A-C)+(D-B)
    // Convert A-B = A+(-B), D-C = D+(-C), A-C = A+(-C), D-B = D+(-B)
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_sub_is_add_neg(d, c);
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_sub_is_add_neg(d, b);

    // (A+(-B))+(D+(-C)) ≡ (A+D)+((-B)+(-C)) by rearrange_2x2
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b), a.add(b.neg()),
        d.sub(c), d.add(c.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b.neg(), d, c.neg());
    T::axiom_eqv_transitive(
        a.sub(b).add(d.sub(c)),
        a.add(b.neg()).add(d.add(c.neg())),
        a.add(d).add(b.neg().add(c.neg())),
    );

    // (A+(-C))+(D+(-B)) ≡ (A+D)+((-C)+(-B)) by rearrange_2x2
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(c), a.add(c.neg()),
        d.sub(b), d.add(b.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, c.neg(), d, b.neg());
    T::axiom_eqv_transitive(
        a.sub(c).add(d.sub(b)),
        a.add(c.neg()).add(d.add(b.neg())),
        a.add(d).add(c.neg().add(b.neg())),
    );

    // (-B)+(-C) ≡ (-C)+(-B) by commutativity
    T::axiom_add_commutative(b.neg(), c.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(d), b.neg().add(c.neg()), c.neg().add(b.neg()),
    );

    // Chain: both sides equal (A+D)+((-C)+(-B))
    T::axiom_eqv_transitive(
        a.sub(b).add(d.sub(c)),
        a.add(d).add(b.neg().add(c.neg())),
        a.add(d).add(c.neg().add(b.neg())),
    );
    T::axiom_eqv_symmetric(
        a.sub(c).add(d.sub(b)),
        a.add(d).add(c.neg().add(b.neg())),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(d.sub(c)),
        a.add(d).add(c.neg().add(b.neg())),
        a.sub(c).add(d.sub(b)),
    );

    // Final: (A-B)-(C-D) ≡ (A-B)+(D-C) ≡ (A-C)+(D-B) ≡ (A-C)-(B-D)
    T::axiom_eqv_transitive(
        a.sub(b).sub(c.sub(d)),
        a.sub(b).add(d.sub(c)),
        a.sub(c).add(d.sub(b)),
    );
    T::axiom_eqv_symmetric(
        a.sub(c).sub(b.sub(d)),
        a.sub(c).add(d.sub(b)),
    );
    T::axiom_eqv_transitive(
        a.sub(b).sub(c.sub(d)),
        a.sub(c).add(d.sub(b)),
        a.sub(c).sub(b.sub(d)),
    );
}

} // verus!
