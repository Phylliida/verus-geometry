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
use crate::constructed_scalar::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;

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

/// a + (b - c) ≡ (a + b) - c
pub proof fn lemma_add_sub_assoc<T: Ring>(a: T, b: T, c: T)
    ensures
        a.add(b.sub(c)).eqv(a.add(b).sub(c)),
{
    // a + (b - c) ≡ a + (b + (-c))
    T::axiom_sub_is_add_neg(b, c);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.sub(c), b.add(c.neg()));

    // a + (b + (-c)) ≡ (a + b) + (-c)   [assoc gives flat→nested, need symmetric]
    T::axiom_add_associative(a, b, c.neg());
    T::axiom_eqv_symmetric(
        a.add(b).add(c.neg()),
        a.add(b.add(c.neg())),
    );

    // (a + b) + (-c) ≡ (a + b) - c
    T::axiom_sub_is_add_neg(a.add(b), c);
    T::axiom_eqv_symmetric(a.add(b).sub(c), a.add(b).add(c.neg()));

    // Chain: a+(b-c) ≡ a+(b+(-c)) ≡ (a+b)+(-c) ≡ (a+b)-c
    T::axiom_eqv_transitive(
        a.add(b.sub(c)),
        a.add(b.add(c.neg())),
        a.add(b).add(c.neg()),
    );
    T::axiom_eqv_transitive(
        a.add(b.sub(c)),
        a.add(b).add(c.neg()),
        a.add(b).sub(c),
    );
}

/// Reverse radical axis: a point on c1 and on the radical axis is also on c2.
///
/// Algebraically: from D1 ≡ r1² and L.a*px + L.b*py + L.c ≡ 0,
/// derive D2 ≡ r2².
///
/// Proof: from lemma_radical_axis_correct we know that for a point on both circles,
/// the line eval is 0. Here we go the other direction:
///   D1 - D2 ≡ E + K  (same algebraic expansion as in lemma_radical_axis_correct)
///   L.c ≡ K - R  where K = c1_sq - c2_sq, R = r1sq - r2sq
///   E + L.c ≡ 0  (point on line)
///   So E + K - R ≡ 0, i.e., E + K ≡ R = r1sq - r2sq
///   D1 - D2 ≡ E + K ≡ r1sq - r2sq
///   D1 ≡ r1sq → D2 ≡ r2sq
pub proof fn lemma_radical_axis_reverse<T: Ring>(
    c1: Circle2<T>, c2: Circle2<T>, p: Point2<T>,
)
    requires
        point_on_circle2(c1, p),
        point_on_line2(radical_axis(c1, c2), p),
    ensures
        point_on_circle2(c2, p),
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

    let t = two::<T>();
    let la = t.mul(c2x.sub(c1x));
    let lb = t.mul(c2y.sub(c1y));
    let c1_sq = c1x.mul(c1x).add(c1y.mul(c1y));
    let c2_sq = c2x.mul(c2x).add(c2y.mul(c2y));
    let lc = c1_sq.sub(r1sq).sub(c2_sq.sub(r2sq));
    let e = la.mul(px).add(lb.mul(py));

    let xd1 = px.sub(c1x).mul(px.sub(c1x));
    let yd1 = py.sub(c1y).mul(py.sub(c1y));
    let xd2 = px.sub(c2x).mul(px.sub(c2x));
    let yd2 = py.sub(c2y).mul(py.sub(c2y));
    let d1 = xd1.add(yd1);
    let d2 = xd2.add(yd2);

    // --- Reproduce the algebraic expansion: D1 - D2 ≡ E + K ---
    // (Same chain as lemma_radical_axis_correct steps 2-7)
    lemma_sum_sub_rearrange::<T>(xd1, yd1, xd2, yd2);

    lemma_sq_diff::<T>(px, c1x, c2x);
    let ax = t.mul(c2x.sub(c1x)).mul(px);
    let kx = c1x.mul(c1x).sub(c2x.mul(c2x));

    lemma_sq_diff::<T>(py, c1y, c2y);
    let by_ = t.mul(c2y.sub(c1y)).mul(py);
    let ky = c1y.mul(c1y).sub(c2y.mul(c2y));

    additive_group_lemmas::lemma_add_congruence::<T>(
        xd1.sub(xd2), ax.add(kx),
        yd1.sub(yd2), by_.add(ky),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(ax, kx, by_, ky);
    lemma_diff_sum_rearrange::<T>(c1x.mul(c1x), c2x.mul(c2x), c1y.mul(c1y), c2y.mul(c2y));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        ax.add(by_), kx.add(ky), c1_sq.sub(c2_sq),
    );

    let k = c1_sq.sub(c2_sq);

    // Chain: D1-D2 ≡ E + K
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
        e.add(k),
    );
    // d1.sub(d2).eqv(e.add(k))

    // --- From line equation: E + L.c ≡ 0 ---
    // point_on_line2 gives: e.add(lc).eqv(T::zero())

    // --- L.c ≡ K - R via sub_sub_rearrange ---
    let r = r1sq.sub(r2sq);
    lemma_sub_sub_rearrange::<T>(c1_sq, r1sq, c2_sq, r2sq);
    // lc ≡ k.sub(r)

    // --- E + L.c ≡ E + (K - R) ≡ (E + K) - R ---
    additive_group_lemmas::lemma_add_congruence_right::<T>(e, lc, k.sub(r));
    lemma_add_sub_assoc::<T>(e, k, r);
    T::axiom_eqv_transitive(e.add(lc), e.add(k.sub(r)), e.add(k).sub(r));
    // e.add(lc).eqv(e.add(k).sub(r))

    // --- (E + K) - R ≡ 0 (from E + L.c ≡ 0) ---
    T::axiom_eqv_symmetric(e.add(lc), e.add(k).sub(r));
    T::axiom_eqv_transitive(e.add(k).sub(r), e.add(lc), T::zero());
    // e.add(k).sub(r).eqv(T::zero())

    // --- E + K ≡ R (from (E+K) - R ≡ 0) ---
    // (E+K) - R ≡ 0 → (E+K) ≡ R
    crate::collinearity::lemma_sub_zero_implies_eqv::<T>(e.add(k), r);

    // --- D1 - D2 ≡ R = r1sq - r2sq ---
    T::axiom_eqv_transitive(d1.sub(d2), e.add(k), r);
    // d1.sub(d2).eqv(r1sq.sub(r2sq))

    // --- D1 ≡ r1sq (from point_on_circle2(c1, p)) ---
    // D2 ≡ r2sq follows: D1 - D2 ≡ r1sq - r2sq and D1 ≡ r1sq
    // → r1sq - D2 ≡ r1sq - r2sq → D2 ≡ r2sq

    // D1 ≡ r1sq → (r1sq - D2) ≡ (D1 - D2) ≡ (r1sq - r2sq)
    T::axiom_eqv_reflexive(d2);
    additive_group_lemmas::lemma_sub_congruence::<T>(d1, r1sq, d2, d2);
    // d1.sub(d2).eqv(r1sq.sub(d2))
    T::axiom_eqv_symmetric(d1.sub(d2), r1sq.sub(d2));
    T::axiom_eqv_transitive(r1sq.sub(d2), d1.sub(d2), r1sq.sub(r2sq));
    // r1sq.sub(d2).eqv(r1sq.sub(r2sq))

    // Cancel r1sq: r1sq - D2 ≡ r1sq - r2sq → D2 ≡ r2sq
    // Use: if a - b ≡ a - c then b ≡ c (by adding a to both sides and cancelling)
    // a - b ≡ a - c → -(a - b) ≡ -(a - c) → b - a ≡ c - a
    // → (b - a) + a ≡ (c - a) + a → b ≡ c
    additive_group_lemmas::lemma_neg_congruence::<T>(r1sq.sub(d2), r1sq.sub(r2sq));
    // r1sq.sub(d2).neg().eqv(r1sq.sub(r2sq).neg())
    additive_group_lemmas::lemma_neg_sub::<T>(r1sq, d2);
    // r1sq.sub(d2).neg().eqv(d2.sub(r1sq))
    additive_group_lemmas::lemma_neg_sub::<T>(r1sq, r2sq);
    // r1sq.sub(r2sq).neg().eqv(r2sq.sub(r1sq))

    // d2.sub(r1sq) ≡ -(r1sq-d2) ≡ -(r1sq-r2sq) ≡ r2sq-r1sq
    T::axiom_eqv_symmetric(r1sq.sub(d2).neg(), d2.sub(r1sq));
    T::axiom_eqv_transitive(d2.sub(r1sq), r1sq.sub(d2).neg(), r1sq.sub(r2sq).neg());
    T::axiom_eqv_transitive(d2.sub(r1sq), r1sq.sub(r2sq).neg(), r2sq.sub(r1sq));
    // d2.sub(r1sq).eqv(r2sq.sub(r1sq))

    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(d2, r1sq);
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(r2sq, r1sq);
    T::axiom_add_congruence_left(d2.sub(r1sq), r2sq.sub(r1sq), r1sq);
    T::axiom_eqv_transitive(d2.sub(r1sq).add(r1sq), r2sq.sub(r1sq).add(r1sq), r2sq);
    T::axiom_eqv_symmetric(d2.sub(r1sq).add(r1sq), d2);
    T::axiom_eqv_transitive(d2, d2.sub(r1sq).add(r1sq), r2sq);
    // d2.eqv(r2sq) — this is point_on_circle2(c2, p)!
}

/// Given D1 ≡ r1sq, D1 - D2 ≡ r1sq - r2sq, derive D2 ≡ r2sq.
/// This is the core algebraic step for the reverse direction.
pub proof fn lemma_on_c2_from_dist_diff<T: Ring>(
    d1: T, d2: T, r1sq: T, r2sq: T,
)
    requires
        d1.eqv(r1sq),                     // point on c1
        d1.sub(d2).eqv(r1sq.sub(r2sq)),   // dist difference = radius difference
    ensures
        d2.eqv(r2sq),                      // point on c2
{
    // D1 ≡ r1sq → r1sq - D2 ≡ D1 - D2 ≡ r1sq - r2sq
    T::axiom_eqv_reflexive(d2);
    additive_group_lemmas::lemma_sub_congruence::<T>(d1, r1sq, d2, d2);
    T::axiom_eqv_symmetric(d1.sub(d2), r1sq.sub(d2));
    T::axiom_eqv_transitive(r1sq.sub(d2), d1.sub(d2), r1sq.sub(r2sq));

    // r1sq - D2 ≡ r1sq - r2sq → D2 ≡ r2sq
    additive_group_lemmas::lemma_neg_congruence::<T>(r1sq.sub(d2), r1sq.sub(r2sq));
    additive_group_lemmas::lemma_neg_sub::<T>(r1sq, d2);
    additive_group_lemmas::lemma_neg_sub::<T>(r1sq, r2sq);
    T::axiom_eqv_symmetric(r1sq.sub(d2).neg(), d2.sub(r1sq));
    T::axiom_eqv_transitive(d2.sub(r1sq), r1sq.sub(d2).neg(), r1sq.sub(r2sq).neg());
    T::axiom_eqv_transitive(d2.sub(r1sq), r1sq.sub(r2sq).neg(), r2sq.sub(r1sq));

    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(d2, r1sq);
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(r2sq, r1sq);
    T::axiom_add_congruence_left(d2.sub(r1sq), r2sq.sub(r1sq), r1sq);
    T::axiom_eqv_transitive(d2.sub(r1sq).add(r1sq), r2sq.sub(r1sq).add(r1sq), r2sq);
    T::axiom_eqv_symmetric(d2.sub(r1sq).add(r1sq), d2);
    T::axiom_eqv_transitive(d2, d2.sub(r1sq).add(r1sq), r2sq);
}

/// If two lines have equivalent coefficients, point_on_line2 transfers.
pub proof fn lemma_point_on_line2_congruence<T: Ring>(
    l1: Line2<T>, l2: Line2<T>, p: Point2<T>,
)
    requires
        l1.a.eqv(l2.a),
        l1.b.eqv(l2.b),
        l1.c.eqv(l2.c),
        point_on_line2(l1, p),
    ensures
        point_on_line2(l2, p),
{
    // l1.a*p.x + l1.b*p.y + l1.c ≡ 0
    // Need: l2.a*p.x + l2.b*p.y + l2.c ≡ 0
    // By congruence: l1.a ≡ l2.a → l1.a*p.x ≡ l2.a*p.x, etc.
    T::axiom_mul_congruence_left(l1.a, l2.a, p.x);
    T::axiom_mul_congruence_left(l1.b, l2.b, p.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        l1.a.mul(p.x), l2.a.mul(p.x),
        l1.b.mul(p.y), l2.b.mul(p.y),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        l1.a.mul(p.x).add(l1.b.mul(p.y)), l2.a.mul(p.x).add(l2.b.mul(p.y)),
        l1.c, l2.c,
    );
    // l1 eval ≡ l2 eval, and l1 eval ≡ 0
    T::axiom_eqv_symmetric(
        l1.a.mul(p.x).add(l1.b.mul(p.y)).add(l1.c),
        l2.a.mul(p.x).add(l2.b.mul(p.y)).add(l2.c),
    );
    T::axiom_eqv_transitive(
        l2.a.mul(p.x).add(l2.b.mul(p.y)).add(l2.c),
        l1.a.mul(p.x).add(l1.b.mul(p.y)).add(l1.c),
        T::zero(),
    );
}

/// Helper: qext_from_rational(a) ≡_QE qext_from_rational(b) when a ≡_F b
pub proof fn lemma_rational_congruence<F: Field, R: Radicand<F>>(a: F, b: F)
    requires
        a.eqv(b),
    ensures
        qext_from_rational::<F, R>(a).eqv(qext_from_rational::<F, R>(b)),
{
    F::axiom_eqv_reflexive(F::zero());
}

/// The lifted radical axis line has QE-eqv coefficients to radical_axis(c1_qe, c2_qe).
///
/// Specifically: lift_line2(radical_axis(c1,c2)) coefficients are eqv to
/// radical_axis(lift_circle(c1), lift_circle(c2)) coefficients.
///
/// We prove the simpler fact: point_on_line2(radical_axis(c1_qe, c2_qe), p)
/// follows from point_on_line2(lift_line2(radical_axis(c1, c2)), p), by
/// showing the three coefficients are eqv.
pub proof fn lemma_lift_radical_axis_bridge<F: OrderedField, R: PositiveRadicand<F>>(
    c1: Circle2<F>, c2: Circle2<F>,
    p: Point2<SpecQuadExt<F, R>>,
)
    requires
        point_on_line2(
            lift_line2::<F, R>(radical_axis(c1, c2)),
            p,
        ),
    ensures
        point_on_line2(
            radical_axis(
                Circle2 { center: lift_point2::<F, R>(c1.center), radius_sq: qext_from_rational::<F, R>(c1.radius_sq) },
                Circle2 { center: lift_point2::<F, R>(c2.center), radius_sq: qext_from_rational::<F, R>(c2.radius_sq) },
            ),
            p,
        ),
{
    // QE = SpecQuadExt<F, R>
    let c1_qe = Circle2 {
        center: lift_point2::<F, R>(c1.center),
        radius_sq: qext_from_rational::<F, R>(c1.radius_sq),
    };
    let c2_qe = Circle2 {
        center: lift_point2::<F, R>(c2.center),
        radius_sq: qext_from_rational::<F, R>(c2.radius_sq),
    };

    let l_f = radical_axis(c1, c2);
    let l_lift = lift_line2::<F, R>(l_f);
    let l_qe = radical_axis(c1_qe, c2_qe);

    // --- Show l_lift.a ≡ l_qe.a ---
    // l_f.a = two::<F>().mul(c2x.sub(c1x))
    // l_lift.a = qext_from_rational(l_f.a)
    // l_qe.a = two::<SpecQuadExt<F, R>>().mul(c2x_qe.sub(c1x_qe))
    //        = QE::one().add(QE::one()).mul(qext_from_rational(c2x).sub(qext_from_rational(c1x)))

    // rational(one) ≡ QE::one  (definitionally qext(one, zero))
    lemma_rational_one::<F, R>();
    // rational(one + one) ≡ rational(one) + rational(one) ≡ QE::one + QE::one = two_qe
    lemma_rational_add::<F, R>(F::one(), F::one());
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(F::one().add(F::one())),
        qe_add::<F, R>(qext_from_rational(F::one()), qext_from_rational(F::one())),
    );
    // two_qe ≡ QE::one().add(QE::one()) by definition
    // qe_add(rational(one), rational(one)) ≡ QE::one().add(QE::one()) since rational(one) ≡ QE::one
    SpecQuadExt::<F, R>::axiom_add_congruence_left(
        qext_from_rational::<F, R>(F::one()), SpecQuadExt::<F, R>::one(), qext_from_rational(F::one()),
    );
    additive_group_lemmas::lemma_add_congruence_right::<SpecQuadExt<F, R>>(
        SpecQuadExt::<F, R>::one(), qext_from_rational(F::one()), SpecQuadExt::<F, R>::one(),
    );
    let two_f = two::<F>();
    let two_qe_computed = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());

    // rational(two) ≡ two_qe_computed
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(two_f),
        qe_add::<F, R>(qext_from_rational(F::one()), qext_from_rational(F::one())),
        two_qe_computed,
    );

    // rational(c2x - c1x) ≡ rational(c2x) - rational(c1x)
    lemma_rational_sub::<F, R>(c2.center.x, c1.center.x);

    // rational(two * (c2x-c1x)) ≡ rational(two) * rational(c2x-c1x) ≡ two_qe * diff_qe ≡ l_qe.a
    lemma_rational_mul::<F, R>(two_f, c2.center.x.sub(c1.center.x));

    // Bridge: rational(two) ≡ two_qe_computed and rational(diff) ≡ qe_sub(rational(c2x), rational(c1x))
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(two_f), two_qe_computed,
        qext_from_rational::<F, R>(c2.center.x.sub(c1.center.x)),
        qe_sub::<F, R>(qext_from_rational(c2.center.x), qext_from_rational(c1.center.x)),
    );
    // qe_mul(rational(two), rational(diff)) ≡ l_qe.a
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(l_f.a),
        qe_mul::<F, R>(qext_from_rational(two_f), qext_from_rational(c2.center.x.sub(c1.center.x))),
        two_qe_computed.mul(qe_sub::<F, R>(qext_from_rational(c2.center.x), qext_from_rational(c1.center.x))),
    );
    // l_lift.a ≡ l_qe.a

    // --- Show l_lift.b ≡ l_qe.b (same structure) ---
    lemma_rational_sub::<F, R>(c2.center.y, c1.center.y);
    lemma_rational_mul::<F, R>(two_f, c2.center.y.sub(c1.center.y));
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(two_f), two_qe_computed,
        qext_from_rational::<F, R>(c2.center.y.sub(c1.center.y)),
        qe_sub::<F, R>(qext_from_rational(c2.center.y), qext_from_rational(c1.center.y)),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(l_f.b),
        qe_mul::<F, R>(qext_from_rational(two_f), qext_from_rational(c2.center.y.sub(c1.center.y))),
        two_qe_computed.mul(qe_sub::<F, R>(qext_from_rational(c2.center.y), qext_from_rational(c1.center.y))),
    );

    // --- Show l_lift.c ≡ l_qe.c ---
    // l_f.c = (c1_sq - r1sq) - (c2_sq - r2sq)
    // where c1_sq = c1x*c1x + c1y*c1y
    let c1x = c1.center.x;
    let c1y = c1.center.y;
    let c2x = c2.center.x;
    let c2y = c2.center.y;

    // Build c1_sq: rational(c1x*c1x) ≡ rational(c1x)*rational(c1x)
    lemma_rational_mul::<F, R>(c1x, c1x);
    lemma_rational_mul::<F, R>(c1y, c1y);
    lemma_rational_add::<F, R>(c1x.mul(c1x), c1y.mul(c1y));
    // rational(c1_sq) ≡ rational(c1x*c1x) + rational(c1y*c1y)
    //                  ≡ (rational(c1x)*rational(c1x)) + (rational(c1y)*rational(c1y))
    let c1_sq_f = c1x.mul(c1x).add(c1y.mul(c1y));
    let c1xx_qe = qe_mul::<F, R>(qext_from_rational(c1x), qext_from_rational(c1x));
    let c1yy_qe = qe_mul::<F, R>(qext_from_rational(c1y), qext_from_rational(c1y));
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(c1x.mul(c1x)), c1xx_qe,
        qext_from_rational::<F, R>(c1y.mul(c1y)), c1yy_qe,
    );
    let c1_sq_qe = c1xx_qe.add(c1yy_qe);
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(c1_sq_f),
        qe_add::<F, R>(qext_from_rational(c1x.mul(c1x)), qext_from_rational(c1y.mul(c1y))),
        c1_sq_qe,
    );

    // Same for c2_sq
    lemma_rational_mul::<F, R>(c2x, c2x);
    lemma_rational_mul::<F, R>(c2y, c2y);
    lemma_rational_add::<F, R>(c2x.mul(c2x), c2y.mul(c2y));
    let c2_sq_f = c2x.mul(c2x).add(c2y.mul(c2y));
    let c2xx_qe = qe_mul::<F, R>(qext_from_rational(c2x), qext_from_rational(c2x));
    let c2yy_qe = qe_mul::<F, R>(qext_from_rational(c2y), qext_from_rational(c2y));
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(c2x.mul(c2x)), c2xx_qe,
        qext_from_rational::<F, R>(c2y.mul(c2y)), c2yy_qe,
    );
    let c2_sq_qe = c2xx_qe.add(c2yy_qe);
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(c2_sq_f),
        qe_add::<F, R>(qext_from_rational(c2x.mul(c2x)), qext_from_rational(c2y.mul(c2y))),
        c2_sq_qe,
    );

    // c1_sq - r1sq
    lemma_rational_sub::<F, R>(c1_sq_f, c1.radius_sq);
    let r1sq_qe = qext_from_rational::<F, R>(c1.radius_sq);
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(r1sq_qe);
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(c1_sq_f), c1_sq_qe,
        r1sq_qe, r1sq_qe,
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(c1_sq_f.sub(c1.radius_sq)),
        qe_sub::<F, R>(qext_from_rational(c1_sq_f), r1sq_qe),
        c1_sq_qe.sub(r1sq_qe),
    );

    // c2_sq - r2sq
    lemma_rational_sub::<F, R>(c2_sq_f, c2.radius_sq);
    let r2sq_qe = qext_from_rational::<F, R>(c2.radius_sq);
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(r2sq_qe);
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(c2_sq_f), c2_sq_qe,
        r2sq_qe, r2sq_qe,
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(c2_sq_f.sub(c2.radius_sq)),
        qe_sub::<F, R>(qext_from_rational(c2_sq_f), r2sq_qe),
        c2_sq_qe.sub(r2sq_qe),
    );

    // (c1_sq - r1sq) - (c2_sq - r2sq)
    lemma_rational_sub::<F, R>(c1_sq_f.sub(c1.radius_sq), c2_sq_f.sub(c2.radius_sq));
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(c1_sq_f.sub(c1.radius_sq)), c1_sq_qe.sub(r1sq_qe),
        qext_from_rational::<F, R>(c2_sq_f.sub(c2.radius_sq)), c2_sq_qe.sub(r2sq_qe),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(l_f.c),
        qe_sub::<F, R>(
            qext_from_rational(c1_sq_f.sub(c1.radius_sq)),
            qext_from_rational(c2_sq_f.sub(c2.radius_sq)),
        ),
        c1_sq_qe.sub(r1sq_qe).sub(c2_sq_qe.sub(r2sq_qe)),
    );

    // Now apply lemma_point_on_line2_congruence
    lemma_point_on_line2_congruence::<SpecQuadExt<F, R>>(l_lift, l_qe, p);
}

} // verus!
