use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::{dot, scale, norm_sq};
use verus_linalg::vec3::ops::{
    lemma_dot_distributes_right, lemma_dot_scale_right,
    lemma_dot_neg_right, lemma_dot_congruence, lemma_scale_congruence,
};
use crate::point3::*;

verus! {

//  =========================================================================
//  Line-line closest approach specs
//  =========================================================================

///  Point on the line through a and b at parameter t: a + t*(b - a).
pub open spec fn line_point_3d<T: Ring>(
    a: Point3<T>, b: Point3<T>, t: T,
) -> Point3<T> {
    add_vec3(a, scale(t, sub3(b, a)))
}

///  The Gram matrix entries for lines (a,b) and (c,d).
///  u = b-a, v = d-c, w = a-c.
///  Returns (dot(u,u), dot(v,v), dot(u,v), dot(u,w), dot(v,w)).
pub open spec fn gram_entries<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> (T, T, T, T, T) {
    let u = sub3(b, a);
    let v = sub3(d, c);
    let w = sub3(a, c);
    (dot(u, u), dot(v, v), dot(u, v), dot(u, w), dot(v, w))
}

///  Denominator of the closest-approach system: |u|²|v|² - (u·v)².
///  This is zero iff the lines are parallel.
pub open spec fn gram_determinant<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (uu, vv, uv, _, _) = gram_entries(a, b, c, d);
    uu.mul(vv).sub(uv.mul(uv))
}

///  Closest-approach parameter on line (a,b):
///  s = (uv * vw - vv * uw) / denom
pub open spec fn closest_parameter_s<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (_, vv, uv, uw, vw) = gram_entries(a, b, c, d);
    let denom = gram_determinant(a, b, c, d);
    uv.mul(vw).sub(vv.mul(uw)).div(denom)
}

///  Closest-approach parameter on line (c,d):
///  t = (uu * vw - uv * uw) / denom
pub open spec fn closest_parameter_t<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let (uu, _, uv, uw, vw) = gram_entries(a, b, c, d);
    let denom = gram_determinant(a, b, c, d);
    uu.mul(vw).sub(uv.mul(uw)).div(denom)
}

///  Squared distance between the closest approach points on two lines.
pub open spec fn line_line_squared_distance<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> T {
    let s = closest_parameter_s(a, b, c, d);
    let t = closest_parameter_t(a, b, c, d);
    let p1 = line_point_3d(a, b, s);
    let p2 = line_point_3d(c, d, t);
    norm_sq(sub3(p1, p2))
}

//  =========================================================================
//  Proof helpers — scalar algebra
//  =========================================================================

///  (a + b) - a ≡ b. Derived from commutativity + lemma_add_then_sub_cancel.
pub proof fn lemma_add_sub_cancel_left<T: Ring>(a: T, b: T)
    ensures
        a.add(b).sub(a).eqv(b),
{
    T::axiom_add_commutative(a, b);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_sub_congruence(a.add(b), b.add(a), a, a);
    additive_group_lemmas::lemma_add_then_sub_cancel(b, a);
    T::axiom_eqv_transitive(a.add(b).sub(a), b.add(a).sub(a), b);
}

///  (a + b) - c ≡ (a - c) + b. Rearranges add/sub.
///  Re-derived from intersection3d (private there).
pub proof fn lemma_add_sub_rearrange<T: Ring>(a: T, b: T, c: T)
    ensures
        a.add(b).sub(c).eqv(a.sub(c).add(b)),
{
    //  a.add(b).sub(c) ≡ a.add(b).add(c.neg())
    T::axiom_sub_is_add_neg(a.add(b), c);
    //  a+b+(-c) ≡ a+(b+(-c)) ≡ a+((-c)+b) ≡ (a+(-c))+b
    T::axiom_add_associative(a, b, c.neg());
    T::axiom_add_commutative(b, c.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.add(c.neg()), c.neg().add(b));
    T::axiom_eqv_transitive(
        a.add(b).add(c.neg()),
        a.add(b.add(c.neg())),
        a.add(c.neg().add(b)),
    );
    T::axiom_add_associative(a, c.neg(), b);
    T::axiom_eqv_symmetric(a.add(c.neg()).add(b), a.add(c.neg().add(b)));
    T::axiom_eqv_transitive(
        a.add(b).add(c.neg()),
        a.add(c.neg().add(b)),
        a.add(c.neg()).add(b),
    );
    //  Chain from sub form
    T::axiom_eqv_transitive(
        a.add(b).sub(c),
        a.add(b).add(c.neg()),
        a.add(c.neg()).add(b),
    );
    //  a.add(c.neg()) ≡ a.sub(c)
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    T::axiom_add_congruence_left(a.add(c.neg()), a.sub(c), b);
    T::axiom_eqv_transitive(
        a.add(b).sub(c),
        a.add(c.neg()).add(b),
        a.sub(c).add(b),
    );
}

///  (a/b) * c ≡ (a*c) / b for nonzero b.
pub proof fn lemma_div_mul_right<T: OrderedField>(a: T, b: T, c: T)
    requires
        !b.eqv(T::zero()),
    ensures
        a.div(b).mul(c).eqv(a.mul(c).div(b)),
{
    //  Forward: (a/b)*c = (a*recip(b))*c = a*(recip(b)*c) = a*(c*recip(b)) = (a*c)*recip(b) = (a*c)/b
    T::axiom_div_is_mul_recip(a, b);
    T::axiom_eqv_reflexive(c);
    ring_lemmas::lemma_mul_congruence(a.div(b), a.mul(b.recip()), c, c);
    //  (a/b)*c ≡ a.mul(b.recip()).mul(c)
    T::axiom_mul_associative(a, b.recip(), c);
    T::axiom_eqv_transitive(
        a.div(b).mul(c),
        a.mul(b.recip()).mul(c),
        a.mul(b.recip().mul(c)),
    );
    T::axiom_mul_commutative(b.recip(), c);
    T::axiom_eqv_reflexive(a);
    ring_lemmas::lemma_mul_congruence(a, a, b.recip().mul(c), c.mul(b.recip()));
    T::axiom_eqv_transitive(
        a.div(b).mul(c),
        a.mul(b.recip().mul(c)),
        a.mul(c.mul(b.recip())),
    );
    //  Reverse from (a*c)/b
    T::axiom_mul_associative(a, c, b.recip());
    T::axiom_eqv_symmetric(a.mul(c).mul(b.recip()), a.mul(c.mul(b.recip())));
    T::axiom_div_is_mul_recip(a.mul(c), b);
    T::axiom_eqv_transitive(
        a.mul(c).div(b),
        a.mul(c).mul(b.recip()),
        a.mul(c.mul(b.recip())),
    );
    T::axiom_eqv_symmetric(a.mul(c).div(b), a.mul(c.mul(b.recip())));
    T::axiom_eqv_transitive(
        a.div(b).mul(c),
        a.mul(c.mul(b.recip())),
        a.mul(c).div(b),
    );
}

///  a ≡ b implies a/c ≡ b/c. Derived from div_is_mul_recip + congruence.
pub proof fn lemma_div_congruence_numerator<T: OrderedField>(a: T, b: T, c: T)
    requires
        a.eqv(b),
    ensures
        a.div(c).eqv(b.div(c)),
{
    T::axiom_div_is_mul_recip(a, c);
    T::axiom_div_is_mul_recip(b, c);
    T::axiom_eqv_reflexive(c.recip());
    ring_lemmas::lemma_mul_congruence(a, b, c.recip(), c.recip());
    //  a*recip(c) ≡ b*recip(c)
    T::axiom_eqv_symmetric(a.div(c), a.mul(c.recip()));
    T::axiom_eqv_transitive(a.div(c), a.mul(c.recip()), b.mul(c.recip()));
    //  b.div(c) ≡ b*recip(c), so symmetric: b*recip(c) ≡ b.div(c)... no,
    //  axiom gives b.div(c).eqv(b.mul(c.recip())), need symmetric for the other direction
    T::axiom_eqv_symmetric(b.div(c), b.mul(c.recip()));
    T::axiom_eqv_transitive(a.div(c), b.mul(c.recip()), b.div(c));
}

//  =========================================================================
//  Numerator identities
//  =========================================================================
//
//  ns = uv*vw - vv*uw   (numerator of s)
//  nt = uu*vw - uv*uw   (numerator of t)
//  D  = uu*vv - uv*uv   (Gram determinant)
//
//  We prove:
//    eq1: ns*uu + D*uw ≡ nt*uv
//    eq2: ns*uv + D*vw ≡ nt*vv
//
//  Strategy: expand both products using distributivity, show the middle
//  terms cancel by commutativity, then factor the remainder.

///  Numerator identity 1: ns*uu + D*uw ≡ nt*uv.
pub proof fn lemma_numerator_eq1<T: Ring>(uu: T, vv: T, uv: T, uw: T, vw: T)
    ensures ({
        let ns = uv.mul(vw).sub(vv.mul(uw));
        let nt = uu.mul(vw).sub(uv.mul(uw));
        let dd = uu.mul(vv).sub(uv.mul(uv));
        ns.mul(uu).add(dd.mul(uw)).eqv(nt.mul(uv))
    }),
{
    let ns = uv.mul(vw).sub(vv.mul(uw));
    let nt = uu.mul(vw).sub(uv.mul(uw));
    let dd = uu.mul(vv).sub(uv.mul(uv));

    //  Step 1: Expand ns*uu = (uv*vw - vv*uw)*uu = uv*vw*uu - vv*uw*uu
    ring_lemmas::lemma_mul_distributes_over_sub(uu, uv.mul(vw), vv.mul(uw));
    T::axiom_mul_commutative(ns, uu);
    //  ns*uu ≡ uu*ns ≡ uu*(uv*vw) - uu*(vv*uw)
    T::axiom_eqv_transitive(
        ns.mul(uu), uu.mul(ns), uu.mul(uv.mul(vw)).sub(uu.mul(vv.mul(uw))),
    );
    let x = uu.mul(uv.mul(vw));
    let a = uu.mul(vv.mul(uw));

    //  Step 2: Expand D*uw = (uu*vv - uv*uv)*uw = uu*vv*uw - uv*uv*uw
    ring_lemmas::lemma_mul_distributes_over_sub(uw, uu.mul(vv), uv.mul(uv));
    T::axiom_mul_commutative(dd, uw);
    T::axiom_eqv_transitive(
        dd.mul(uw), uw.mul(dd), uw.mul(uu.mul(vv)).sub(uw.mul(uv.mul(uv))),
    );
    let b = uw.mul(uu.mul(vv));
    let y = uw.mul(uv.mul(uv));

    //  Step 3: Show a ≡ b (the cancellation pair)
    //  a = uu*(vv*uw), b = uw*(uu*vv)
    //  uu*(vv*uw) = (uu*vv)*uw [assoc] = uw*(uu*vv) [comm]
    T::axiom_mul_associative(uu, vv, uw);
    T::axiom_mul_commutative(uu.mul(vv).mul(uw), b);  //  wrong approach
    //  Let me do this properly:
    //  a = uu.mul(vv.mul(uw))
    //  (uu*vv)*uw by assoc (backwards): uu*(vv*uw) ≡ wait, assoc gives (uu*vv)*uw ≡ uu*(vv*uw)
    //  So uu*(vv*uw) is the nested form. By symmetric: a ≡ (uu*vv)*uw
    T::axiom_eqv_symmetric(uu.mul(vv).mul(uw), uu.mul(vv.mul(uw)));
    //  (uu*vv)*uw ≡ uw*(uu*vv) [comm]
    T::axiom_mul_commutative(uu.mul(vv), uw);
    //  Chain: a ≡ (uu*vv)*uw ≡ uw*(uu*vv) = b
    T::axiom_eqv_transitive(a, uu.mul(vv).mul(uw), b);

    //  Step 4: Use a ≡ b to convert (b - y) into (a - y)
    T::axiom_eqv_symmetric(a, b);  //  b ≡ a
    T::axiom_eqv_reflexive(y);
    additive_group_lemmas::lemma_sub_congruence(b, a, y, y);
    //  b.sub(y) ≡ a.sub(y)

    //  Step 5: Congruence on the sum: (x-a) + (b-y) ≡ (x-a) + (a-y)
    T::axiom_eqv_reflexive(x.sub(a));
    additive_group_lemmas::lemma_add_congruence(
        x.sub(a), x.sub(a), b.sub(y), a.sub(y),
    );

    //  Step 6: Congruence on ns*uu + D*uw ≡ (x-a) + (b-y)
    additive_group_lemmas::lemma_add_congruence(
        ns.mul(uu), x.sub(a), dd.mul(uw), b.sub(y),
    );
    //  Chain to (x-a) + (a-y)
    T::axiom_eqv_transitive(
        ns.mul(uu).add(dd.mul(uw)),
        x.sub(a).add(b.sub(y)),
        x.sub(a).add(a.sub(y)),
    );

    //  Step 7: Telescope: (x-a) + (a-y) ≡ x-y
    additive_group_lemmas::lemma_sub_add_sub(x, a, y);
    T::axiom_eqv_transitive(
        ns.mul(uu).add(dd.mul(uw)),
        x.sub(a).add(a.sub(y)),
        x.sub(y),
    );

    //  Step 8: Factor x-y back to nt*uv
    //  x = uu*(uv*vw), y = uw*(uv*uv)
    //  x = uv*(uu*vw) [via assoc+comm]:
    //    uu*(uv*vw) ≡ (uu*uv)*vw [assoc backwards]
    T::axiom_mul_associative(uu, uv, vw);
    T::axiom_eqv_symmetric(uu.mul(uv).mul(vw), uu.mul(uv.mul(vw)));
    //    (uu*uv)*vw ≡ (uv*uu)*vw [comm on first pair]
    T::axiom_mul_commutative(uu, uv);
    T::axiom_eqv_reflexive(vw);
    ring_lemmas::lemma_mul_congruence(uu.mul(uv), uv.mul(uu), vw, vw);
    //    (uv*uu)*vw ≡ uv*(uu*vw) [assoc]
    T::axiom_mul_associative(uv, uu, vw);
    //  Chain: x ≡ uu.mul(uv).mul(vw) ≡ uv.mul(uu).mul(vw) ≡ uv*(uu*vw)
    T::axiom_eqv_transitive(x, uu.mul(uv).mul(vw), uv.mul(uu).mul(vw));
    T::axiom_eqv_transitive(x, uv.mul(uu).mul(vw), uv.mul(uu.mul(vw)));

    //  y = uw*(uv*uv) ≡ uv*(uw*uv) [assoc+comm]:
    //    uw*(uv*uv) ≡ (uw*uv)*uv [assoc backwards]
    T::axiom_mul_associative(uw, uv, uv);
    T::axiom_eqv_symmetric(uw.mul(uv).mul(uv), uw.mul(uv.mul(uv)));
    //    (uw*uv)*uv ≡ (uv*uw)*uv [comm on first pair]
    T::axiom_mul_commutative(uw, uv);
    T::axiom_eqv_reflexive(uv);
    ring_lemmas::lemma_mul_congruence(uw.mul(uv), uv.mul(uw), uv, uv);
    //    (uv*uw)*uv ≡ uv*(uw*uv) [assoc]
    T::axiom_mul_associative(uv, uw, uv);
    //  Chain: y ≡ uv*(uw*uv)
    T::axiom_eqv_transitive(y, uw.mul(uv).mul(uv), uv.mul(uw).mul(uv));
    T::axiom_eqv_transitive(y, uv.mul(uw).mul(uv), uv.mul(uw.mul(uv)));

    //  x - y ≡ uv*(uu*vw) - uv*(uw*uv) [sub_congruence]
    additive_group_lemmas::lemma_sub_congruence(x, uv.mul(uu.mul(vw)), y, uv.mul(uw.mul(uv)));
    //  Factor: uv*(uu*vw) - uv*(uw*uv) ≡ uv*(uu*vw - uw*uv) [distributes_over_sub backwards]
    ring_lemmas::lemma_mul_distributes_over_sub(uv, uu.mul(vw), uw.mul(uv));
    T::axiom_eqv_symmetric(
        uv.mul(uu.mul(vw).sub(uw.mul(uv))),
        uv.mul(uu.mul(vw)).sub(uv.mul(uw.mul(uv))),
    );
    T::axiom_eqv_transitive(
        x.sub(y),
        uv.mul(uu.mul(vw)).sub(uv.mul(uw.mul(uv))),
        uv.mul(uu.mul(vw).sub(uw.mul(uv))),
    );

    //  uu*vw - uw*uv ≡ nt = uu*vw - uv*uw
    //  Need: uw*uv ≡ uv*uw [comm]
    T::axiom_mul_commutative(uw, uv);
    T::axiom_eqv_reflexive(uu.mul(vw));
    additive_group_lemmas::lemma_sub_congruence(
        uu.mul(vw), uu.mul(vw), uw.mul(uv), uv.mul(uw),
    );
    //  uu*vw - uw*uv ≡ uu*vw - uv*uw = nt
    T::axiom_eqv_reflexive(uv);
    ring_lemmas::lemma_mul_congruence(
        uv, uv,
        uu.mul(vw).sub(uw.mul(uv)), uu.mul(vw).sub(uv.mul(uw)),
    );
    //  uv * (uu*vw - uw*uv) ≡ uv * (uu*vw - uv*uw) = uv*nt

    //  Chain: x-y ≡ uv*(uu*vw - uw*uv) ≡ uv*nt
    T::axiom_eqv_transitive(
        x.sub(y),
        uv.mul(uu.mul(vw).sub(uw.mul(uv))),
        uv.mul(uu.mul(vw).sub(uv.mul(uw))),
    );

    //  uv*nt ≡ nt*uv [comm]
    T::axiom_mul_commutative(uv, nt);
    T::axiom_eqv_transitive(x.sub(y), uv.mul(nt), nt.mul(uv));

    //  Final chain: ns*uu + D*uw ≡ x-y ≡ nt*uv
    T::axiom_eqv_transitive(
        ns.mul(uu).add(dd.mul(uw)),
        x.sub(y),
        nt.mul(uv),
    );
}

///  Numerator identity 2: ns*uv + D*vw ≡ nt*vv.
pub proof fn lemma_numerator_eq2<T: Ring>(uu: T, vv: T, uv: T, uw: T, vw: T)
    ensures ({
        let ns = uv.mul(vw).sub(vv.mul(uw));
        let nt = uu.mul(vw).sub(uv.mul(uw));
        let dd = uu.mul(vv).sub(uv.mul(uv));
        ns.mul(uv).add(dd.mul(vw)).eqv(nt.mul(vv))
    }),
{
    let ns = uv.mul(vw).sub(vv.mul(uw));
    let nt = uu.mul(vw).sub(uv.mul(uw));
    let dd = uu.mul(vv).sub(uv.mul(uv));

    //  Step 1: Expand ns*uv = (uv*vw - vv*uw)*uv = uv*vw*uv - vv*uw*uv
    ring_lemmas::lemma_mul_distributes_over_sub(uv, uv.mul(vw), vv.mul(uw));
    T::axiom_mul_commutative(ns, uv);
    T::axiom_eqv_transitive(
        ns.mul(uv), uv.mul(ns), uv.mul(uv.mul(vw)).sub(uv.mul(vv.mul(uw))),
    );
    let x = uv.mul(uv.mul(vw));
    let a = uv.mul(vv.mul(uw));

    //  Step 2: Expand D*vw = (uu*vv - uv*uv)*vw = uu*vv*vw - uv*uv*vw
    ring_lemmas::lemma_mul_distributes_over_sub(vw, uu.mul(vv), uv.mul(uv));
    T::axiom_mul_commutative(dd, vw);
    T::axiom_eqv_transitive(
        dd.mul(vw), vw.mul(dd), vw.mul(uu.mul(vv)).sub(vw.mul(uv.mul(uv))),
    );
    let b = vw.mul(uu.mul(vv));
    let y = vw.mul(uv.mul(uv));

    //  Step 3: Show x ≡ y (the cancellation pair)
    //  x = uv*(uv*vw), y = vw*(uv*uv)
    //  uv*(uv*vw) ≡ (uv*uv)*vw [assoc backwards]
    T::axiom_mul_associative(uv, uv, vw);
    T::axiom_eqv_symmetric(uv.mul(uv).mul(vw), uv.mul(uv.mul(vw)));
    //  (uv*uv)*vw ≡ vw*(uv*uv) [comm]
    T::axiom_mul_commutative(uv.mul(uv), vw);
    //  Chain: x ≡ (uv*uv)*vw ≡ vw*(uv*uv) = y
    T::axiom_eqv_transitive(x, uv.mul(uv).mul(vw), y);

    //  Step 4: Rewrite to (a - x) + (x - y) form, but we have (x - a) + (b - y).
    //  Since x ≡ y, we have b - y ≡ b - x. Also x - a is unchanged.
    //  Actually we want: (x - a) + (b - y) where x ≡ y.
    //  Convert to: (b - y) + (x - a) ≡ (b - x) + (x - a) ≡ b - a via sub_add_sub.
    //  Wait, let me just use the same approach as eq1.

    //  Convert (b-y) to (b-x) since y ≡ x:
    T::axiom_eqv_symmetric(x, y);  //  y ≡ x
    T::axiom_eqv_reflexive(b);
    additive_group_lemmas::lemma_sub_congruence(b, b, y, x);
    //  b - y ≡ b - x

    //  (x - a) + (b - y) ≡ (x - a) + (b - x) [congruence]
    T::axiom_eqv_reflexive(x.sub(a));
    additive_group_lemmas::lemma_add_congruence(
        x.sub(a), x.sub(a), b.sub(y), b.sub(x),
    );

    //  Commute: (x-a) + (b-x) ≡ (b-x) + (x-a) [add comm for Vec3... no, scalar]
    T::axiom_add_commutative(x.sub(a), b.sub(x));

    //  Telescope: (b-x) + (x-a) ≡ b-a
    additive_group_lemmas::lemma_sub_add_sub(b, x, a);
    T::axiom_eqv_transitive(
        x.sub(a).add(b.sub(x)),
        b.sub(x).add(x.sub(a)),
        b.sub(a),
    );

    //  Congruence: ns*uv + D*vw ≡ (x-a) + (b-y)
    additive_group_lemmas::lemma_add_congruence(
        ns.mul(uv), x.sub(a), dd.mul(vw), b.sub(y),
    );

    //  Chain to b - a
    T::axiom_eqv_transitive(
        ns.mul(uv).add(dd.mul(vw)),
        x.sub(a).add(b.sub(y)),
        x.sub(a).add(b.sub(x)),
    );
    T::axiom_eqv_transitive(
        ns.mul(uv).add(dd.mul(vw)),
        x.sub(a).add(b.sub(x)),
        b.sub(a),
    );

    //  Step 5: Show b - a ≡ nt*vv
    //  a = uv*(vv*uw), b = vw*(uu*vv)
    //  Factor out vv from both:
    //  a = uv*(vv*uw) ≡ (uv*vv)*uw [assoc backwards] ≡ (vv*uv)*uw [comm] ≡ vv*(uv*uw) [assoc]
    T::axiom_mul_associative(uv, vv, uw);
    T::axiom_eqv_symmetric(uv.mul(vv).mul(uw), uv.mul(vv.mul(uw)));
    T::axiom_mul_commutative(uv, vv);
    T::axiom_eqv_reflexive(uw);
    ring_lemmas::lemma_mul_congruence(uv.mul(vv), vv.mul(uv), uw, uw);
    //  (uv*vv)*uw ≡ (vv*uv)*uw
    T::axiom_mul_associative(vv, uv, uw);
    //  (vv*uv)*uw ≡ vv*(uv*uw)
    //  Chain: a ≡ (uv*vv)*uw ≡ (vv*uv)*uw ≡ vv*(uv*uw)
    T::axiom_eqv_transitive(a, uv.mul(vv).mul(uw), vv.mul(uv).mul(uw));
    T::axiom_eqv_transitive(a, vv.mul(uv).mul(uw), vv.mul(uv.mul(uw)));

    //  b = vw*(uu*vv) ≡ (uu*vv)*vw [comm] ≡ vv*(uu*vw) [assoc+comm on first pair... no]
    //  b = vw*(uu*vv) ≡ (vw*uu)*vv [assoc backwards]
    T::axiom_mul_associative(vw, uu, vv);
    T::axiom_eqv_symmetric(vw.mul(uu).mul(vv), vw.mul(uu.mul(vv)));
    //  (vw*uu)*vv ≡ (uu*vw)*vv [comm on first pair]
    T::axiom_mul_commutative(vw, uu);
    T::axiom_eqv_reflexive(vv);
    ring_lemmas::lemma_mul_congruence(vw.mul(uu), uu.mul(vw), vv, vv);
    //  (uu*vw)*vv ≡ vv*(uu*vw) [comm]
    T::axiom_mul_commutative(uu.mul(vw), vv);
    //  Chain: b ≡ vv*(uu*vw)
    T::axiom_eqv_transitive(b, vw.mul(uu).mul(vv), uu.mul(vw).mul(vv));
    T::axiom_eqv_transitive(b, uu.mul(vw).mul(vv), vv.mul(uu.mul(vw)));

    //  b - a ≡ vv*(uu*vw) - vv*(uv*uw)
    additive_group_lemmas::lemma_sub_congruence(b, vv.mul(uu.mul(vw)), a, vv.mul(uv.mul(uw)));
    //  Factor: vv*(uu*vw) - vv*(uv*uw) ≡ vv*(uu*vw - uv*uw) = vv*nt
    ring_lemmas::lemma_mul_distributes_over_sub(vv, uu.mul(vw), uv.mul(uw));
    T::axiom_eqv_symmetric(
        vv.mul(uu.mul(vw).sub(uv.mul(uw))),
        vv.mul(uu.mul(vw)).sub(vv.mul(uv.mul(uw))),
    );
    T::axiom_eqv_transitive(
        b.sub(a),
        vv.mul(uu.mul(vw)).sub(vv.mul(uv.mul(uw))),
        vv.mul(nt),
    );
    //  vv*nt ≡ nt*vv [comm]
    T::axiom_mul_commutative(vv, nt);
    T::axiom_eqv_transitive(b.sub(a), vv.mul(nt), nt.mul(vv));

    //  Final: ns*uv + D*vw ≡ b - a ≡ nt*vv
    T::axiom_eqv_transitive(
        ns.mul(uv).add(dd.mul(vw)),
        b.sub(a),
        nt.mul(vv),
    );
}

//  =========================================================================
//  Cramer equations: s*uu + uw ≡ t*uv, s*uv + vw ≡ t*vv
//  =========================================================================

///  Cramer equation 1: s*uu + uw ≡ t*uv, where s = ns/D, t = nt/D.
pub proof fn lemma_cramer_eq1<T: OrderedField>(uu: T, vv: T, uv: T, uw: T, vw: T)
    requires ({
        let dd = uu.mul(vv).sub(uv.mul(uv));
        !dd.eqv(T::zero())
    }),
    ensures ({
        let ns = uv.mul(vw).sub(vv.mul(uw));
        let nt = uu.mul(vw).sub(uv.mul(uw));
        let dd = uu.mul(vv).sub(uv.mul(uv));
        let s = ns.div(dd);
        let t = nt.div(dd);
        s.mul(uu).add(uw).eqv(t.mul(uv))
    }),
{
    let ns = uv.mul(vw).sub(vv.mul(uw));
    let nt = uu.mul(vw).sub(uv.mul(uw));
    let dd = uu.mul(vv).sub(uv.mul(uv));
    let s = ns.div(dd);
    let t = nt.div(dd);

    //  s*uu = (ns/D)*uu ≡ (ns*uu)/D
    lemma_div_mul_right(ns, dd, uu);

    //  D*uw/D ≡ uw
    T::axiom_mul_commutative(dd, uw);
    //  uw*D/D ≡ uw... no, we need (D*uw)/D ≡ uw
    //  lemma_mul_div_cancel(uw, D): (uw*D)/D ≡ uw
    field_lemmas::lemma_mul_div_cancel(uw, dd);
    //  (uw*D)/D ≡ uw, but we need uw ≡ (D*uw)/D
    //  D*uw ≡ uw*D [comm]
    lemma_div_congruence_numerator(dd.mul(uw), uw.mul(dd), dd);
    //  (D*uw)/D ≡ (uw*D)/D ≡ uw
    T::axiom_eqv_transitive(dd.mul(uw).div(dd), uw.mul(dd).div(dd), uw);
    T::axiom_eqv_symmetric(dd.mul(uw).div(dd), uw);
    //  uw ≡ (D*uw)/D

    //  s*uu + uw ≡ (ns*uu)/D + (D*uw)/D
    T::axiom_eqv_symmetric(uw, dd.mul(uw).div(dd));
    additive_group_lemmas::lemma_add_congruence(
        s.mul(uu), ns.mul(uu).div(dd),
        uw, dd.mul(uw).div(dd),
    );

    //  (ns*uu)/D + (D*uw)/D ≡ (ns*uu + D*uw)/D [div_distributes_over_add backwards]
    field_lemmas::lemma_div_distributes_over_add(ns.mul(uu), dd.mul(uw), dd);
    T::axiom_eqv_symmetric(
        ns.mul(uu).add(dd.mul(uw)).div(dd),
        ns.mul(uu).div(dd).add(dd.mul(uw).div(dd)),
    );
    T::axiom_eqv_transitive(
        s.mul(uu).add(uw),
        ns.mul(uu).div(dd).add(dd.mul(uw).div(dd)),
        ns.mul(uu).add(dd.mul(uw)).div(dd),
    );

    //  Numerator identity: ns*uu + D*uw ≡ nt*uv
    lemma_numerator_eq1(uu, vv, uv, uw, vw);
    lemma_div_congruence_numerator(ns.mul(uu).add(dd.mul(uw)), nt.mul(uv), dd);
    T::axiom_eqv_transitive(
        s.mul(uu).add(uw),
        ns.mul(uu).add(dd.mul(uw)).div(dd),
        nt.mul(uv).div(dd),
    );

    //  (nt*uv)/D ≡ (nt/D)*uv = t*uv [div_mul_right backwards]
    lemma_div_mul_right(nt, dd, uv);
    T::axiom_eqv_symmetric(t.mul(uv), nt.mul(uv).div(dd));
    T::axiom_eqv_transitive(
        s.mul(uu).add(uw),
        nt.mul(uv).div(dd),
        t.mul(uv),
    );
}

///  Cramer equation 2: s*uv + vw ≡ t*vv, where s = ns/D, t = nt/D.
pub proof fn lemma_cramer_eq2<T: OrderedField>(uu: T, vv: T, uv: T, uw: T, vw: T)
    requires ({
        let dd = uu.mul(vv).sub(uv.mul(uv));
        !dd.eqv(T::zero())
    }),
    ensures ({
        let ns = uv.mul(vw).sub(vv.mul(uw));
        let nt = uu.mul(vw).sub(uv.mul(uw));
        let dd = uu.mul(vv).sub(uv.mul(uv));
        let s = ns.div(dd);
        let t = nt.div(dd);
        s.mul(uv).add(vw).eqv(t.mul(vv))
    }),
{
    let ns = uv.mul(vw).sub(vv.mul(uw));
    let nt = uu.mul(vw).sub(uv.mul(uw));
    let dd = uu.mul(vv).sub(uv.mul(uv));
    let s = ns.div(dd);
    let t = nt.div(dd);

    //  s*uv ≡ (ns*uv)/D
    lemma_div_mul_right(ns, dd, uv);

    //  vw ≡ (D*vw)/D
    T::axiom_mul_commutative(dd, vw);
    field_lemmas::lemma_mul_div_cancel(vw, dd);
    lemma_div_congruence_numerator(dd.mul(vw), vw.mul(dd), dd);
    T::axiom_eqv_transitive(dd.mul(vw).div(dd), vw.mul(dd).div(dd), vw);
    T::axiom_eqv_symmetric(dd.mul(vw).div(dd), vw);
    T::axiom_eqv_symmetric(uw, uw);  //  dummy, will remove
    T::axiom_eqv_symmetric(vw, dd.mul(vw).div(dd));

    //  s*uv + vw ≡ (ns*uv)/D + (D*vw)/D
    additive_group_lemmas::lemma_add_congruence(
        s.mul(uv), ns.mul(uv).div(dd),
        vw, dd.mul(vw).div(dd),
    );

    //  ≡ (ns*uv + D*vw)/D
    field_lemmas::lemma_div_distributes_over_add(ns.mul(uv), dd.mul(vw), dd);
    T::axiom_eqv_symmetric(
        ns.mul(uv).add(dd.mul(vw)).div(dd),
        ns.mul(uv).div(dd).add(dd.mul(vw).div(dd)),
    );
    T::axiom_eqv_transitive(
        s.mul(uv).add(vw),
        ns.mul(uv).div(dd).add(dd.mul(vw).div(dd)),
        ns.mul(uv).add(dd.mul(vw)).div(dd),
    );

    //  Numerator identity: ns*uv + D*vw ≡ nt*vv
    lemma_numerator_eq2(uu, vv, uv, uw, vw);
    lemma_div_congruence_numerator(ns.mul(uv).add(dd.mul(vw)), nt.mul(vv), dd);
    T::axiom_eqv_transitive(
        s.mul(uv).add(vw),
        ns.mul(uv).add(dd.mul(vw)).div(dd),
        nt.mul(vv).div(dd),
    );

    //  (nt*vv)/D ≡ t*vv
    lemma_div_mul_right(nt, dd, vv);
    T::axiom_eqv_symmetric(t.mul(vv), nt.mul(vv).div(dd));
    T::axiom_eqv_transitive(
        s.mul(uv).add(vw),
        nt.mul(vv).div(dd),
        t.mul(vv),
    );
}

//  =========================================================================
//  Diff expansion: sub3(p1, p2) ≡ w + scale(s,u) - scale(t,v)
//  =========================================================================

///  Vector expansion: sub3(add_vec3(a, su), add_vec3(c, tv)) ≡ sub3(a,c).add(su).sub(tv)
///  where su, tv are arbitrary Vec3 offsets.
pub proof fn lemma_diff_expansion<T: Ring>(
    a: Point3<T>, c: Point3<T>, su: Vec3<T>, tv: Vec3<T>,
)
    ensures
        sub3(add_vec3(a, su), add_vec3(c, tv)).eqv(
            sub3(a, c).add(su).sub(tv)
        ),
{
    //  Component-wise: (a.x + su.x) - (c.x + tv.x) ≡ (a.x - c.x) + su.x - tv.x
    //  Using lemma_add_sub_rearrange twice:
    //    (a + su) - (c + tv)
    //    = ((a + su) - c) - tv        [rearrange: z - (c+tv) = (z-c) - tv... need helper]
    //  Actually let's use a different approach:
    //    (a + su) - (c + tv)
    //    step 1: = (a - c + su) - tv  [by lemma_add_sub_rearrange: (a+su)-c = (a-c)+su, then sub tv]
    //    But we're subtracting (c+tv), not c then tv.
    //  Let me do it per-component using two applications of existing lemmas.
    lemma_add_sub_add_scalar::<T>(a.x, su.x, c.x, tv.x);
    lemma_add_sub_add_scalar::<T>(a.y, su.y, c.y, tv.y);
    lemma_add_sub_add_scalar::<T>(a.z, su.z, c.z, tv.z);
}

///  Scalar helper: (a + p) - (b + q) ≡ (a - b) + p - q.
pub proof fn lemma_add_sub_add_scalar<T: Ring>(a: T, p: T, b: T, q: T)
    ensures
        a.add(p).sub(b.add(q)).eqv(a.sub(b).add(p).sub(q)),
{
    //  Step 1: (a+p) - (b+q) ≡ ((a+p) - b) - q
    //  First show: (a+p) - (b+q) ≡ (a+p) + (-(b+q))
    T::axiom_sub_is_add_neg(a.add(p), b.add(q));
    //  -(b+q) ≡ (-b) + (-q)
    additive_group_lemmas::lemma_neg_add::<T>(b, q);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(p), b.add(q).neg(), b.neg().add(q.neg()),
    );
    T::axiom_eqv_transitive(
        a.add(p).sub(b.add(q)),
        a.add(p).add(b.add(q).neg()),
        a.add(p).add(b.neg().add(q.neg())),
    );
    //  (a+p) + ((-b)+(-q)) ≡ ((a+p)+(-b)) + (-q) [assoc backwards]
    T::axiom_add_associative(a.add(p), b.neg(), q.neg());
    T::axiom_eqv_symmetric(
        a.add(p).add(b.neg()).add(q.neg()),
        a.add(p).add(b.neg().add(q.neg())),
    );
    T::axiom_eqv_transitive(
        a.add(p).sub(b.add(q)),
        a.add(p).add(b.neg().add(q.neg())),
        a.add(p).add(b.neg()).add(q.neg()),
    );
    //  (a+p)+(-b) ≡ (a+p)-b ≡ (a-b)+p [add_sub_rearrange]
    lemma_add_sub_rearrange::<T>(a, p, b);
    //  so ((a+p)+(-b))+(-q) ≡ ((a-b)+p)+(-q)
    //  First: (a+p)+(-b) ≡ (a+p)-b
    T::axiom_sub_is_add_neg(a.add(p), b);
    T::axiom_eqv_symmetric(a.add(p).sub(b), a.add(p).add(b.neg()));
    //  (a+p)-b ≡ (a-b)+p
    //  Chain: (a+p)+(-b) ≡ (a+p)-b ≡ (a-b)+p
    T::axiom_eqv_transitive(
        a.add(p).add(b.neg()),
        a.add(p).sub(b),
        a.sub(b).add(p),
    );
    //  Lift to: ((a+p)+(-b))+(-q) ≡ ((a-b)+p)+(-q)
    T::axiom_eqv_reflexive(q.neg());
    additive_group_lemmas::lemma_add_congruence(
        a.add(p).add(b.neg()), a.sub(b).add(p),
        q.neg(), q.neg(),
    );
    T::axiom_eqv_transitive(
        a.add(p).sub(b.add(q)),
        a.add(p).add(b.neg()).add(q.neg()),
        a.sub(b).add(p).add(q.neg()),
    );
    //  ((a-b)+p)+(-q) ≡ ((a-b)+p)-q
    T::axiom_sub_is_add_neg(a.sub(b).add(p), q);
    T::axiom_eqv_symmetric(a.sub(b).add(p).sub(q), a.sub(b).add(p).add(q.neg()));
    T::axiom_eqv_transitive(
        a.add(p).sub(b.add(q)),
        a.sub(b).add(p).add(q.neg()),
        a.sub(b).add(p).sub(q),
    );
}

//  =========================================================================
//  Main lemma: closest-approach perpendicularity
//  =========================================================================

///  For two non-parallel lines (a,b) and (c,d), the closest-approach
///  vector p1-p2 is orthogonal to both line directions u=b-a and v=d-c.
pub proof fn lemma_closest_points_perpendicular<T: OrderedField>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    requires
        !gram_determinant(a, b, c, d).eqv(T::zero()),
    ensures ({
        let s = closest_parameter_s(a, b, c, d);
        let t = closest_parameter_t(a, b, c, d);
        let p1 = line_point_3d(a, b, s);
        let p2 = line_point_3d(c, d, t);
        let diff = sub3(p1, p2);
        &&& dot(sub3(b, a), diff).eqv(T::zero())
        &&& dot(sub3(d, c), diff).eqv(T::zero())
    }),
{
    let u = sub3(b, a);
    let v = sub3(d, c);
    let w = sub3(a, c);
    let (uu_val, vv_val, uv_val, uw_val, vw_val) = gram_entries(a, b, c, d);
    let dd = gram_determinant(a, b, c, d);
    let s = closest_parameter_s(a, b, c, d);
    let t = closest_parameter_t(a, b, c, d);
    let su = scale(s, u);
    let tv = scale(t, v);
    let p1 = line_point_3d(a, b, s);
    let p2 = line_point_3d(c, d, t);
    let diff = sub3(p1, p2);

    //  Phase B: diff ≡ w.add(su).sub(tv)
    let decomposed = w.add(su).sub(tv);
    lemma_diff_expansion(a, c, su, tv);
    //  sub3(add_vec3(a, su), add_vec3(c, tv)) ≡ w.add(su).sub(tv)
    //  But diff = sub3(p1, p2) = sub3(add_vec3(a, scale(s, sub3(b,a))), add_vec3(c, scale(t, sub3(d,c))))
    //  which IS sub3(add_vec3(a, su), add_vec3(c, tv)) by definition. ✓

    //  Phase C1: dot(u, diff) ≡ 0
    //  Step 1: dot(u, diff) ≡ dot(u, decomposed) [congruence]
    Vec3::<T>::axiom_eqv_reflexive(u);
    lemma_dot_congruence(u, u, diff, decomposed);

    //  Step 2: Expand dot(u, decomposed) = dot(u, w.add(su).sub(tv))
    //  decomposed = w.add(su).sub(tv) ≡ w.add(su).add(tv.neg()) [sub_is_add_neg]
    Vec3::<T>::axiom_sub_is_add_neg(w.add(su), tv);
    Vec3::<T>::axiom_eqv_reflexive(u);
    lemma_dot_congruence(u, u, decomposed, w.add(su).add(tv.neg()));
    T::axiom_eqv_transitive(
        dot(u, diff),
        dot(u, decomposed),
        dot(u, w.add(su).add(tv.neg())),
    );

    //  dot(u, w.add(su).add(tv.neg())) ≡ dot(u, w.add(su)) + dot(u, tv.neg())
    lemma_dot_distributes_right(u, w.add(su), tv.neg());
    T::axiom_eqv_transitive(
        dot(u, diff),
        dot(u, w.add(su).add(tv.neg())),
        dot(u, w.add(su)).add(dot(u, tv.neg())),
    );

    //  dot(u, w.add(su)) ≡ dot(u, w) + dot(u, su) = uw + s*uu
    lemma_dot_distributes_right(u, w, su);
    lemma_dot_scale_right(s, u, u);
    //  dot(u, su) ≡ s * dot(u, u) = s*uu
    //  dot(u, w.add(su)) ≡ dot(u,w) + dot(u,su) ≡ uw + s*uu

    //  dot(u, tv.neg()) ≡ -dot(u, tv) ≡ -(t*uv)
    lemma_dot_neg_right(u, tv);
    lemma_dot_scale_right(t, u, v);
    //  dot(u, tv) ≡ t * dot(u, v) = t*uv
    //  dot(u, tv.neg()) ≡ -dot(u, tv) ≡ -(t*uv)

    //  Assemble: dot(u, diff) ≡ (uw + s*uu) + (-(t*uv))
    //  First chain dot(u, w.add(su)) to uw + s*uu
    T::axiom_eqv_reflexive(dot(u, w));
    additive_group_lemmas::lemma_add_congruence(
        dot(u, w), dot(u, w),
        dot(u, su), s.mul(dot(u, u)),
    );
    //  dot(u, w) + dot(u, su) ≡ dot(u, w) + s*dot(u,u)
    T::axiom_eqv_transitive(
        dot(u, w.add(su)),
        dot(u, w).add(dot(u, su)),
        dot(u, w).add(s.mul(dot(u, u))),
    );
    //  But uw_val = dot(u,w) and uu_val = dot(u,u) by definition, so these are the same terms.

    //  Now chain dot(u, tv.neg()) to -(t*uv)
    //  dot(u, tv.neg()) ≡ -dot(u, tv) [neg_right]
    //  dot(u, tv) ≡ t * dot(u, v) [scale_right] = t*uv_val
    additive_group_lemmas::lemma_neg_congruence(dot(u, tv), t.mul(dot(u, v)));
    T::axiom_eqv_transitive(
        dot(u, tv.neg()),
        dot(u, tv).neg(),
        t.mul(dot(u, v)).neg(),
    );

    //  Combine: (uw + s*uu) + (-(t*uv)) where uw = dot(u,w), uu = dot(u,u), uv = dot(u,v)
    additive_group_lemmas::lemma_add_congruence(
        dot(u, w.add(su)), dot(u, w).add(s.mul(dot(u, u))),
        dot(u, tv.neg()), t.mul(dot(u, v)).neg(),
    );
    //  dot(u,w.add(su)) + dot(u,tv.neg()) ≡ (uw + s*uu) + (-(t*uv))
    T::axiom_eqv_transitive(
        dot(u, diff),
        dot(u, w.add(su)).add(dot(u, tv.neg())),
        dot(u, w).add(s.mul(dot(u, u))).add(t.mul(dot(u, v)).neg()),
    );

    //  Convert add(neg) to sub: x + (-y) ≡ x - y
    let uw_plus_suu = dot(u, w).add(s.mul(dot(u, u)));
    let t_uv = t.mul(dot(u, v));
    T::axiom_sub_is_add_neg(uw_plus_suu, t_uv);
    T::axiom_eqv_symmetric(uw_plus_suu.sub(t_uv), uw_plus_suu.add(t_uv.neg()));
    T::axiom_eqv_transitive(
        dot(u, diff),
        uw_plus_suu.add(t_uv.neg()),
        uw_plus_suu.sub(t_uv),
    );

    //  Now show uw + s*uu - t*uv ≡ 0 using Cramer eq1
    //  Cramer eq1: s*uu + uw ≡ t*uv
    //  So uw + s*uu ≡ s*uu + uw [comm] ≡ t*uv
    T::axiom_add_commutative(dot(u, w), s.mul(dot(u, u)));
    //  uw_plus_suu = uw + s*uu ≡ s*uu + uw
    lemma_cramer_eq1(uu_val, vv_val, uv_val, uw_val, vw_val);
    //  s*uu + uw ≡ t*uv (where uu = dot(u,u), etc.)
    T::axiom_eqv_transitive(uw_plus_suu, s.mul(dot(u, u)).add(dot(u, w)), t_uv);

    //  uw_plus_suu ≡ t_uv, so uw_plus_suu - t_uv ≡ t_uv - t_uv ≡ 0
    T::axiom_eqv_reflexive(t_uv);
    additive_group_lemmas::lemma_sub_congruence(uw_plus_suu, t_uv, t_uv, t_uv);
    additive_group_lemmas::lemma_sub_self(t_uv);
    T::axiom_eqv_transitive(uw_plus_suu.sub(t_uv), t_uv.sub(t_uv), T::zero());

    //  Final chain for eq1: dot(u, diff) ≡ 0
    T::axiom_eqv_transitive(dot(u, diff), uw_plus_suu.sub(t_uv), T::zero());

    //  Phase C2: dot(v, diff) ≡ 0 (same structure)
    Vec3::<T>::axiom_eqv_reflexive(v);
    lemma_dot_congruence(v, v, diff, decomposed);
    Vec3::<T>::axiom_eqv_reflexive(v);
    lemma_dot_congruence(v, v, decomposed, w.add(su).add(tv.neg()));
    T::axiom_eqv_transitive(
        dot(v, diff),
        dot(v, decomposed),
        dot(v, w.add(su).add(tv.neg())),
    );

    lemma_dot_distributes_right(v, w.add(su), tv.neg());
    T::axiom_eqv_transitive(
        dot(v, diff),
        dot(v, w.add(su).add(tv.neg())),
        dot(v, w.add(su)).add(dot(v, tv.neg())),
    );

    lemma_dot_distributes_right(v, w, su);
    lemma_dot_scale_right(s, v, u);
    lemma_dot_neg_right(v, tv);
    lemma_dot_scale_right(t, v, v);

    //  dot(v, su) ≡ s * dot(v, u)
    //  dot(v, w.add(su)) ≡ dot(v,w) + dot(v,su) ≡ vw + s*dot(v,u)
    T::axiom_eqv_reflexive(dot(v, w));
    additive_group_lemmas::lemma_add_congruence(
        dot(v, w), dot(v, w),
        dot(v, su), s.mul(dot(v, u)),
    );
    T::axiom_eqv_transitive(
        dot(v, w.add(su)),
        dot(v, w).add(dot(v, su)),
        dot(v, w).add(s.mul(dot(v, u))),
    );

    //  dot(v, tv.neg()) ≡ -(t * dot(v,v))
    additive_group_lemmas::lemma_neg_congruence(dot(v, tv), t.mul(dot(v, v)));
    T::axiom_eqv_transitive(
        dot(v, tv.neg()),
        dot(v, tv).neg(),
        t.mul(dot(v, v)).neg(),
    );

    additive_group_lemmas::lemma_add_congruence(
        dot(v, w.add(su)), dot(v, w).add(s.mul(dot(v, u))),
        dot(v, tv.neg()), t.mul(dot(v, v)).neg(),
    );
    T::axiom_eqv_transitive(
        dot(v, diff),
        dot(v, w.add(su)).add(dot(v, tv.neg())),
        dot(v, w).add(s.mul(dot(v, u))).add(t.mul(dot(v, v)).neg()),
    );

    let vw_plus_suv = dot(v, w).add(s.mul(dot(v, u)));
    let t_vv = t.mul(dot(v, v));
    T::axiom_sub_is_add_neg(vw_plus_suv, t_vv);
    T::axiom_eqv_symmetric(vw_plus_suv.sub(t_vv), vw_plus_suv.add(t_vv.neg()));
    T::axiom_eqv_transitive(
        dot(v, diff),
        vw_plus_suv.add(t_vv.neg()),
        vw_plus_suv.sub(t_vv),
    );

    //  Now: vw + s*dot(v,u) - t*dot(v,v) ≡ 0
    //  But Cramer eq2 uses uv = dot(u,v), not dot(v,u).
    //  dot(v,u) ≡ dot(u,v) by commutativity:
    //  dot is defined as v.x*u.x + v.y*u.y + v.z*u.z vs u.x*v.x + u.y*v.y + u.z*v.z
    //  These are equal by mul commutativity. Actually, let me use a dot symmetry fact.
    //  dot(v, u).x_component = v.x*u.x = u.x*v.x = dot(u,v).x_component, etc.
    //  So dot(v,u) ≡ dot(u,v) should follow from Ring commutativity.
    T::axiom_mul_commutative(v.x, u.x);
    T::axiom_mul_commutative(v.y, u.y);
    T::axiom_mul_commutative(v.z, u.z);
    //  dot(v,u) = v.x*u.x + v.y*u.y + v.z*u.z
    //  dot(u,v) = u.x*v.x + u.y*v.y + u.z*v.z
    //  v.x*u.x ≡ u.x*v.x, etc. So:
    additive_group_lemmas::lemma_add_congruence(
        v.x.mul(u.x), u.x.mul(v.x),
        v.y.mul(u.y), u.y.mul(v.y),
    );
    additive_group_lemmas::lemma_add_congruence(
        v.x.mul(u.x).add(v.y.mul(u.y)), u.x.mul(v.x).add(u.y.mul(v.y)),
        v.z.mul(u.z), u.z.mul(v.z),
    );
    //  dot(v,u) ≡ dot(u,v) = uv_val

    //  So s*dot(v,u) ≡ s*dot(u,v) = s*uv_val
    T::axiom_eqv_reflexive(s);
    ring_lemmas::lemma_mul_congruence(s, s, dot(v, u), dot(u, v));
    //  vw + s*dot(v,u) ≡ vw + s*dot(u,v)
    T::axiom_eqv_reflexive(dot(v, w));
    additive_group_lemmas::lemma_add_congruence(
        dot(v, w), dot(v, w),
        s.mul(dot(v, u)), s.mul(dot(u, v)),
    );
    //  vw_plus_suv = dot(v,w) + s*dot(v,u) ≡ dot(v,w) + s*dot(u,v)

    //  Commute: dot(v,w) + s*dot(u,v) ≡ s*dot(u,v) + dot(v,w)
    T::axiom_add_commutative(dot(v, w), s.mul(dot(u, v)));
    //  Chain: vw_plus_suv ≡ s*dot(u,v) + dot(v,w)
    T::axiom_eqv_transitive(
        vw_plus_suv,
        dot(v, w).add(s.mul(dot(u, v))),
        s.mul(dot(u, v)).add(dot(v, w)),
    );

    //  Cramer eq2: s*uv + vw ≡ t*vv
    lemma_cramer_eq2(uu_val, vv_val, uv_val, uw_val, vw_val);
    T::axiom_eqv_transitive(vw_plus_suv, s.mul(dot(u, v)).add(dot(v, w)), t_vv);

    //  vw_plus_suv ≡ t_vv, so vw_plus_suv - t_vv ≡ 0
    T::axiom_eqv_reflexive(t_vv);
    additive_group_lemmas::lemma_sub_congruence(vw_plus_suv, t_vv, t_vv, t_vv);
    additive_group_lemmas::lemma_sub_self(t_vv);
    T::axiom_eqv_transitive(vw_plus_suv.sub(t_vv), t_vv.sub(t_vv), T::zero());

    T::axiom_eqv_transitive(dot(v, diff), vw_plus_suv.sub(t_vv), T::zero());
}

} //  verus!
