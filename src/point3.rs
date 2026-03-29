use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::traits::*;
use verus_linalg::vec3::Vec3;
use vstd::prelude::*;

verus! {

//  ---------------------------------------------------------------------------
//  Point3 type
//  ---------------------------------------------------------------------------

pub struct Point3<T: Ring> {
    pub x: T,
    pub y: T,
    pub z: T,
}

//  ---------------------------------------------------------------------------
//  Equivalence
//  ---------------------------------------------------------------------------

impl<T: Ring> Equivalence for Point3<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.x.eqv(other.x) && self.y.eqv(other.y) && self.z.eqv(other.z)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        T::axiom_eqv_reflexive(a.x);
        T::axiom_eqv_reflexive(a.y);
        T::axiom_eqv_reflexive(a.z);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        T::axiom_eqv_symmetric(a.x, b.x);
        T::axiom_eqv_symmetric(a.y, b.y);
        T::axiom_eqv_symmetric(a.z, b.z);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        T::axiom_eqv_transitive(a.x, b.x, c.x);
        T::axiom_eqv_transitive(a.y, b.y, c.y);
        T::axiom_eqv_transitive(a.z, b.z, c.z);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        if a == b {
            T::axiom_eq_implies_eqv(a.x, b.x);
            T::axiom_eq_implies_eqv(a.y, b.y);
            T::axiom_eq_implies_eqv(a.z, b.z);
        }
    }
}

//  ---------------------------------------------------------------------------
//  Point-vector operations
//  ---------------------------------------------------------------------------

///  Point subtraction: point - point = vector
pub open spec fn sub3<T: Ring>(a: Point3<T>, b: Point3<T>) -> Vec3<T> {
    Vec3 { x: a.x.sub(b.x), y: a.y.sub(b.y), z: a.z.sub(b.z) }
}

///  Point-vector addition: point + vector = point
pub open spec fn add_vec3<T: Ring>(p: Point3<T>, v: Vec3<T>) -> Point3<T> {
    Point3 { x: p.x.add(v.x), y: p.y.add(v.y), z: p.z.add(v.z) }
}

//  ---------------------------------------------------------------------------
//  Lemmas
//  ---------------------------------------------------------------------------

///  sub3(a, a) ≡ Vec3::zero()
pub proof fn lemma_sub3_self_zero<T: Ring>(a: Point3<T>)
    ensures
        sub3(a, a).eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    additive_group_lemmas::lemma_sub_self::<T>(a.x);
    additive_group_lemmas::lemma_sub_self::<T>(a.y);
    additive_group_lemmas::lemma_sub_self::<T>(a.z);
}

///  sub3(add_vec3(b, t), add_vec3(a, t)) ≡ sub3(b, a)
pub proof fn lemma_sub3_translation<T: Ring>(a: Point3<T>, b: Point3<T>, t: Vec3<T>)
    ensures
        sub3(add_vec3(b, t), add_vec3(a, t)).eqv(sub3(b, a)),
{
    //  Component x:
    lemma_sub_add_cancel_component::<T>(a.x, b.x, t.x);
    //  Component y:
    lemma_sub_add_cancel_component::<T>(a.y, b.y, t.y);
    //  Component z:
    lemma_sub_add_cancel_component::<T>(a.z, b.z, t.z);
}

///  Helper: (b+t)-(a+t) ≡ b-a for a single Ring component
pub proof fn lemma_sub_add_cancel_component<T: Ring>(a: T, b: T, t: T)
    ensures
        b.add(t).sub(a.add(t)).eqv(b.sub(a)),
{
    additive_group_lemmas::lemma_neg_add::<T>(a, t);
    T::axiom_sub_is_add_neg(b.add(t), a.add(t));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.add(t),
        a.add(t).neg(),
        a.neg().add(t.neg()),
    );
    T::axiom_eqv_transitive(
        b.add(t).sub(a.add(t)),
        b.add(t).add(a.add(t).neg()),
        b.add(t).add(a.neg().add(t.neg())),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(b, t, a.neg(), t.neg());
    T::axiom_eqv_transitive(
        b.add(t).sub(a.add(t)),
        b.add(t).add(a.neg().add(t.neg())),
        b.add(a.neg()).add(t.add(t.neg())),
    );
    T::axiom_add_inverse_right(t);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.add(a.neg()),
        t.add(t.neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        b.add(t).sub(a.add(t)),
        b.add(a.neg()).add(t.add(t.neg())),
        b.add(a.neg()).add(T::zero()),
    );
    T::axiom_add_zero_right(b.add(a.neg()));
    T::axiom_eqv_transitive(
        b.add(t).sub(a.add(t)),
        b.add(a.neg()).add(T::zero()),
        b.add(a.neg()),
    );
    T::axiom_sub_is_add_neg(b, a);
    T::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
    T::axiom_eqv_transitive(
        b.add(t).sub(a.add(t)),
        b.add(a.neg()),
        b.sub(a),
    );
}

///  sub3(d, a).add(sub3(e, d)) ≡ sub3(e, a)  (telescope cancellation)
pub proof fn lemma_sub3_telescope<T: Ring>(d: Point3<T>, e: Point3<T>, a: Point3<T>)
    ensures
        sub3(d, a).add(sub3(e, d)).eqv(sub3(e, a)),
{
    //  Componentwise: (d.x-a.x) + (e.x-d.x) = e.x-a.x
    //  Using lemma_sub_add_sub(e, d, a): e.sub(d).add(d.sub(a)) ≡ e.sub(a)
    //  Then add_commutative to swap summands.

    //  x component
    T::axiom_add_commutative(d.x.sub(a.x), e.x.sub(d.x));
    additive_group_lemmas::lemma_sub_add_sub::<T>(e.x, d.x, a.x);
    T::axiom_eqv_transitive(
        d.x.sub(a.x).add(e.x.sub(d.x)),
        e.x.sub(d.x).add(d.x.sub(a.x)),
        e.x.sub(a.x),
    );

    //  y component
    T::axiom_add_commutative(d.y.sub(a.y), e.y.sub(d.y));
    additive_group_lemmas::lemma_sub_add_sub::<T>(e.y, d.y, a.y);
    T::axiom_eqv_transitive(
        d.y.sub(a.y).add(e.y.sub(d.y)),
        e.y.sub(d.y).add(d.y.sub(a.y)),
        e.y.sub(a.y),
    );

    //  z component
    T::axiom_add_commutative(d.z.sub(a.z), e.z.sub(d.z));
    additive_group_lemmas::lemma_sub_add_sub::<T>(e.z, d.z, a.z);
    T::axiom_eqv_transitive(
        d.z.sub(a.z).add(e.z.sub(d.z)),
        e.z.sub(d.z).add(d.z.sub(a.z)),
        e.z.sub(a.z),
    );
}

//  ---------------------------------------------------------------------------
//  Addition rearrangement helpers
//  ---------------------------------------------------------------------------

///  (a + b) + c ≡ (a + c) + b
proof fn lemma_add_swap_last<T: Ring>(a: T, b: T, c: T)
    ensures
        a.add(b).add(c).eqv(a.add(c).add(b)),
{
    //  (a+b)+c ≡ a+(b+c) by associativity
    T::axiom_add_associative(a, b, c);
    //  b+c ≡ c+b by commutativity
    T::axiom_add_commutative(b, c);
    //  a+(b+c) ≡ a+(c+b) by right congruence
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.add(c), c.add(b));
    //  (a+b)+c ≡ a+(c+b) by transitivity
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(b.add(c)), a.add(c.add(b)));
    //  (a+c)+b ≡ a+(c+b) by associativity
    T::axiom_add_associative(a, c, b);
    //  a+(c+b) ≡ (a+c)+b by symmetric
    T::axiom_eqv_symmetric(a.add(c).add(b), a.add(c.add(b)));
    //  (a+b)+c ≡ (a+c)+b by transitivity
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(c.add(b)), a.add(c).add(b));
}

///  (a + b) - c ≡ (a - c) + b
proof fn lemma_sub_shift_component<T: Ring>(a: T, b: T, c: T)
    ensures
        a.add(b).sub(c).eqv(a.sub(c).add(b)),
{
    let nc = c.neg();
    //  LHS: (a+b).sub(c) ≡ (a+b)+(-c)
    T::axiom_sub_is_add_neg(a.add(b), c);
    //  (a+b)+(-c) ≡ (a+(-c))+b by add_swap_last
    lemma_add_swap_last::<T>(a, b, nc);
    //  Chain: (a+b).sub(c) ≡ (a+(-c))+b
    T::axiom_eqv_transitive(a.add(b).sub(c), a.add(b).add(nc), a.add(nc).add(b));
    //  RHS: a.sub(c) ≡ a+(-c)
    T::axiom_sub_is_add_neg(a, c);
    //  (a+(-c)) ≡ a.sub(c) by symmetric
    T::axiom_eqv_symmetric(a.sub(c), a.add(nc));
    //  (a+(-c))+b ≡ a.sub(c)+b by left congruence
    T::axiom_add_congruence_left(a.add(nc), a.sub(c), b);
    //  Chain: (a+b).sub(c) ≡ a.sub(c).add(b)
    T::axiom_eqv_transitive(a.add(b).sub(c), a.add(nc).add(b), a.sub(c).add(b));
}

///  sub3(add_vec3(p, v), q) ≡ sub3(p, q) + v
///
///  Geometric meaning: (p + v) - q = (p - q) + v
pub proof fn lemma_sub3_shift_add<T: Ring>(p: Point3<T>, v: Vec3<T>, q: Point3<T>)
    ensures
        sub3(add_vec3(p, v), q).eqv(sub3(p, q).add(v)),
{
    lemma_sub_shift_component::<T>(p.x, v.x, q.x);
    lemma_sub_shift_component::<T>(p.y, v.y, q.y);
    lemma_sub_shift_component::<T>(p.z, v.z, q.z);
}

///  sub3(a, b) ≡ sub3(b, a).neg()  (antisymmetry)
pub proof fn lemma_sub3_antisymmetric<T: Ring>(a: Point3<T>, b: Point3<T>)
    ensures
        sub3(a, b).eqv(sub3(b, a).neg()),
{
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.x, b.x);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.y, b.y);
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.z, b.z);
}

} //  verus!
