use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_linalg::vec2::Vec2;

verus! {

// ---------------------------------------------------------------------------
// Point2 type
// ---------------------------------------------------------------------------

pub struct Point2<T: Ring> {
    pub x: T,
    pub y: T,
}

// ---------------------------------------------------------------------------
// Equivalence
// ---------------------------------------------------------------------------

impl<T: Ring> Equivalence for Point2<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.x.eqv(other.x) && self.y.eqv(other.y)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        T::axiom_eqv_reflexive(a.x);
        T::axiom_eqv_reflexive(a.y);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        T::axiom_eqv_symmetric(a.x, b.x);
        T::axiom_eqv_symmetric(a.y, b.y);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        T::axiom_eqv_transitive(a.x, b.x, c.x);
        T::axiom_eqv_transitive(a.y, b.y, c.y);
    }
}

// ---------------------------------------------------------------------------
// Point-vector operations
// ---------------------------------------------------------------------------

/// Point subtraction: point - point = vector
pub open spec fn sub2<T: Ring>(a: Point2<T>, b: Point2<T>) -> Vec2<T> {
    Vec2 { x: a.x.sub(b.x), y: a.y.sub(b.y) }
}

/// Point-vector addition: point + vector = point
pub open spec fn add_vec2<T: Ring>(p: Point2<T>, v: Vec2<T>) -> Point2<T> {
    Point2 { x: p.x.add(v.x), y: p.y.add(v.y) }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// sub2(a, a) ≡ Vec2::zero()
pub proof fn lemma_sub2_self_zero<T: Ring>(a: Point2<T>)
    ensures
        sub2(a, a).eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    additive_group_lemmas::lemma_sub_self::<T>(a.x);
    additive_group_lemmas::lemma_sub_self::<T>(a.y);
}

/// sub2(add_vec2(b, t), add_vec2(a, t)) ≡ sub2(b, a)
pub proof fn lemma_sub2_translation<T: Ring>(a: Point2<T>, b: Point2<T>, t: Vec2<T>)
    ensures
        sub2(add_vec2(b, t), add_vec2(a, t)).eqv(sub2(b, a)),
{
    // (b.x + t.x) - (a.x + t.x) ≡ b.x - a.x
    additive_group_lemmas::lemma_add_then_sub_cancel::<T>(b.x.sub(a.x), t.x);
    // Need: (b.x+t.x)-(a.x+t.x) ≡ (b.x-a.x+t.x)-t.x ≡ b.x-a.x
    // Actually use: (b.x+t.x) - (a.x+t.x) directly
    // sub_add_sub: a.sub(b).add(b.sub(c)) ≡ a.sub(c)
    // Let's use a different approach: expand and cancel
    // (b.x + t.x) - (a.x + t.x)
    // = (b.x + t.x) + (-(a.x + t.x))
    // = (b.x + t.x) + (-a.x + -t.x)     [neg_add]
    // We need to show this equals b.x - a.x

    // Component x:
    // (b.x+t.x).sub(a.x+t.x) ≡ b.x.sub(a.x)
    additive_group_lemmas::lemma_neg_add::<T>(a.x, t.x);
    // -(a.x+t.x) ≡ -a.x + -t.x
    T::axiom_sub_is_add_neg(b.x.add(t.x), a.x.add(t.x));
    // (b.x+t.x)-(a.x+t.x) ≡ (b.x+t.x)+-(a.x+t.x)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.x.add(t.x),
        a.x.add(t.x).neg(),
        a.x.neg().add(t.x.neg()),
    );
    // (b.x+t.x)+-(a.x+t.x) ≡ (b.x+t.x)+(-a.x+-t.x)
    T::axiom_eqv_transitive(
        b.x.add(t.x).sub(a.x.add(t.x)),
        b.x.add(t.x).add(a.x.add(t.x).neg()),
        b.x.add(t.x).add(a.x.neg().add(t.x.neg())),
    );
    // (b.x+t.x)+(-a.x+-t.x) rearrange via 2x2: (b.x+(-a.x))+(t.x+(-t.x))
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(b.x, t.x, a.x.neg(), t.x.neg());
    T::axiom_eqv_transitive(
        b.x.add(t.x).sub(a.x.add(t.x)),
        b.x.add(t.x).add(a.x.neg().add(t.x.neg())),
        b.x.add(a.x.neg()).add(t.x.add(t.x.neg())),
    );
    // t.x + -t.x ≡ 0
    T::axiom_add_inverse_right(t.x);
    // b.x+(-a.x) + (t.x+(-t.x)) ≡ b.x+(-a.x) + 0
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.x.add(a.x.neg()),
        t.x.add(t.x.neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        b.x.add(t.x).sub(a.x.add(t.x)),
        b.x.add(a.x.neg()).add(t.x.add(t.x.neg())),
        b.x.add(a.x.neg()).add(T::zero()),
    );
    T::axiom_add_zero_right(b.x.add(a.x.neg()));
    T::axiom_eqv_transitive(
        b.x.add(t.x).sub(a.x.add(t.x)),
        b.x.add(a.x.neg()).add(T::zero()),
        b.x.add(a.x.neg()),
    );
    // b.x+(-a.x) ≡ b.x-a.x
    T::axiom_sub_is_add_neg(b.x, a.x);
    T::axiom_eqv_symmetric(b.x.sub(a.x), b.x.add(a.x.neg()));
    T::axiom_eqv_transitive(
        b.x.add(t.x).sub(a.x.add(t.x)),
        b.x.add(a.x.neg()),
        b.x.sub(a.x),
    );

    // Component y: same argument
    additive_group_lemmas::lemma_neg_add::<T>(a.y, t.y);
    T::axiom_sub_is_add_neg(b.y.add(t.y), a.y.add(t.y));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.y.add(t.y),
        a.y.add(t.y).neg(),
        a.y.neg().add(t.y.neg()),
    );
    T::axiom_eqv_transitive(
        b.y.add(t.y).sub(a.y.add(t.y)),
        b.y.add(t.y).add(a.y.add(t.y).neg()),
        b.y.add(t.y).add(a.y.neg().add(t.y.neg())),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(b.y, t.y, a.y.neg(), t.y.neg());
    T::axiom_eqv_transitive(
        b.y.add(t.y).sub(a.y.add(t.y)),
        b.y.add(t.y).add(a.y.neg().add(t.y.neg())),
        b.y.add(a.y.neg()).add(t.y.add(t.y.neg())),
    );
    T::axiom_add_inverse_right(t.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        b.y.add(a.y.neg()),
        t.y.add(t.y.neg()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        b.y.add(t.y).sub(a.y.add(t.y)),
        b.y.add(a.y.neg()).add(t.y.add(t.y.neg())),
        b.y.add(a.y.neg()).add(T::zero()),
    );
    T::axiom_add_zero_right(b.y.add(a.y.neg()));
    T::axiom_eqv_transitive(
        b.y.add(t.y).sub(a.y.add(t.y)),
        b.y.add(a.y.neg()).add(T::zero()),
        b.y.add(a.y.neg()),
    );
    T::axiom_sub_is_add_neg(b.y, a.y);
    T::axiom_eqv_symmetric(b.y.sub(a.y), b.y.add(a.y.neg()));
    T::axiom_eqv_transitive(
        b.y.add(t.y).sub(a.y.add(t.y)),
        b.y.add(a.y.neg()),
        b.y.sub(a.y),
    );
}

} // verus!
