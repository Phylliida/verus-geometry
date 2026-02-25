use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_linalg::vec3::Vec3;

verus! {

// ---------------------------------------------------------------------------
// Point3 type
// ---------------------------------------------------------------------------

pub struct Point3<T: Ring> {
    pub x: T,
    pub y: T,
    pub z: T,
}

// ---------------------------------------------------------------------------
// Equivalence
// ---------------------------------------------------------------------------

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
}

// ---------------------------------------------------------------------------
// Point-vector operations
// ---------------------------------------------------------------------------

/// Point subtraction: point - point = vector
pub open spec fn sub3<T: Ring>(a: Point3<T>, b: Point3<T>) -> Vec3<T> {
    Vec3 { x: a.x.sub(b.x), y: a.y.sub(b.y), z: a.z.sub(b.z) }
}

/// Point-vector addition: point + vector = point
pub open spec fn add_vec3<T: Ring>(p: Point3<T>, v: Vec3<T>) -> Point3<T> {
    Point3 { x: p.x.add(v.x), y: p.y.add(v.y), z: p.z.add(v.z) }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// sub3(a, a) ≡ Vec3::zero()
pub proof fn lemma_sub3_self_zero<T: Ring>(a: Point3<T>)
    ensures
        sub3(a, a).eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    additive_group_lemmas::lemma_sub_self::<T>(a.x);
    additive_group_lemmas::lemma_sub_self::<T>(a.y);
    additive_group_lemmas::lemma_sub_self::<T>(a.z);
}

/// sub3(add_vec3(b, t), add_vec3(a, t)) ≡ sub3(b, a)
pub proof fn lemma_sub3_translation<T: Ring>(a: Point3<T>, b: Point3<T>, t: Vec3<T>)
    ensures
        sub3(add_vec3(b, t), add_vec3(a, t)).eqv(sub3(b, a)),
{
    // Component x:
    lemma_sub_add_cancel_component::<T>(a.x, b.x, t.x);
    // Component y:
    lemma_sub_add_cancel_component::<T>(a.y, b.y, t.y);
    // Component z:
    lemma_sub_add_cancel_component::<T>(a.z, b.z, t.z);
}

/// Helper: (b+t)-(a+t) ≡ b-a for a single Ring component
proof fn lemma_sub_add_cancel_component<T: Ring>(a: T, b: T, t: T)
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

} // verus!
