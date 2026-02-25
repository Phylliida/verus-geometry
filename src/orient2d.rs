use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_linalg::vec2::Vec2;
use crate::point2::*;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// 2D determinant: det2d(u, v) = u.x*v.y - u.y*v.x
pub open spec fn det2d<T: Ring>(u: Vec2<T>, v: Vec2<T>) -> T {
    u.x.mul(v.y).sub(u.y.mul(v.x))
}

/// 2D orientation predicate: orient2d(a, b, c) = det2d(b-a, c-a)
pub open spec fn orient2d<T: Ring>(a: Point2<T>, b: Point2<T>, c: Point2<T>) -> T {
    det2d(sub2(b, a), sub2(c, a))
}

// ---------------------------------------------------------------------------
// Private det2d lemmas
// ---------------------------------------------------------------------------

/// det2d(u, v) ≡ -det2d(v, u)
proof fn lemma_det2d_antisymmetric<T: Ring>(u: Vec2<T>, v: Vec2<T>)
    ensures
        det2d(u, v).eqv(det2d(v, u).neg()),
{
    // det2d(u,v) = u.x*v.y - u.y*v.x
    // det2d(v,u) = v.x*u.y - v.y*u.x
    // Need: u.x*v.y - u.y*v.x ≡ -(v.x*u.y - v.y*u.x)

    // u.x*v.y ≡ v.y*u.x  [mul_commutative]
    T::axiom_mul_commutative(u.x, v.y);
    // u.y*v.x ≡ v.x*u.y  [mul_commutative]
    T::axiom_mul_commutative(u.y, v.x);

    // u.x*v.y - u.y*v.x ≡ v.y*u.x - v.x*u.y  [sub_congruence]
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(v.y), v.y.mul(u.x),
        u.y.mul(v.x), v.x.mul(u.y),
    );

    // v.y*u.x - v.x*u.y ≡ -(v.x*u.y - v.y*u.x)  [sub_antisymmetric]
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(v.y.mul(u.x), v.x.mul(u.y));

    T::axiom_eqv_transitive(
        det2d(u, v),
        v.y.mul(u.x).sub(v.x.mul(u.y)),
        v.x.mul(u.y).sub(v.y.mul(u.x)).neg(),
    );
}

/// det2d(v, v) ≡ 0
proof fn lemma_det2d_self_zero<T: Ring>(v: Vec2<T>)
    ensures
        det2d(v, v).eqv(T::zero()),
{
    // det2d(v,v) = v.x*v.y - v.y*v.x
    // v.x*v.y ≡ v.y*v.x  [mul_commutative]
    T::axiom_mul_commutative(v.x, v.y);
    // v.x*v.y - v.y*v.x ≡ v.y*v.x - v.y*v.x  [sub_congruence with reflexive right]
    T::axiom_eqv_reflexive(v.y.mul(v.x));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        v.x.mul(v.y), v.y.mul(v.x),
        v.y.mul(v.x), v.y.mul(v.x),
    );
    // v.y*v.x - v.y*v.x ≡ 0  [sub_self]
    additive_group_lemmas::lemma_sub_self::<T>(v.y.mul(v.x));
    T::axiom_eqv_transitive(
        det2d(v, v),
        v.y.mul(v.x).sub(v.y.mul(v.x)),
        T::zero(),
    );
}

/// Congruence: a1≡a2, b1≡b2 implies det2d(a1,b1) ≡ det2d(a2,b2)
proof fn lemma_det2d_congruence<T: Ring>(a1: Vec2<T>, a2: Vec2<T>, b1: Vec2<T>, b2: Vec2<T>)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        det2d(a1, b1).eqv(det2d(a2, b2)),
{
    // a1.x*b1.y ≡ a2.x*b2.y
    ring_lemmas::lemma_mul_congruence_right::<T>(a1.x, b1.y, b2.y);
    T::axiom_mul_congruence_left(a1.x, a2.x, b2.y);
    T::axiom_eqv_transitive(a1.x.mul(b1.y), a1.x.mul(b2.y), a2.x.mul(b2.y));

    // a1.y*b1.x ≡ a2.y*b2.x
    ring_lemmas::lemma_mul_congruence_right::<T>(a1.y, b1.x, b2.x);
    T::axiom_mul_congruence_left(a1.y, a2.y, b2.x);
    T::axiom_eqv_transitive(a1.y.mul(b1.x), a1.y.mul(b2.x), a2.y.mul(b2.x));

    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.x.mul(b1.y), a2.x.mul(b2.y),
        a1.y.mul(b1.x), a2.y.mul(b2.x),
    );
}

/// det2d(u, -v) ≡ -det2d(u, v)
proof fn lemma_det2d_neg_right<T: Ring>(u: Vec2<T>, v: Vec2<T>)
    ensures
        det2d(u, Vec2 { x: v.x.neg(), y: v.y.neg() }).eqv(det2d(u, v).neg()),
{
    // det2d(u, -v) = u.x*(-v.y) - u.y*(-v.x)
    // u.x*(-v.y) ≡ -(u.x*v.y)  [mul_neg_right]
    ring_lemmas::lemma_mul_neg_right::<T>(u.x, v.y);
    // u.y*(-v.x) ≡ -(u.y*v.x)  [mul_neg_right]
    ring_lemmas::lemma_mul_neg_right::<T>(u.y, v.x);

    // -(u.x*v.y) - -(u.y*v.x) ≡ -(u.x*v.y - u.y*v.x)
    // Need: a.neg().sub(b.neg()) ≡ (a.sub(b)).neg()
    // via sub_congruence to get to negated form, then use neg properties
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.mul(v.y.neg()), u.x.mul(v.y).neg(),
        u.y.mul(v.x.neg()), u.y.mul(v.x).neg(),
    );
    // det2d(u,-v) ≡ -(u.x*v.y) - -(u.y*v.x) [from sub_congruence]

    // -(a) - -(b) ≡ -(a - b)
    // sub_is_add_neg: -a - (-b) = -a + -(-b) = -a + b
    // neg of (a-b) = -(a) + -(-(b)) ... no, -(a-b) = -a + b via neg_add + sub_is_add_neg
    // Actually: -(a-b) = -(a + (-b)) = (-a) + (-(-b)) = -a + b  [neg_add, double_neg]
    // And: (-a) - (-b) = -a + -(-b) = -a + b  [sub_is_add_neg, double_neg]
    // So: (-a) - (-b) ≡ -(a-b)

    // Let me use: -(a) - -(b) via sub_is_add_neg
    let a = u.x.mul(v.y);
    let b = u.y.mul(v.x);

    // -a - (-b) = -a + -(-b)  [sub_is_add_neg]
    T::axiom_sub_is_add_neg(a.neg(), b.neg());
    // -(-b) ≡ b  [double_neg]
    additive_group_lemmas::lemma_neg_involution::<T>(b);
    // -a + -(-b) ≡ -a + b  [add_congruence_right]
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(
        a.neg().sub(b.neg()),
        a.neg().add(b.neg().neg()),
        a.neg().add(b),
    );

    // -(a-b) = -(a + (-b)) = -a + -(-b) ... wait, use neg_add
    // -(a - b): first, a - b ≡ a + (-b)
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_neg_congruence(a.sub(b), a.add(b.neg()));
    // -(a+(-b)) ≡ (-a)+(-(-b))  [neg_add]
    additive_group_lemmas::lemma_neg_add::<T>(a, b.neg());
    T::axiom_eqv_transitive(
        a.sub(b).neg(),
        a.add(b.neg()).neg(),
        a.neg().add(b.neg().neg()),
    );
    // (-a)+(-(-b)) ≡ (-a)+b  [add_congruence_right with double_neg]
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(
        a.sub(b).neg(),
        a.neg().add(b.neg().neg()),
        a.neg().add(b),
    );

    // Now: -a - (-b) ≡ -a + b ≡ -(a-b)
    T::axiom_eqv_symmetric(a.sub(b).neg(), a.neg().add(b));
    T::axiom_eqv_transitive(
        a.neg().sub(b.neg()),
        a.neg().add(b),
        a.sub(b).neg(),
    );

    // Chain: det2d(u,-v) ≡ -a - (-b) ≡ -(a-b) = -det2d(u,v)
    T::axiom_eqv_transitive(
        det2d(u, Vec2 { x: v.x.neg(), y: v.y.neg() }),
        a.neg().sub(b.neg()),
        det2d(u, v).neg(),
    );
}

/// det2d(u+v, w) ≡ det2d(u, w) + det2d(v, w)
proof fn lemma_det2d_linear_left<T: Ring>(u: Vec2<T>, v: Vec2<T>, w: Vec2<T>)
    ensures
        det2d(Vec2 { x: u.x.add(v.x), y: u.y.add(v.y) }, w).eqv(
            det2d(u, w).add(det2d(v, w))
        ),
{
    // det2d(u+v, w) = (u.x+v.x)*w.y - (u.y+v.y)*w.x
    // det2d(u,w) + det2d(v,w) = (u.x*w.y - u.y*w.x) + (v.x*w.y - v.y*w.x)

    // (u.x+v.x)*w.y ≡ u.x*w.y + v.x*w.y  [distributes_right]
    ring_lemmas::lemma_mul_distributes_right::<T>(u.x, v.x, w.y);
    // (u.y+v.y)*w.x ≡ u.y*w.x + v.y*w.x  [distributes_right]
    ring_lemmas::lemma_mul_distributes_right::<T>(u.y, v.y, w.x);

    // det2d(u+v,w) ≡ (u.x*w.y + v.x*w.y) - (u.y*w.x + v.y*w.x)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.x.add(v.x).mul(w.y), u.x.mul(w.y).add(v.x.mul(w.y)),
        u.y.add(v.y).mul(w.x), u.y.mul(w.x).add(v.y.mul(w.x)),
    );

    // (a+b)-(c+d) ≡ (a-c)+(b-d)
    // Use sub_is_add_neg + neg_add + rearrange
    let a = u.x.mul(w.y);
    let b = v.x.mul(w.y);
    let c = u.y.mul(w.x);
    let d = v.y.mul(w.x);

    // (a+b)-(c+d) ≡ (a+b)+-(c+d)  [sub_is_add_neg]
    T::axiom_sub_is_add_neg(a.add(b), c.add(d));
    // -(c+d) ≡ -c + -d  [neg_add]
    additive_group_lemmas::lemma_neg_add::<T>(c, d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.add(b), c.add(d).neg(), c.neg().add(d.neg()));
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );
    // (a+b)+(-c+-d) rearrange 2x2: (a+(-c))+(b+(-d))
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, c.neg(), d.neg());
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );
    // a+(-c) ≡ a-c  [sub_is_add_neg backwards]
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    // b+(-d) ≡ b-d
    T::axiom_sub_is_add_neg(b, d);
    T::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));
    // (a+(-c))+(b+(-d)) ≡ (a-c)+(b-d)
    T::axiom_add_congruence_left(a.add(c.neg()), a.sub(c), b.add(d.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.sub(c), b.add(d.neg()), b.sub(d));
    T::axiom_eqv_transitive(
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );

    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );

    // Chain: det2d(u+v,w) ≡ (a+b)-(c+d) ≡ (a-c)+(b-d) = det2d(u,w)+det2d(v,w)
    T::axiom_eqv_transitive(
        det2d(Vec2 { x: u.x.add(v.x), y: u.y.add(v.y) }, w),
        a.add(b).sub(c.add(d)),
        a.sub(c).add(b.sub(d)),
    );
}

/// det2d(u-v, w) ≡ det2d(u, w) - det2d(v, w)
proof fn lemma_det2d_sub_left<T: Ring>(u: Vec2<T>, v: Vec2<T>, w: Vec2<T>)
    ensures
        det2d(Vec2 { x: u.x.sub(v.x), y: u.y.sub(v.y) }, w).eqv(
            det2d(u, w).sub(det2d(v, w))
        ),
{
    // u-v = u+(-v), so det2d(u-v, w) = det2d(u+(-v), w) ≡ det2d(u,w) + det2d(-v,w)
    // via linear_left

    // First: u.x-v.x ≡ u.x+(-v.x), u.y-v.y ≡ u.y+(-v.y)
    T::axiom_sub_is_add_neg(u.x, v.x);
    T::axiom_sub_is_add_neg(u.y, v.y);

    // det2d(u-v, w) ≡ det2d(u+(-v), w) via congruence
    let neg_v = Vec2 { x: v.x.neg(), y: v.y.neg() };
    let u_sub_v = Vec2 { x: u.x.sub(v.x), y: u.y.sub(v.y) };
    let u_add_neg_v = Vec2 { x: u.x.add(v.x.neg()), y: u.y.add(v.y.neg()) };

    // u_sub_v ≡ u_add_neg_v (componentwise via sub_is_add_neg)
    // w ≡ w (reflexive)
    Vec2::<T>::axiom_eqv_reflexive(w);
    lemma_det2d_congruence::<T>(u_sub_v, u_add_neg_v, w, w);

    // det2d(u+(-v), w) ≡ det2d(u,w) + det2d(-v,w) via linear_left
    lemma_det2d_linear_left::<T>(u, neg_v, w);

    T::axiom_eqv_transitive(
        det2d(u_sub_v, w),
        det2d(u_add_neg_v, w),
        det2d(u, w).add(det2d(neg_v, w)),
    );

    // det2d(-v, w) ≡ -det2d(v, w) via neg_right... no, we need det2d with negated left
    // det2d(-v, w) = (-v.x)*w.y - (-v.y)*w.x
    // (-v.x)*w.y ≡ -(v.x*w.y)  [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<T>(v.x, w.y);
    // (-v.y)*w.x ≡ -(v.y*w.x)  [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<T>(v.y, w.x);
    // -(v.x*w.y) - -(v.y*w.x) ≡ -(v.x*w.y - v.y*w.x)
    // This is the same pattern as in neg_right: -a - (-b) ≡ -(a-b)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        v.x.neg().mul(w.y), v.x.mul(w.y).neg(),
        v.y.neg().mul(w.x), v.y.mul(w.x).neg(),
    );

    // Now show: -(a) - -(b) ≡ -(a - b) where a=v.x*w.y, b=v.y*w.x
    let a = v.x.mul(w.y);
    let b = v.y.mul(w.x);

    T::axiom_sub_is_add_neg(a.neg(), b.neg());
    additive_group_lemmas::lemma_neg_involution::<T>(b);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(
        a.neg().sub(b.neg()),
        a.neg().add(b.neg().neg()),
        a.neg().add(b),
    );

    T::axiom_sub_is_add_neg(a, b);
    T::axiom_neg_congruence(a.sub(b), a.add(b.neg()));
    additive_group_lemmas::lemma_neg_add::<T>(a, b.neg());
    T::axiom_eqv_transitive(
        a.sub(b).neg(),
        a.add(b.neg()).neg(),
        a.neg().add(b.neg().neg()),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(
        a.sub(b).neg(),
        a.neg().add(b.neg().neg()),
        a.neg().add(b),
    );

    T::axiom_eqv_symmetric(a.sub(b).neg(), a.neg().add(b));
    T::axiom_eqv_transitive(
        a.neg().sub(b.neg()),
        a.neg().add(b),
        a.sub(b).neg(),
    );

    // det2d(-v, w) ≡ -a - (-b) ≡ -(a-b) = -det2d(v,w)
    T::axiom_eqv_transitive(
        det2d(neg_v, w),
        a.neg().sub(b.neg()),
        det2d(v, w).neg(),
    );

    // det2d(u,w) + det2d(-v,w) ≡ det2d(u,w) + (-det2d(v,w))
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        det2d(u, w),
        det2d(neg_v, w),
        det2d(v, w).neg(),
    );

    // det2d(u,w) + (-det2d(v,w)) ≡ det2d(u,w) - det2d(v,w)
    T::axiom_sub_is_add_neg(det2d(u, w), det2d(v, w));
    T::axiom_eqv_symmetric(
        det2d(u, w).sub(det2d(v, w)),
        det2d(u, w).add(det2d(v, w).neg()),
    );

    T::axiom_eqv_transitive(
        det2d(u, w).add(det2d(neg_v, w)),
        det2d(u, w).add(det2d(v, w).neg()),
        det2d(u, w).sub(det2d(v, w)),
    );

    T::axiom_eqv_transitive(
        det2d(u_sub_v, w),
        det2d(u, w).add(det2d(neg_v, w)),
        det2d(u, w).sub(det2d(v, w)),
    );
}

// ---------------------------------------------------------------------------
// Public orient2d lemmas
// ---------------------------------------------------------------------------

/// orient2d(a, c, b) ≡ -orient2d(a, b, c)
pub proof fn lemma_orient2d_swap_bc<T: Ring>(a: Point2<T>, b: Point2<T>, c: Point2<T>)
    ensures
        orient2d(a, c, b).eqv(orient2d(a, b, c).neg()),
{
    lemma_det2d_antisymmetric::<T>(sub2(c, a), sub2(b, a));
    // det2d(c-a, b-a) ≡ -det2d(b-a, c-a)
    // orient2d(a,c,b) = det2d(sub2(c,a), sub2(b,a))
    // orient2d(a,b,c) = det2d(sub2(b,a), sub2(c,a))
    // So: orient2d(a,c,b) ≡ -orient2d(a,b,c) ✓
}

/// orient2d(a, a, c) ≡ 0
pub proof fn lemma_orient2d_degenerate_ab<T: Ring>(a: Point2<T>, c: Point2<T>)
    ensures
        orient2d(a, a, c).eqv(T::zero()),
{
    // orient2d(a,a,c) = det2d(sub2(a,a), sub2(c,a))
    // sub2(a,a) ≡ zero_vec
    lemma_sub2_self_zero::<T>(a);
    let zero_vec = Vec2 { x: T::zero(), y: T::zero() };
    // det2d(zero_vec, sub2(c,a)):
    // 0*c_a.y - 0*c_a.x ≡ 0 - 0 ≡ 0
    let ca = sub2(c, a);
    Vec2::<T>::axiom_eqv_reflexive(ca);
    lemma_det2d_congruence::<T>(sub2(a, a), zero_vec, ca, ca);
    // det2d(zero_vec, ca) = 0*ca.y - 0*ca.x
    ring_lemmas::lemma_mul_zero_left::<T>(ca.y);
    ring_lemmas::lemma_mul_zero_left::<T>(ca.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(ca.y), T::zero(),
        T::zero().mul(ca.x), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        det2d(zero_vec, ca),
        T::zero().sub(T::zero()),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        orient2d(a, a, c),
        det2d(zero_vec, ca),
        T::zero(),
    );
}

/// orient2d(a, b, b) ≡ 0
pub proof fn lemma_orient2d_degenerate_bc<T: Ring>(a: Point2<T>, b: Point2<T>)
    ensures
        orient2d(a, b, b).eqv(T::zero()),
{
    // orient2d(a,b,b) = det2d(sub2(b,a), sub2(b,a))
    lemma_det2d_self_zero::<T>(sub2(b, a));
}

/// orient2d(a, b, c) ≡ orient2d(b, c, a)  (cyclic permutation)
pub proof fn lemma_orient2d_cyclic<T: Ring>(a: Point2<T>, b: Point2<T>, c: Point2<T>)
    ensures
        orient2d(a, b, c).eqv(orient2d(b, c, a)),
{
    // orient2d(a,b,c) = det2d(b-a, c-a)
    // orient2d(b,c,a) = det2d(c-b, a-b)
    // Need: det2d(b-a, c-a) ≡ det2d(c-b, a-b)

    // Strategy: c-a = (c-b) + (b-a), so
    // det2d(b-a, c-a) = det2d(b-a, (c-b)+(b-a))
    //                 = det2d(b-a, c-b) + det2d(b-a, b-a)    [linear right... but we have linear left]
    // We need linear right. We can get it from antisymmetry + linear left.
    // det2d(b-a, c-b) = -det2d(c-b, b-a) [antisymmetric]
    // And det2d(b-a, b-a) = 0 [self_zero]

    // Actually, let's use a direct approach.
    // Let u = b-a, v = c-a.
    // orient2d(b,c,a) = det2d(c-b, a-b)
    // c-b = (c-a)-(b-a) = v-u at the component level
    // a-b = -(b-a) = -u at the component level

    let u = sub2(b, a);
    let v = sub2(c, a);

    // c-b: componentwise c.x-b.x = (c.x-a.x)-(b.x-a.x) = v.x-u.x
    // a-b: componentwise a.x-b.x = -(b.x-a.x) = -u.x
    let c_minus_b = sub2(c, b);
    let a_minus_b = sub2(a, b);
    let v_minus_u = Vec2 { x: v.x.sub(u.x), y: v.y.sub(u.y) };
    let neg_u = Vec2 { x: u.x.neg(), y: u.y.neg() };

    // Show c_minus_b ≡ v_minus_u
    // c.x-b.x and v.x-u.x = (c.x-a.x)-(b.x-a.x)
    additive_group_lemmas::lemma_sub_add_sub::<T>(c.x, a.x, b.x);
    T::axiom_eqv_symmetric(c.x.sub(a.x).add(a.x.sub(b.x)), c.x.sub(b.x));
    // sub_add_sub gives: c.x.sub(a.x).add(a.x.sub(b.x)) ≡ c.x.sub(b.x)
    // We need: c.x-b.x ≡ (c.x-a.x)-(b.x-a.x)
    // i.e. c.x-b.x ≡ v.x - u.x

    // Let's use: (c-a) - (b-a) ≡ c-b
    // sub_add_sub: a.sub(b).add(b.sub(c)) ≡ a.sub(c)
    // With a=c.x, b=a.x, c=b.x: (c.x-a.x) + (a.x-b.x) ≡ c.x-b.x
    // But we want (c.x-a.x) - (b.x-a.x)
    // (c.x-a.x) - (b.x-a.x) ≡ (c.x-a.x) + (-(b.x-a.x))
    // -(b.x-a.x) ≡ a.x-b.x  [sub_antisymmetric gives b.x-a.x ≡ -(a.x-b.x), so -(b.x-a.x) ≡ a.x-b.x via double neg... no]
    // sub_antisymmetric: a.sub(b) ≡ b.sub(a).neg()
    // So b.x.sub(a.x) ≡ a.x.sub(b.x).neg()
    // And neg of that: b.x.sub(a.x).neg() ≡ a.x.sub(b.x).neg().neg() ≡ a.x.sub(b.x)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(b.x, a.x);
    // b.x-a.x ≡ -(a.x-b.x)
    T::axiom_neg_congruence(b.x.sub(a.x), a.x.sub(b.x).neg());
    // -(b.x-a.x) ≡ -(-(a.x-b.x))
    additive_group_lemmas::lemma_neg_involution::<T>(a.x.sub(b.x));
    // -(-(a.x-b.x)) ≡ a.x-b.x
    T::axiom_eqv_transitive(
        b.x.sub(a.x).neg(),
        a.x.sub(b.x).neg().neg(),
        a.x.sub(b.x),
    );

    // (c.x-a.x) + (a.x-b.x) ≡ c.x-b.x  [sub_add_sub with c.x, a.x, b.x]
    additive_group_lemmas::lemma_sub_add_sub::<T>(c.x, a.x, b.x);

    // (c.x-a.x) - (b.x-a.x): sub_is_add_neg then congruence
    T::axiom_sub_is_add_neg(v.x, u.x);
    // v.x - u.x ≡ v.x + (-u.x) ≡ v.x + (a.x-b.x)
    // since -u.x = -(b.x-a.x) ≡ a.x-b.x (proved above)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        v.x,
        u.x.neg(),
        a.x.sub(b.x),
    );
    T::axiom_eqv_transitive(
        v.x.sub(u.x),
        v.x.add(u.x.neg()),
        v.x.add(a.x.sub(b.x)),
    );
    // v.x + (a.x-b.x) ≡ c.x - b.x  [sub_add_sub]
    T::axiom_eqv_transitive(
        v.x.sub(u.x),
        v.x.add(a.x.sub(b.x)),
        c.x.sub(b.x),
    );

    // Same for y component
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(b.y, a.y);
    T::axiom_neg_congruence(b.y.sub(a.y), a.y.sub(b.y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(a.y.sub(b.y));
    T::axiom_eqv_transitive(
        b.y.sub(a.y).neg(),
        a.y.sub(b.y).neg().neg(),
        a.y.sub(b.y),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(c.y, a.y, b.y);
    T::axiom_sub_is_add_neg(v.y, u.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        v.y,
        u.y.neg(),
        a.y.sub(b.y),
    );
    T::axiom_eqv_transitive(
        v.y.sub(u.y),
        v.y.add(u.y.neg()),
        v.y.add(a.y.sub(b.y)),
    );
    T::axiom_eqv_transitive(
        v.y.sub(u.y),
        v.y.add(a.y.sub(b.y)),
        c.y.sub(b.y),
    );

    // So v_minus_u ≡ c_minus_b
    // Also need: neg_u ≡ a_minus_b
    // -u.x = -(b.x-a.x) ≡ a.x-b.x (proved above)
    // But a_minus_b.x = a.x - b.x, so we need -(b.x-a.x) ≡ a.x-b.x
    // Already proved: u.x.neg() = (b.x-a.x).neg() ≡ a.x-b.x = a_minus_b.x ✓

    // Now: orient2d(b,c,a) = det2d(c_minus_b, a_minus_b)
    //                      ≡ det2d(v_minus_u, neg_u)        [congruence]

    // v_minus_u ≡ c_minus_b: swap direction
    T::axiom_eqv_symmetric(v.x.sub(u.x), c.x.sub(b.x));
    T::axiom_eqv_symmetric(v.y.sub(u.y), c.y.sub(b.y));

    // neg_u ≡ a_minus_b: swap direction
    T::axiom_eqv_symmetric(u.x.neg(), a.x.sub(b.x));
    T::axiom_eqv_symmetric(u.y.neg(), a.y.sub(b.y));

    lemma_det2d_congruence::<T>(c_minus_b, v_minus_u, a_minus_b, neg_u);
    // det2d(c_minus_b, a_minus_b) ≡ det2d(v_minus_u, neg_u)

    // det2d(v-u, -u) via sub_left + neg_right + self_zero:
    // det2d(v-u, -u) ≡ det2d(v, -u) - det2d(u, -u)  [sub_left]
    lemma_det2d_sub_left::<T>(v, u, neg_u);
    // det2d(u, -u): first det2d(u, -u) ≡ -det2d(u, u) [neg_right]
    lemma_det2d_neg_right::<T>(u, u);
    // det2d(u, u) ≡ 0  [self_zero]
    lemma_det2d_self_zero::<T>(u);
    // -det2d(u,u) ≡ -0 ≡ 0
    T::axiom_neg_congruence(det2d(u, u), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(
        det2d(u, u).neg(),
        T::zero().neg(),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        det2d(u, neg_u),
        det2d(u, u).neg(),
        T::zero(),
    );

    // det2d(v, -u) - det2d(u, -u) ≡ det2d(v, -u) - 0 ≡ det2d(v, -u)
    T::axiom_eqv_reflexive(det2d(v, neg_u));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(v, neg_u), det2d(v, neg_u),
        det2d(u, neg_u), T::zero(),
    );
    // a - 0 ≡ a: sub_is_add_neg -> a + (-0) -> a + 0 -> a
    T::axiom_sub_is_add_neg(det2d(v, neg_u), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        det2d(v, neg_u), T::zero().neg(), T::zero(),
    );
    T::axiom_eqv_transitive(
        det2d(v, neg_u).sub(T::zero()),
        det2d(v, neg_u).add(T::zero().neg()),
        det2d(v, neg_u).add(T::zero()),
    );
    T::axiom_add_zero_right(det2d(v, neg_u));
    T::axiom_eqv_transitive(
        det2d(v, neg_u).sub(T::zero()),
        det2d(v, neg_u).add(T::zero()),
        det2d(v, neg_u),
    );
    T::axiom_eqv_transitive(
        det2d(v_minus_u, neg_u),
        det2d(v, neg_u).sub(det2d(u, neg_u)),
        det2d(v, neg_u).sub(T::zero()),
    );
    T::axiom_eqv_transitive(
        det2d(v_minus_u, neg_u),
        det2d(v, neg_u).sub(T::zero()),
        det2d(v, neg_u),
    );

    // det2d(v, -u) ≡ -det2d(v, u)  [neg_right]
    lemma_det2d_neg_right::<T>(v, u);

    // -det2d(v, u) ≡ det2d(u, v)  [antisymmetric gives det2d(v,u) ≡ -det2d(u,v),
    //   so -det2d(v,u) ≡ -(-det2d(u,v)) ≡ det2d(u,v)]
    lemma_det2d_antisymmetric::<T>(v, u);
    T::axiom_neg_congruence(det2d(v, u), det2d(u, v).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(det2d(u, v));
    T::axiom_eqv_transitive(
        det2d(v, u).neg(),
        det2d(u, v).neg().neg(),
        det2d(u, v),
    );

    // Chain: det2d(v, -u) ≡ -det2d(v, u) ≡ det2d(u, v)
    T::axiom_eqv_transitive(
        det2d(v, neg_u),
        det2d(v, u).neg(),
        det2d(u, v),
    );

    // Chain: det2d(v_minus_u, neg_u) ≡ det2d(v, neg_u) ≡ det2d(u, v) = orient2d(a,b,c)
    T::axiom_eqv_transitive(
        det2d(v_minus_u, neg_u),
        det2d(v, neg_u),
        det2d(u, v),
    );

    // orient2d(b,c,a) = det2d(c_minus_b, a_minus_b) ≡ det2d(v_minus_u, neg_u) ≡ det2d(u, v) = orient2d(a,b,c)
    T::axiom_eqv_transitive(
        orient2d(b, c, a),
        det2d(v_minus_u, neg_u),
        orient2d(a, b, c),
    );

    // We need orient2d(a,b,c) ≡ orient2d(b,c,a), so swap
    T::axiom_eqv_symmetric(orient2d(b, c, a), orient2d(a, b, c));
}

/// orient2d(a, b, c) is translation-invariant:
/// orient2d(add_vec2(a,t), add_vec2(b,t), add_vec2(c,t)) ≡ orient2d(a, b, c)
pub proof fn lemma_orient2d_translation<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, t: Vec2<T>,
)
    ensures
        orient2d(add_vec2(a, t), add_vec2(b, t), add_vec2(c, t)).eqv(orient2d(a, b, c)),
{
    let at = add_vec2(a, t);
    let bt = add_vec2(b, t);
    let ct = add_vec2(c, t);

    // sub2(bt, at) ≡ sub2(b, a) via translation lemma
    lemma_sub2_translation::<T>(a, b, t);
    // sub2(ct, at) ≡ sub2(c, a) via translation lemma
    lemma_sub2_translation::<T>(a, c, t);

    // orient2d(at,bt,ct) = det2d(sub2(bt,at), sub2(ct,at))
    //                    ≡ det2d(sub2(b,a), sub2(c,a))       [congruence]
    //                    = orient2d(a,b,c)
    lemma_det2d_congruence::<T>(sub2(bt, at), sub2(b, a), sub2(ct, at), sub2(c, a));
}

} // verus!
