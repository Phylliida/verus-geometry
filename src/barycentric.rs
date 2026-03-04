use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_linalg::vec2::Vec2;
use crate::point2::*;
use crate::orient2d::*;

verus! {

// =========================================================================
// Barycentric coordinate specs
// =========================================================================

/// Unnormalized barycentric coordinates of p with respect to triangle (a, b, c).
/// The triple (orient2d(b,c,p), orient2d(c,a,p), orient2d(a,b,p)).
pub open spec fn barycentric_unnorm_2d<T: Ring>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> (T, T, T) {
    (orient2d(b, c, p), orient2d(c, a, p), orient2d(a, b, p))
}

/// Normalized barycentric coordinates: each component divided by orient2d(a, b, c).
/// Requires non-degenerate triangle (orient2d(a,b,c) ≢ 0).
pub open spec fn barycentric_coords_2d<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> (T, T, T) {
    let area = orient2d(a, b, c);
    (
        orient2d(b, c, p).div(area),
        orient2d(c, a, p).div(area),
        orient2d(a, b, p).div(area),
    )
}

// =========================================================================
// Barycentric lemmas
// =========================================================================

/// orient2d(a, b, a) ≡ 0: repeated first and third vertex.
pub proof fn lemma_orient2d_repeated_ac<T: Ring>(a: Point2<T>, b: Point2<T>)
    ensures
        orient2d(a, b, a).eqv(T::zero()),
{
    // orient2d(a, b, a) ≡ orient2d(b, a, a) [cyclic]
    lemma_orient2d_cyclic::<T>(a, b, a);
    // orient2d(b, a, a) = det2d(sub2(a, b), sub2(a, b)) ≡ 0 [self_zero]
    lemma_det2d_self_zero::<T>(sub2(a, b));
    // orient2d(a, b, a) ≡ orient2d(b, a, a) ≡ 0
    T::axiom_eqv_transitive(orient2d(a, b, a), orient2d(b, a, a), T::zero());
}

/// Unnormalized sum at vertex a:
/// orient2d(b,c,a) + orient2d(c,a,a) + orient2d(a,b,a) ≡ orient2d(a,b,c).
/// This is a special case of the general partition-of-unity identity.
pub proof fn lemma_barycentric_sum_at_vertex_a<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d(b, c, a).add(orient2d(c, a, a)).add(orient2d(a, b, a))
            .eqv(orient2d(a, b, c)),
{
    // orient2d(c, a, a) ≡ 0 [degenerate_bc on (c, a)]
    lemma_orient2d_degenerate_bc::<T>(c, a);
    // orient2d(a, b, a) ≡ 0 [repeated_ac]
    lemma_orient2d_repeated_ac::<T>(a, b);

    // orient2d(b,c,a) + orient2d(c,a,a) ≡ orient2d(b,c,a) + 0
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        orient2d(b, c, a), orient2d(c, a, a), T::zero(),
    );
    // orient2d(b,c,a) + 0 ≡ orient2d(b,c,a)
    T::axiom_add_zero_right(orient2d(b, c, a));
    T::axiom_eqv_transitive(
        orient2d(b, c, a).add(orient2d(c, a, a)),
        orient2d(b, c, a).add(T::zero()),
        orient2d(b, c, a),
    );

    // (orient2d(b,c,a) + orient2d(c,a,a)) + orient2d(a,b,a)
    // ≡ orient2d(b,c,a) + orient2d(a,b,a)
    T::axiom_add_congruence_left(
        orient2d(b, c, a).add(orient2d(c, a, a)),
        orient2d(b, c, a),
        orient2d(a, b, a),
    );
    // orient2d(b,c,a) + orient2d(a,b,a) ≡ orient2d(b,c,a) + 0
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        orient2d(b, c, a), orient2d(a, b, a), T::zero(),
    );
    // orient2d(b,c,a) + 0 ≡ orient2d(b,c,a)
    T::axiom_eqv_transitive(
        orient2d(b, c, a).add(orient2d(a, b, a)),
        orient2d(b, c, a).add(T::zero()),
        orient2d(b, c, a),
    );
    // Full chain
    T::axiom_eqv_transitive(
        orient2d(b, c, a).add(orient2d(c, a, a)).add(orient2d(a, b, a)),
        orient2d(b, c, a).add(orient2d(a, b, a)),
        orient2d(b, c, a),
    );

    // orient2d(b,c,a) ≡ orient2d(a,b,c) [cyclic, reversed]
    lemma_orient2d_cyclic::<T>(a, b, c);
    T::axiom_eqv_symmetric(orient2d(a, b, c), orient2d(b, c, a));
    // orient2d(b,c,a) ≡ orient2d(c,a,b) [cyclic on (b,c,a)]
    // Actually we just need orient2d(b,c,a) ≡ orient2d(a,b,c), and the
    // symmetric of orient2d(a,b,c) ≡ orient2d(b,c,a) gives us that.

    T::axiom_eqv_transitive(
        orient2d(b, c, a).add(orient2d(c, a, a)).add(orient2d(a, b, a)),
        orient2d(b, c, a),
        orient2d(a, b, c),
    );
}

/// Unnormalized sum at vertex b (by symmetry argument via cyclic):
/// orient2d(b,c,b) + orient2d(c,a,b) + orient2d(a,b,b) ≡ orient2d(a,b,c).
pub proof fn lemma_barycentric_sum_at_vertex_b<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d(b, c, b).add(orient2d(c, a, b)).add(orient2d(a, b, b))
            .eqv(orient2d(a, b, c)),
{
    // orient2d(b, c, b) ≡ 0 [repeated_ac on (b, c)]
    lemma_orient2d_repeated_ac::<T>(b, c);
    // orient2d(a, b, b) ≡ 0 [degenerate_bc on (a, b)]
    lemma_orient2d_degenerate_bc::<T>(a, b);

    // orient2d(b,c,b) + orient2d(c,a,b) ≡ 0 + orient2d(c,a,b) ≡ orient2d(c,a,b)
    T::axiom_add_congruence_left(
        orient2d(b, c, b), T::zero(), orient2d(c, a, b),
    );
    T::axiom_add_commutative(T::zero(), orient2d(c, a, b));
    T::axiom_add_zero_right(orient2d(c, a, b));
    T::axiom_eqv_transitive(
        T::zero().add(orient2d(c, a, b)),
        orient2d(c, a, b).add(T::zero()),
        orient2d(c, a, b),
    );
    T::axiom_eqv_transitive(
        orient2d(b, c, b).add(orient2d(c, a, b)),
        T::zero().add(orient2d(c, a, b)),
        orient2d(c, a, b),
    );

    // (... ) + orient2d(a,b,b) ≡ orient2d(c,a,b) + orient2d(a,b,b)
    T::axiom_add_congruence_left(
        orient2d(b, c, b).add(orient2d(c, a, b)),
        orient2d(c, a, b),
        orient2d(a, b, b),
    );
    // orient2d(c,a,b) + orient2d(a,b,b) ≡ orient2d(c,a,b) + 0 ≡ orient2d(c,a,b)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        orient2d(c, a, b), orient2d(a, b, b), T::zero(),
    );
    T::axiom_add_zero_right(orient2d(c, a, b));
    T::axiom_eqv_transitive(
        orient2d(c, a, b).add(orient2d(a, b, b)),
        orient2d(c, a, b).add(T::zero()),
        orient2d(c, a, b),
    );
    T::axiom_eqv_transitive(
        orient2d(b, c, b).add(orient2d(c, a, b)).add(orient2d(a, b, b)),
        orient2d(c, a, b).add(orient2d(a, b, b)),
        orient2d(c, a, b),
    );

    // orient2d(c,a,b) ≡ orient2d(a,b,c) [cyclic twice]
    lemma_orient2d_cyclic::<T>(c, a, b);
    // orient2d(c,a,b) ≡ orient2d(a,b,c)
    T::axiom_eqv_transitive(
        orient2d(b, c, b).add(orient2d(c, a, b)).add(orient2d(a, b, b)),
        orient2d(c, a, b),
        orient2d(a, b, c),
    );
}

/// Unnormalized sum at vertex c:
/// orient2d(b,c,c) + orient2d(c,a,c) + orient2d(a,b,c) ≡ orient2d(a,b,c).
pub proof fn lemma_barycentric_sum_at_vertex_c<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d(b, c, c).add(orient2d(c, a, c)).add(orient2d(a, b, c))
            .eqv(orient2d(a, b, c)),
{
    // orient2d(b, c, c) ≡ 0 [degenerate_bc on (b, c)]
    lemma_orient2d_degenerate_bc::<T>(b, c);
    // orient2d(c, a, c) ≡ 0 [repeated_ac on (c, a)]
    lemma_orient2d_repeated_ac::<T>(c, a);

    // orient2d(b,c,c) + orient2d(c,a,c) ≡ 0 + 0
    T::axiom_add_congruence_left(
        orient2d(b, c, c), T::zero(), orient2d(c, a, c),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), orient2d(c, a, c), T::zero(),
    );
    T::axiom_eqv_transitive(
        orient2d(b, c, c).add(orient2d(c, a, c)),
        T::zero().add(orient2d(c, a, c)),
        T::zero().add(T::zero()),
    );
    // 0 + 0 ≡ 0
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        orient2d(b, c, c).add(orient2d(c, a, c)),
        T::zero().add(T::zero()),
        T::zero(),
    );

    // (...) + orient2d(a,b,c) ≡ 0 + orient2d(a,b,c)
    T::axiom_add_congruence_left(
        orient2d(b, c, c).add(orient2d(c, a, c)),
        T::zero(),
        orient2d(a, b, c),
    );
    // 0 + orient2d(a,b,c) ≡ orient2d(a,b,c)
    T::axiom_add_commutative(T::zero(), orient2d(a, b, c));
    T::axiom_add_zero_right(orient2d(a, b, c));
    T::axiom_eqv_transitive(
        T::zero().add(orient2d(a, b, c)),
        orient2d(a, b, c).add(T::zero()),
        orient2d(a, b, c),
    );
    T::axiom_eqv_transitive(
        orient2d(b, c, c).add(orient2d(c, a, c)).add(orient2d(a, b, c)),
        T::zero().add(orient2d(a, b, c)),
        orient2d(a, b, c),
    );
}

// =========================================================================
// Partition of unity helpers
// =========================================================================

/// a - 0 ≡ a for Ring elements.
pub proof fn lemma_sub_zero<T: Ring>(a: T)
    ensures
        a.sub(T::zero()).eqv(a),
{
    T::axiom_sub_is_add_neg(a, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero().neg()), a.add(T::zero()));
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero()), a);
}

/// det2d(v.sub(u), q.sub(u)) ≡ det2d(v, q) - det2d(v, u) - det2d(u, q)
///
/// Expansion via sub_left and sub_right, with det2d(u, u) = 0.
pub proof fn lemma_det2d_expand_vsub_qsub<T: Ring>(
    u: Vec2<T>, v: Vec2<T>, q: Vec2<T>,
)
    ensures
        det2d(v.sub(u), q.sub(u)).eqv(
            det2d(v, q).sub(det2d(v, u)).sub(det2d(u, q))
        ),
{
    // Step 1: sub_left: det2d(v-u, q-u) ≡ det2d(v, q-u) - det2d(u, q-u)
    lemma_det2d_sub_left::<T>(v, u, q.sub(u));

    // Step 2: sub_right on det2d(v, q-u) ≡ det2d(v, q) - det2d(v, u)
    lemma_det2d_sub_right::<T>(v, q, u);

    // Step 3: sub_right on det2d(u, q-u) ≡ det2d(u, q) - det2d(u, u)
    lemma_det2d_sub_right::<T>(u, q, u);

    // Step 4: det2d(u, u) ≡ 0
    lemma_det2d_self_zero::<T>(u);

    // det2d(u, q) - det2d(u, u) ≡ det2d(u, q) - 0 ≡ det2d(u, q)
    T::axiom_eqv_reflexive(det2d(u, q));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(u, q), det2d(u, q), det2d(u, u), T::zero(),
    );
    lemma_sub_zero::<T>(det2d(u, q));
    T::axiom_eqv_transitive(
        det2d(u, q.sub(u)),
        det2d(u, q).sub(det2d(u, u)),
        det2d(u, q).sub(T::zero()),
    );
    T::axiom_eqv_transitive(
        det2d(u, q.sub(u)),
        det2d(u, q).sub(T::zero()),
        det2d(u, q),
    );

    // Now: det2d(v-u, q-u) ≡ det2d(v, q-u) - det2d(u, q-u)
    //                       ≡ (det2d(v,q) - det2d(v,u)) - det2d(u,q)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(v, q.sub(u)), det2d(v, q).sub(det2d(v, u)),
        det2d(u, q.sub(u)), det2d(u, q),
    );
    T::axiom_eqv_transitive(
        det2d(v.sub(u), q.sub(u)),
        det2d(v, q.sub(u)).sub(det2d(u, q.sub(u))),
        det2d(v, q).sub(det2d(v, u)).sub(det2d(u, q)),
    );
}

/// det2d(v.neg(), q.sub(v)) ≡ -det2d(v, q)
///
/// Uses neg_left and sub_right with det2d(v,v) = 0.
pub proof fn lemma_det2d_expand_vneg_qsub<T: Ring>(
    v: Vec2<T>, q: Vec2<T>,
)
    ensures
        det2d(v.neg(), q.sub(v)).eqv(det2d(v, q).neg()),
{
    // neg_left: det2d(-v, q-v) ≡ -det2d(v, q-v)
    lemma_det2d_neg_left::<T>(v, q.sub(v));

    // sub_right: det2d(v, q-v) ≡ det2d(v, q) - det2d(v, v)
    lemma_det2d_sub_right::<T>(v, q, v);

    // det2d(v, v) ≡ 0
    lemma_det2d_self_zero::<T>(v);

    // det2d(v, q) - det2d(v, v) ≡ det2d(v, q) - 0 ≡ det2d(v, q)
    T::axiom_eqv_reflexive(det2d(v, q));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(v, q), det2d(v, q), det2d(v, v), T::zero(),
    );
    lemma_sub_zero::<T>(det2d(v, q));
    T::axiom_eqv_transitive(
        det2d(v, q.sub(v)),
        det2d(v, q).sub(det2d(v, v)),
        det2d(v, q).sub(T::zero()),
    );
    T::axiom_eqv_transitive(
        det2d(v, q.sub(v)),
        det2d(v, q).sub(T::zero()),
        det2d(v, q),
    );

    // -det2d(v, q-v) ≡ -det2d(v, q)
    T::axiom_neg_congruence(det2d(v, q.sub(v)), det2d(v, q));

    // Chain: det2d(-v, q-v) ≡ -det2d(v, q-v) ≡ -det2d(v, q)
    T::axiom_eqv_transitive(
        det2d(v.neg(), q.sub(v)),
        det2d(v, q.sub(v)).neg(),
        det2d(v, q).neg(),
    );
}

// =========================================================================
// Partition of unity (general case)
// =========================================================================

/// orient2d(b,c,p) + orient2d(c,a,p) + orient2d(a,b,p) ≡ orient2d(a,b,c)
/// for any point p. This is the general partition-of-unity identity
/// for unnormalized barycentric coordinates.
///
/// Proof outline: Let u = b-a, v = c-a, q = p-a.
/// Then orient2d(b,c,p) ≡ det2d(v-u, q-u), orient2d(c,a,p) ≡ det2d(-v, q-v),
/// orient2d(a,b,p) = det2d(u, q).
/// Reorder sum as (T1+T3)+T2, use sub_left to get det2d(v, q-u),
/// then sub_right + antisymmetric to reach det2d(u, v).
pub proof fn lemma_barycentric_partition_of_unity<T: Ring>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d(b, c, p).add(orient2d(c, a, p)).add(orient2d(a, b, p))
            .eqv(orient2d(a, b, c)),
{
    let u = sub2(b, a);
    let v = sub2(c, a);
    let q = sub2(p, a);

    let t1 = orient2d(b, c, p);
    let t2 = orient2d(c, a, p);
    let t3 = orient2d(a, b, p);

    // =============================================
    // Phase 1: Establish congruences via rebase
    // =============================================

    // sub2(c, b) ≡ v.sub(u)
    lemma_sub2_rebase::<T>(c, b, a);
    // sub2(p, b) ≡ q.sub(u)
    lemma_sub2_rebase::<T>(p, b, a);
    // sub2(a, c) ≡ v.neg()
    lemma_sub2_antisymmetric::<T>(a, c);
    // sub2(p, c) ≡ q.sub(v)
    lemma_sub2_rebase::<T>(p, c, a);

    // t1 = det2d(sub2(c,b), sub2(p,b)) ≡ det2d(v.sub(u), q.sub(u))
    lemma_det2d_congruence::<T>(sub2(c, b), v.sub(u), sub2(p, b), q.sub(u));
    // t2 = det2d(sub2(a,c), sub2(p,c)) ≡ det2d(v.neg(), q.sub(v))
    lemma_det2d_congruence::<T>(sub2(a, c), v.neg(), sub2(p, c), q.sub(v));
    // t3 = det2d(u, q) [directly, no rebase needed]

    // =============================================
    // Phase 2: Reorder sum as (T1 + T3) + T2
    // =============================================

    // (T1 + T2) + T3 ≡ (T1 + T3) + T2 via assoc + comm + assoc
    T::axiom_add_associative(t1, t2, t3);
    T::axiom_add_commutative(t2, t3);
    additive_group_lemmas::lemma_add_congruence_right::<T>(t1, t2.add(t3), t3.add(t2));
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3),
        t1.add(t2.add(t3)),
        t1.add(t3.add(t2)),
    );
    T::axiom_add_associative(t1, t3, t2);
    T::axiom_eqv_symmetric(t1.add(t3).add(t2), t1.add(t3.add(t2)));
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3),
        t1.add(t3.add(t2)),
        t1.add(t3).add(t2),
    );

    // =============================================
    // Phase 3: T1 + T3 ≡ det2d(v, q.sub(u))
    // =============================================

    // From sub_left: det2d(v.sub(u), q.sub(u)) ≡ det2d(v, q.sub(u)).sub(det2d(u, q.sub(u)))
    lemma_det2d_sub_left::<T>(v, u, q.sub(u));
    // So: det2d(v.sub(u), q.sub(u)).add(det2d(u, q.sub(u))) ≡ det2d(v, q.sub(u))
    //   via (a - b) + b ≡ a [sub_then_add_cancel]
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(
        det2d(v, q.sub(u)), det2d(u, q.sub(u)),
    );

    // But we have t1 ≡ det2d(v.sub(u), q.sub(u)) and t3 = det2d(u, q), not det2d(u, q.sub(u)).
    // Need: det2d(u, q.sub(u)) ≡ det2d(u, q) [because det2d(u, u) = 0]
    lemma_det2d_sub_right::<T>(u, q, u);
    lemma_det2d_self_zero::<T>(u);
    // det2d(u, q.sub(u)) ≡ det2d(u, q).sub(det2d(u, u)) ≡ det2d(u, q).sub(0) ≡ det2d(u, q)
    T::axiom_eqv_reflexive(det2d(u, q));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        det2d(u, q), det2d(u, q), det2d(u, u), T::zero(),
    );
    T::axiom_eqv_transitive(
        det2d(u, q.sub(u)),
        det2d(u, q).sub(det2d(u, u)),
        det2d(u, q).sub(T::zero()),
    );
    // a - 0 ≡ a
    lemma_sub_zero::<T>(det2d(u, q));
    T::axiom_eqv_transitive(
        det2d(u, q.sub(u)),
        det2d(u, q).sub(T::zero()),
        det2d(u, q),
    );
    // det2d(u, q.sub(u)) ≡ det2d(u, q) = t3 ✓

    // Now bridge: t1.add(t3) where t1 ≡ det2d(v.sub(u), q.sub(u)):
    // Replace t3 with det2d(u, q.sub(u)) [eqv], add to t1 ≡ det2d(v.sub(u), q.sub(u)):
    T::axiom_eqv_symmetric(det2d(u, q.sub(u)), det2d(u, q));
    // det2d(u, q) ≡ det2d(u, q.sub(u))
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1, det2d(v.sub(u), q.sub(u)),
        t3, det2d(u, q.sub(u)),
    );
    // t1 + t3 ≡ det2d(v.sub(u), q.sub(u)) + det2d(u, q.sub(u))
    // Bridge: det2d(v.sub(u), q.sub(u)) ≡ det2d(v, q.sub(u)).sub(det2d(u, q.sub(u))) [from sub_left]
    // so (..).add(det2d(u, q.sub(u))) on both sides:
    T::axiom_add_congruence_left(
        det2d(v.sub(u), q.sub(u)),
        det2d(v, q.sub(u)).sub(det2d(u, q.sub(u))),
        det2d(u, q.sub(u)),
    );
    // det2d(v,q.sub(u)).sub(det2d(u,q.sub(u))).add(det2d(u,q.sub(u))) ≡ det2d(v,q.sub(u))
    // [from sub_then_add_cancel]
    T::axiom_eqv_transitive(
        det2d(v.sub(u), q.sub(u)).add(det2d(u, q.sub(u))),
        det2d(v, q.sub(u)).sub(det2d(u, q.sub(u))).add(det2d(u, q.sub(u))),
        det2d(v, q.sub(u)),
    );
    T::axiom_eqv_transitive(
        t1.add(t3),
        det2d(v.sub(u), q.sub(u)).add(det2d(u, q.sub(u))),
        det2d(v, q.sub(u)),
    );
    // t1 + t3 ≡ det2d(v, q.sub(u)) ✓

    // =============================================
    // Phase 4: (T1 + T3) + T2 ≡ -det2d(v, u)
    // =============================================

    // t2 ≡ det2d(v.neg(), q.sub(v)) ≡ det2d(v, q).neg()
    lemma_det2d_expand_vneg_qsub::<T>(v, q);
    T::axiom_eqv_transitive(
        t2,
        det2d(v.neg(), q.sub(v)),
        det2d(v, q).neg(),
    );

    // (T1+T3) + T2 ≡ det2d(v, q.sub(u)) + det2d(v, q).neg()
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1.add(t3), det2d(v, q.sub(u)),
        t2, det2d(v, q).neg(),
    );

    // det2d(v, q.sub(u)) = det2d(v, q) - det2d(v, u) [sub_right]
    lemma_det2d_sub_right::<T>(v, q, u);

    // (det2d(v,q) - det2d(v,u)) + det2d(v,q).neg()
    // = (det2d(v,q) - det2d(v,u)) + (-det2d(v,q))
    // via sub_then_add_cancel reversed: (a - b) + (-a) ≡ -b? No...
    // Actually: (a - b) + (-a) = a + (-b) + (-a) = (a + (-a)) + (-b) = 0 + (-b) = -b
    // i.e., a.sub(b).add(a.neg()) ≡ b.neg()
    // From sub_then_add: a.sub(b).add(b) ≡ a.
    // We need: det2d(v,q).sub(det2d(v,u)).add(det2d(v,q).neg()) ≡ det2d(v,u).neg()

    // Use: x.sub(y) = x + (-y). So x.sub(y).add(x.neg()) = x + (-y) + (-x) = (x + (-x)) + (-y) = (-y).
    // By sub_is_add_neg + rearrange:
    let dv_q = det2d(v, q);
    let dv_u = det2d(v, u);

    T::axiom_sub_is_add_neg(dv_q, dv_u);
    // dv_q.sub(dv_u) ≡ dv_q.add(dv_u.neg())
    T::axiom_add_congruence_left(
        dv_q.sub(dv_u), dv_q.add(dv_u.neg()), dv_q.neg(),
    );
    // dv_q.sub(dv_u).add(dv_q.neg()) ≡ dv_q.add(dv_u.neg()).add(dv_q.neg())
    // Associate: ≡ dv_q.add(dv_u.neg().add(dv_q.neg()))
    T::axiom_add_associative(dv_q, dv_u.neg(), dv_q.neg());
    T::axiom_eqv_transitive(
        dv_q.sub(dv_u).add(dv_q.neg()),
        dv_q.add(dv_u.neg()).add(dv_q.neg()),
        dv_q.add(dv_u.neg().add(dv_q.neg())),
    );
    // Commute inner: dv_u.neg().add(dv_q.neg()) ≡ dv_q.neg().add(dv_u.neg())
    T::axiom_add_commutative(dv_u.neg(), dv_q.neg());
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        dv_q, dv_u.neg().add(dv_q.neg()), dv_q.neg().add(dv_u.neg()),
    );
    T::axiom_eqv_transitive(
        dv_q.sub(dv_u).add(dv_q.neg()),
        dv_q.add(dv_u.neg().add(dv_q.neg())),
        dv_q.add(dv_q.neg().add(dv_u.neg())),
    );
    // Re-associate: dv_q.add(dv_q.neg().add(dv_u.neg())) ≡ dv_q.add(dv_q.neg()).add(dv_u.neg())
    T::axiom_add_associative(dv_q, dv_q.neg(), dv_u.neg());
    T::axiom_eqv_symmetric(
        dv_q.add(dv_q.neg()).add(dv_u.neg()),
        dv_q.add(dv_q.neg().add(dv_u.neg())),
    );
    T::axiom_eqv_transitive(
        dv_q.sub(dv_u).add(dv_q.neg()),
        dv_q.add(dv_q.neg().add(dv_u.neg())),
        dv_q.add(dv_q.neg()).add(dv_u.neg()),
    );
    // dv_q + dv_q.neg() ≡ 0
    T::axiom_add_inverse_right(dv_q);
    T::axiom_add_congruence_left(
        dv_q.add(dv_q.neg()), T::zero(), dv_u.neg(),
    );
    T::axiom_eqv_transitive(
        dv_q.sub(dv_u).add(dv_q.neg()),
        dv_q.add(dv_q.neg()).add(dv_u.neg()),
        T::zero().add(dv_u.neg()),
    );
    // 0 + x ≡ x
    T::axiom_add_commutative(T::zero(), dv_u.neg());
    T::axiom_add_zero_right(dv_u.neg());
    T::axiom_eqv_transitive(
        T::zero().add(dv_u.neg()),
        dv_u.neg().add(T::zero()),
        dv_u.neg(),
    );
    T::axiom_eqv_transitive(
        dv_q.sub(dv_u).add(dv_q.neg()),
        T::zero().add(dv_u.neg()),
        dv_u.neg(),
    );

    // Bridge: det2d(v, q.sub(u)).add(det2d(v,q).neg()) ≡ dv_q.sub(dv_u).add(dv_q.neg())
    T::axiom_add_congruence_left(
        det2d(v, q.sub(u)), dv_q.sub(dv_u), dv_q.neg(),
    );
    T::axiom_eqv_transitive(
        det2d(v, q.sub(u)).add(dv_q.neg()),
        dv_q.sub(dv_u).add(dv_q.neg()),
        dv_u.neg(),
    );

    // So: (T1+T3) + T2 ≡ det2d(v, q.sub(u)) + det2d(v,q).neg() ≡ dv_u.neg()
    T::axiom_eqv_transitive(
        t1.add(t3).add(t2),
        det2d(v, q.sub(u)).add(dv_q.neg()),
        dv_u.neg(),
    );

    // =============================================
    // Phase 5: -det2d(v, u) ≡ det2d(u, v) = orient2d(a, b, c)
    // =============================================

    // antisymmetric: det2d(v, u) ≡ det2d(u, v).neg()
    lemma_det2d_antisymmetric::<T>(v, u);
    // neg both sides: det2d(v, u).neg() ≡ det2d(u, v).neg().neg()
    T::axiom_neg_congruence(det2d(v, u), det2d(u, v).neg());
    // neg_involution: det2d(u, v).neg().neg() ≡ det2d(u, v)
    additive_group_lemmas::lemma_neg_involution::<T>(det2d(u, v));
    T::axiom_eqv_transitive(
        dv_u.neg(),
        det2d(u, v).neg().neg(),
        det2d(u, v),
    );
    // det2d(u, v) = orient2d(a, b, c) [definitionally]

    // =============================================
    // Phase 6: Final chain
    // =============================================

    // (T1+T2)+T3 ≡ (T1+T3)+T2 ≡ dv_u.neg() ≡ det2d(u, v) = orient2d(a, b, c)
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3),
        t1.add(t3).add(t2),
        dv_u.neg(),
    );
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3),
        dv_u.neg(),
        orient2d(a, b, c),
    );
}

/// For non-degenerate triangle, normalized barycentric coordinates sum to 1:
/// u/area + v/area + w/area ≡ 1.
///
/// Follows from partition_of_unity by dividing both sides by orient2d(a,b,c).
pub proof fn lemma_barycentric_coords_sum_to_one<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        !orient2d(a, b, c).eqv(T::zero()),
    ensures ({
        let (u, v, w) = barycentric_coords_2d(p, a, b, c);
        u.add(v).add(w).eqv(T::one())
    }),
{
    let area = orient2d(a, b, c);
    let t1 = orient2d(b, c, p);
    let t2 = orient2d(c, a, p);
    let t3 = orient2d(a, b, p);

    // Step 1: t1+t2+t3 ≡ area
    lemma_barycentric_partition_of_unity::<T>(p, a, b, c);

    // Step 2: (t1+t2)/area + t3/area ≡ ((t1+t2)+t3)/area  [div_distributes reversed]
    field_lemmas::lemma_div_distributes_over_add::<T>(t1.add(t2), t3, area);
    T::axiom_eqv_symmetric(
        t1.add(t2).add(t3).div(area),
        t1.add(t2).div(area).add(t3.div(area)),
    );

    // Step 3: t1/area + t2/area ≡ (t1+t2)/area  [div_distributes reversed]
    field_lemmas::lemma_div_distributes_over_add::<T>(t1, t2, area);
    T::axiom_eqv_symmetric(
        t1.add(t2).div(area),
        t1.div(area).add(t2.div(area)),
    );

    // Step 4: (t1/a + t2/a) + t3/a ≡ (t1+t2)/a + t3/a
    T::axiom_add_congruence_left(
        t1.div(area).add(t2.div(area)),
        t1.add(t2).div(area),
        t3.div(area),
    );

    // Step 5: (t1/a + t2/a) + t3/a ≡ (t1+t2+t3)/a
    T::axiom_eqv_transitive(
        t1.div(area).add(t2.div(area)).add(t3.div(area)),
        t1.add(t2).div(area).add(t3.div(area)),
        t1.add(t2).add(t3).div(area),
    );

    // Step 6: (t1+t2+t3)/area ≡ area/area [div congruence via mul_recip]
    T::axiom_div_is_mul_recip(t1.add(t2).add(t3), area);
    T::axiom_div_is_mul_recip(area, area);
    T::axiom_mul_congruence_left(t1.add(t2).add(t3), area, area.recip());
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3).div(area),
        t1.add(t2).add(t3).mul(area.recip()),
        area.mul(area.recip()),
    );
    T::axiom_eqv_symmetric(area.div(area), area.mul(area.recip()));
    T::axiom_eqv_transitive(
        t1.add(t2).add(t3).div(area),
        area.mul(area.recip()),
        area.div(area),
    );

    // Step 7: area/area ≡ 1
    field_lemmas::lemma_div_self::<T>(area);

    // Step 8: Final chain
    T::axiom_eqv_transitive(
        t1.div(area).add(t2.div(area)).add(t3.div(area)),
        t1.add(t2).add(t3).div(area),
        area.div(area),
    );
    T::axiom_eqv_transitive(
        t1.div(area).add(t2.div(area)).add(t3.div(area)),
        area.div(area),
        T::one(),
    );
}

// =========================================================================
// Reconstruction helpers: Ring triple-product rearrangements
// =========================================================================

/// a*(b*c) ≡ c*(a*b) — cycle right in a triple product.
pub proof fn lemma_mul_cycle_right<T: Ring>(a: T, b: T, c: T)
    ensures a.mul(b.mul(c)).eqv(c.mul(a.mul(b)))
{
    T::axiom_mul_associative(a, b, c);
    T::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
    T::axiom_mul_commutative(a.mul(b), c);
    T::axiom_eqv_transitive(a.mul(b.mul(c)), a.mul(b).mul(c), c.mul(a.mul(b)));
}

/// a*(b*c) ≡ c*(b*a) — swap outer factors in a triple product.
pub proof fn lemma_mul_swap_outer<T: Ring>(a: T, b: T, c: T)
    ensures a.mul(b.mul(c)).eqv(c.mul(b.mul(a)))
{
    lemma_mul_cycle_right::<T>(a, b, c);
    // a*(b*c) ≡ c*(a*b)
    T::axiom_mul_commutative(a, b);
    ring_lemmas::lemma_mul_congruence_right::<T>(c, a.mul(b), b.mul(a));
    T::axiom_eqv_transitive(a.mul(b.mul(c)), c.mul(a.mul(b)), c.mul(b.mul(a)));
}

/// a*(b*c) ≡ b*(a*c) — swap first two factors in a triple product.
pub proof fn lemma_mul_swap_first_two<T: Ring>(a: T, b: T, c: T)
    ensures a.mul(b.mul(c)).eqv(b.mul(a.mul(c)))
{
    T::axiom_mul_associative(a, b, c);
    T::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
    T::axiom_mul_commutative(a, b);
    T::axiom_mul_congruence_left(a.mul(b), b.mul(a), c);
    T::axiom_mul_associative(b, a, c);
    T::axiom_eqv_transitive(a.mul(b.mul(c)), a.mul(b).mul(c), b.mul(a).mul(c));
    T::axiom_eqv_transitive(a.mul(b.mul(c)), b.mul(a).mul(c), b.mul(a.mul(c)));
}

/// (a/b)*c ≡ (a*c)/b for nonzero b.
pub proof fn lemma_div_mul_right<T: OrderedField>(a: T, b: T, c: T)
    requires !b.eqv(T::zero()),
    ensures a.div(b).mul(c).eqv(a.mul(c).div(b))
{
    let r = b.recip();
    T::axiom_div_is_mul_recip(a, b);
    T::axiom_mul_congruence_left(a.div(b), a.mul(r), c);
    T::axiom_mul_associative(a, r, c);
    T::axiom_eqv_symmetric(a.mul(r).mul(c), a.mul(r.mul(c)));
    T::axiom_mul_commutative(r, c);
    ring_lemmas::lemma_mul_congruence_right::<T>(a, r.mul(c), c.mul(r));
    T::axiom_mul_associative(a, c, r);
    T::axiom_eqv_symmetric(a.mul(c).mul(r), a.mul(c.mul(r)));
    T::axiom_div_is_mul_recip(a.mul(c), b);
    T::axiom_eqv_symmetric(a.mul(c).div(b), a.mul(c).mul(r));
    // Chain: a.div(b).mul(c) ≡ a.mul(r).mul(c) ≡ a.mul(r.mul(c)) ≡ a.mul(c.mul(r))
    //        ≡ a.mul(c).mul(r) ≡ a.mul(c).div(b)
    T::axiom_eqv_transitive(a.div(b).mul(c), a.mul(r).mul(c), a.mul(r.mul(c)));
    T::axiom_eqv_transitive(a.div(b).mul(c), a.mul(r.mul(c)), a.mul(c.mul(r)));
    T::axiom_eqv_transitive(a.div(b).mul(c), a.mul(c.mul(r)), a.mul(c).mul(r));
    T::axiom_eqv_transitive(a.div(b).mul(c), a.mul(c).mul(r), a.mul(c).div(b));
}

// =========================================================================
// 2D Cramer resolution identity
// =========================================================================

/// Cramer identity: det2d(q,b)*a.k + det2d(a,q)*b.k ≡ q.k*det2d(a,b)
/// for k ∈ {x, y}. This is the 2D analog of Cramer's rule.
pub proof fn lemma_det2d_cramer<T: Ring>(a: Vec2<T>, b: Vec2<T>, q: Vec2<T>)
    ensures
        det2d(q, b).mul(a.x).add(det2d(a, q).mul(b.x)).eqv(q.x.mul(det2d(a, b))),
        det2d(q, b).mul(a.y).add(det2d(a, q).mul(b.y)).eqv(q.y.mul(det2d(a, b))),
{
    // Abbreviations for products
    let qxby = q.x.mul(b.y);
    let qybx = q.y.mul(b.x);
    let axqy = a.x.mul(q.y);
    let ayqx = a.y.mul(q.x);

    // =================== x-component ===================

    // Phase 1: Expand det2d(q,b)*a.x ≡ a.x*qxby - a.x*qybx
    T::axiom_mul_commutative(det2d(q, b), a.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(a.x, qxby, qybx);
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.x), a.x.mul(det2d(q, b)),
        a.x.mul(qxby).sub(a.x.mul(qybx)),
    );

    // Expand det2d(a,q)*b.x ≡ b.x*axqy - b.x*ayqx
    T::axiom_mul_commutative(det2d(a, q), b.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(b.x, axqy, ayqx);
    T::axiom_eqv_transitive(
        det2d(a, q).mul(b.x), b.x.mul(det2d(a, q)),
        b.x.mul(axqy).sub(b.x.mul(ayqx)),
    );

    // Phase 2: Middle terms cancel: a.x*qybx ≡ b.x*axqy
    lemma_mul_cycle_right::<T>(a.x, q.y, b.x);
    // a.x*(q.y*b.x) ≡ b.x*(a.x*q.y) = b.x*axqy ✓

    // Phase 3: (A-B)+(C-D) where B≡C ⟹ A-D
    // A=a.x*qxby, B=a.x*qybx, C=b.x*axqy, D=b.x*ayqx
    T::axiom_eqv_symmetric(a.x.mul(qybx), b.x.mul(axqy));
    T::axiom_eqv_reflexive(b.x.mul(ayqx));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        b.x.mul(axqy), a.x.mul(qybx), b.x.mul(ayqx), b.x.mul(ayqx),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.x.mul(qxby).sub(a.x.mul(qybx)),
        b.x.mul(axqy).sub(b.x.mul(ayqx)),
        a.x.mul(qybx).sub(b.x.mul(ayqx)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        a.x.mul(qxby), a.x.mul(qybx), b.x.mul(ayqx),
    );
    T::axiom_eqv_transitive(
        a.x.mul(qxby).sub(a.x.mul(qybx)).add(b.x.mul(axqy).sub(b.x.mul(ayqx))),
        a.x.mul(qxby).sub(a.x.mul(qybx)).add(a.x.mul(qybx).sub(b.x.mul(ayqx))),
        a.x.mul(qxby).sub(b.x.mul(ayqx)),
    );

    // Connect to original sum
    additive_group_lemmas::lemma_add_congruence::<T>(
        det2d(q, b).mul(a.x), a.x.mul(qxby).sub(a.x.mul(qybx)),
        det2d(a, q).mul(b.x), b.x.mul(axqy).sub(b.x.mul(ayqx)),
    );
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.x).add(det2d(a, q).mul(b.x)),
        a.x.mul(qxby).sub(a.x.mul(qybx)).add(b.x.mul(axqy).sub(b.x.mul(ayqx))),
        a.x.mul(qxby).sub(b.x.mul(ayqx)),
    );

    // Phase 4: Factor A-D into q.x*det2d(a,b)
    // A = a.x*qxby ≡ q.x*(a.x*b.y) via swap_first_two
    lemma_mul_swap_first_two::<T>(a.x, q.x, b.y);
    // D = b.x*ayqx ≡ q.x*(a.y*b.x) via swap_outer
    lemma_mul_swap_outer::<T>(b.x, a.y, q.x);

    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.mul(qxby), q.x.mul(a.x.mul(b.y)),
        b.x.mul(ayqx), q.x.mul(a.y.mul(b.x)),
    );
    // A-D ≡ q.x*axby - q.x*aybx

    ring_lemmas::lemma_mul_distributes_over_sub::<T>(q.x, a.x.mul(b.y), a.y.mul(b.x));
    T::axiom_eqv_symmetric(
        q.x.mul(a.x.mul(b.y).sub(a.y.mul(b.x))),
        q.x.mul(a.x.mul(b.y)).sub(q.x.mul(a.y.mul(b.x))),
    );
    // q.x*axby - q.x*aybx ≡ q.x*det2d(a,b)

    T::axiom_eqv_transitive(
        a.x.mul(qxby).sub(b.x.mul(ayqx)),
        q.x.mul(a.x.mul(b.y)).sub(q.x.mul(a.y.mul(b.x))),
        q.x.mul(det2d(a, b)),
    );

    // Final x chain
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.x).add(det2d(a, q).mul(b.x)),
        a.x.mul(qxby).sub(b.x.mul(ayqx)),
        q.x.mul(det2d(a, b)),
    );

    // =================== y-component ===================
    // Same structure. Cancel: a.y*(q.x*b.y) ≡ b.y*(a.y*q.x)
    // Remain: b.y*(a.x*q.y) - a.y*(q.y*b.x) → q.y*det2d(a,b)

    // Phase 1: Expand det2d(q,b)*a.y
    T::axiom_mul_commutative(det2d(q, b), a.y);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(a.y, qxby, qybx);
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.y), a.y.mul(det2d(q, b)),
        a.y.mul(qxby).sub(a.y.mul(qybx)),
    );

    // Expand det2d(a,q)*b.y
    T::axiom_mul_commutative(det2d(a, q), b.y);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(b.y, axqy, ayqx);
    T::axiom_eqv_transitive(
        det2d(a, q).mul(b.y), b.y.mul(det2d(a, q)),
        b.y.mul(axqy).sub(b.y.mul(ayqx)),
    );

    // Phase 2: First and fourth terms cancel: a.y*qxby ≡ b.y*ayqx
    lemma_mul_cycle_right::<T>(a.y, q.x, b.y);
    // a.y*(q.x*b.y) ≡ b.y*(a.y*q.x) = b.y*ayqx ✓

    // Phase 3: (P-N)+(Q-M) where P≡M. Commute and cancel.
    // P=a.y*qxby, N=a.y*qybx, Q=b.y*axqy, M=b.y*ayqx
    // P≡M established above. Use comm then sub_add_sub.
    T::axiom_eqv_symmetric(a.y.mul(qxby), b.y.mul(ayqx));
    // M≡P, so Q-M ≡ Q-P
    T::axiom_eqv_reflexive(b.y.mul(axqy));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        b.y.mul(axqy), b.y.mul(axqy), b.y.mul(ayqx), a.y.mul(qxby),
    );
    // (P-N)+(Q-M) ≡ (P-N)+(Q-P) via congruence on second summand
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.y.mul(qxby).sub(a.y.mul(qybx)),
        b.y.mul(axqy).sub(b.y.mul(ayqx)),
        b.y.mul(axqy).sub(a.y.mul(qxby)),
    );
    // Commute: (P-N)+(Q-P) ≡ (Q-P)+(P-N) then sub_add_sub → Q-N
    T::axiom_add_commutative(
        a.y.mul(qxby).sub(a.y.mul(qybx)),
        b.y.mul(axqy).sub(a.y.mul(qxby)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        b.y.mul(axqy), a.y.mul(qxby), a.y.mul(qybx),
    );
    T::axiom_eqv_transitive(
        a.y.mul(qxby).sub(a.y.mul(qybx)).add(b.y.mul(axqy).sub(a.y.mul(qxby))),
        b.y.mul(axqy).sub(a.y.mul(qxby)).add(a.y.mul(qxby).sub(a.y.mul(qybx))),
        b.y.mul(axqy).sub(a.y.mul(qybx)),
    );
    T::axiom_eqv_transitive(
        a.y.mul(qxby).sub(a.y.mul(qybx)).add(b.y.mul(axqy).sub(b.y.mul(ayqx))),
        a.y.mul(qxby).sub(a.y.mul(qybx)).add(b.y.mul(axqy).sub(a.y.mul(qxby))),
        b.y.mul(axqy).sub(a.y.mul(qybx)),
    );

    // Connect to original
    additive_group_lemmas::lemma_add_congruence::<T>(
        det2d(q, b).mul(a.y), a.y.mul(qxby).sub(a.y.mul(qybx)),
        det2d(a, q).mul(b.y), b.y.mul(axqy).sub(b.y.mul(ayqx)),
    );
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.y).add(det2d(a, q).mul(b.y)),
        a.y.mul(qxby).sub(a.y.mul(qybx)).add(b.y.mul(axqy).sub(b.y.mul(ayqx))),
        b.y.mul(axqy).sub(a.y.mul(qybx)),
    );

    // Phase 4: Factor Q-N into q.y*det2d(a,b)
    // Q = b.y*axqy ≡ q.y*(a.x*b.y) via swap_outer
    lemma_mul_swap_outer::<T>(b.y, a.x, q.y);
    // N = a.y*qybx ≡ q.y*(a.y*b.x) via swap_first_two
    lemma_mul_swap_first_two::<T>(a.y, q.y, b.x);

    additive_group_lemmas::lemma_sub_congruence::<T>(
        b.y.mul(axqy), q.y.mul(a.x.mul(b.y)),
        a.y.mul(qybx), q.y.mul(a.y.mul(b.x)),
    );

    ring_lemmas::lemma_mul_distributes_over_sub::<T>(q.y, a.x.mul(b.y), a.y.mul(b.x));
    T::axiom_eqv_symmetric(
        q.y.mul(a.x.mul(b.y).sub(a.y.mul(b.x))),
        q.y.mul(a.x.mul(b.y)).sub(q.y.mul(a.y.mul(b.x))),
    );

    T::axiom_eqv_transitive(
        b.y.mul(axqy).sub(a.y.mul(qybx)),
        q.y.mul(a.x.mul(b.y)).sub(q.y.mul(a.y.mul(b.x))),
        q.y.mul(det2d(a, b)),
    );

    // Final y chain
    T::axiom_eqv_transitive(
        det2d(q, b).mul(a.y).add(det2d(a, q).mul(b.y)),
        b.y.mul(axqy).sub(a.y.mul(qybx)),
        q.y.mul(det2d(a, b)),
    );
}

// =========================================================================
// Integral identity helper
// =========================================================================

/// T1*a.x + T2*b.x + T3*c.x ≡ p.x*area and same for y.
/// Uses Cramer identity + partition of unity.
pub proof fn lemma_barycentric_integral_identity<T: Ring>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d(b,c,p).mul(a.x).add(orient2d(c,a,p).mul(b.x)).add(orient2d(a,b,p).mul(c.x))
            .eqv(p.x.mul(orient2d(a,b,c))),
        orient2d(b,c,p).mul(a.y).add(orient2d(c,a,p).mul(b.y)).add(orient2d(a,b,p).mul(c.y))
            .eqv(p.y.mul(orient2d(a,b,c))),
{
    let al = sub2(a, c);  // α
    let be = sub2(b, c);  // β
    let pi = sub2(p, c);  // π
    let t1 = orient2d(b, c, p);
    let t2 = orient2d(c, a, p);
    let t3 = orient2d(a, b, p);
    let area = orient2d(a, b, c);

    // ---- Establish t1 ≡ det2d(π, β) ----
    // sub2(c,b) ≡ β.neg() by antisymmetric
    lemma_sub2_antisymmetric::<T>(c, b);
    // sub2(p,b) ≡ π.sub(β) by rebase
    lemma_sub2_rebase::<T>(p, b, c);
    // t1 = det2d(sub2(c,b), sub2(p,b)) ≡ det2d(β.neg(), π.sub(β))
    lemma_det2d_congruence::<T>(sub2(c, b), be.neg(), sub2(p, b), pi.sub(be));
    // det2d(β.neg(), π.sub(β)) ≡ det2d(β, π).neg()
    lemma_det2d_expand_vneg_qsub::<T>(be, pi);
    T::axiom_eqv_transitive(t1, det2d(be.neg(), pi.sub(be)), det2d(be, pi).neg());
    // det2d(β, π) ≡ det2d(π, β).neg() [antisymmetric]
    lemma_det2d_antisymmetric::<T>(be, pi);
    T::axiom_neg_congruence(det2d(be, pi), det2d(pi, be).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(det2d(pi, be));
    T::axiom_eqv_transitive(
        det2d(be, pi).neg(), det2d(pi, be).neg().neg(), det2d(pi, be),
    );
    T::axiom_eqv_transitive(t1, det2d(be, pi).neg(), det2d(pi, be));

    // ---- Establish area ≡ det2d(α, β) ----
    // orient2d(a,b,c) ≡ orient2d(c,a,b) by double cyclic
    lemma_orient2d_cyclic::<T>(a, b, c);
    lemma_orient2d_cyclic::<T>(b, c, a);
    T::axiom_eqv_transitive(area, orient2d(b, c, a), orient2d(c, a, b));
    // orient2d(c,a,b) = det2d(sub2(a,c), sub2(b,c)) = det2d(α, β)

    // ---- Apply Cramer: det2d(π,β)*α.k + det2d(α,π)*β.k ≡ π.k*det2d(α,β) ----
    lemma_det2d_cramer::<T>(al, be, pi);
    // Note: t2 = orient2d(c,a,p) = det2d(sub2(a,c), sub2(p,c)) = det2d(α, π) [structural]

    // Congruence: t1*α.k + t2*β.k ≡ det2d(π,β)*α.k + det2d(α,π)*β.k ≡ π.k*det2d(α,β)
    // For each component k, we need:
    // t1.mul(α.k) ≡ det2d(π,β).mul(α.k) [by t1 ≡ det2d(π,β)]
    T::axiom_mul_congruence_left(t1, det2d(pi, be), al.x);
    T::axiom_eqv_reflexive(t2.mul(be.x));
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1.mul(al.x), det2d(pi, be).mul(al.x),
        t2.mul(be.x), t2.mul(be.x),
    );
    T::axiom_eqv_transitive(
        t1.mul(al.x).add(t2.mul(be.x)),
        det2d(pi, be).mul(al.x).add(det2d(al, pi).mul(be.x)),
        pi.x.mul(det2d(al, be)),
    );

    // Also need π.x*det2d(α,β) ≡ π.x*area (via area ≡ det2d(α,β), symmetric)
    T::axiom_eqv_symmetric(area, orient2d(c, a, b));
    ring_lemmas::lemma_mul_congruence_right::<T>(pi.x, det2d(al, be), area);
    T::axiom_eqv_transitive(
        t1.mul(al.x).add(t2.mul(be.x)),
        pi.x.mul(det2d(al, be)),
        pi.x.mul(area),
    );
    // ★ t1*α.x + t2*β.x ≡ π.x*area

    // Same for y
    T::axiom_mul_congruence_left(t1, det2d(pi, be), al.y);
    T::axiom_eqv_reflexive(t2.mul(be.y));
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1.mul(al.y), det2d(pi, be).mul(al.y),
        t2.mul(be.y), t2.mul(be.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(al.y).add(t2.mul(be.y)),
        det2d(pi, be).mul(al.y).add(det2d(al, pi).mul(be.y)),
        pi.y.mul(det2d(al, be)),
    );
    ring_lemmas::lemma_mul_congruence_right::<T>(pi.y, det2d(al, be), area);
    T::axiom_eqv_transitive(
        t1.mul(al.y).add(t2.mul(be.y)),
        pi.y.mul(det2d(al, be)),
        pi.y.mul(area),
    );
    // ★ t1*α.y + t2*β.y ≡ π.y*area

    // ---- Convert from rebased to original coords ----
    // For each k ∈ {x, y}:
    //   t1*a.k + t2*b.k + t3*c.k
    //   = t1*(α.k+c.k) + t2*(β.k+c.k) + t3*c.k  [since v.k = v.k-c.k+c.k]
    //   = (t1*α.k + t2*β.k) + (t1+t2+t3)*c.k
    //   ≡ π.k*area + area*c.k  [Cramer + partition]
    //   = area*(π.k+c.k) = area*p.k = p.k*area

    // Partition of unity: t1+t2+t3 ≡ area
    lemma_barycentric_partition_of_unity::<T>(p, a, b, c);
    let sum123 = t1.add(t2).add(t3);

    // Helper: a.k ≡ α.k + c.k from sub_then_add_cancel
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(a.x, c.x);
    T::axiom_eqv_symmetric(al.x.add(c.x), a.x);
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(a.y, c.y);
    T::axiom_eqv_symmetric(al.y.add(c.y), a.y);
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(b.x, c.x);
    T::axiom_eqv_symmetric(be.x.add(c.x), b.x);
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(b.y, c.y);
    T::axiom_eqv_symmetric(be.y.add(c.y), b.y);

    // ---- x-component integral identity ----

    // t1*a.x ≡ t1*(α.x+c.x) ≡ t1*α.x + t1*c.x
    ring_lemmas::lemma_mul_congruence_right::<T>(t1, a.x, al.x.add(c.x));
    T::axiom_mul_distributes_left(t1, al.x, c.x);
    T::axiom_eqv_transitive(t1.mul(a.x), t1.mul(al.x.add(c.x)), t1.mul(al.x).add(t1.mul(c.x)));

    // t2*b.x ≡ t2*β.x + t2*c.x
    ring_lemmas::lemma_mul_congruence_right::<T>(t2, b.x, be.x.add(c.x));
    T::axiom_mul_distributes_left(t2, be.x, c.x);
    T::axiom_eqv_transitive(t2.mul(b.x), t2.mul(be.x.add(c.x)), t2.mul(be.x).add(t2.mul(c.x)));

    // (t1*a.x + t2*b.x) ≡ (t1*α.x+t1*c.x) + (t2*β.x+t2*c.x)
    additive_group_lemmas::lemma_add_congruence::<T>(
        t1.mul(a.x), t1.mul(al.x).add(t1.mul(c.x)),
        t2.mul(b.x), t2.mul(be.x).add(t2.mul(c.x)),
    );

    // Rearrange (t1*α.x+t1*c.x)+(t2*β.x+t2*c.x) ≡ (t1*α.x+t2*β.x)+(t1*c.x+t2*c.x)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        t1.mul(al.x), t1.mul(c.x), t2.mul(be.x), t2.mul(c.x),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)),
        t1.mul(al.x).add(t1.mul(c.x)).add(t2.mul(be.x).add(t2.mul(c.x))),
        t1.mul(al.x).add(t2.mul(be.x)).add(t1.mul(c.x).add(t2.mul(c.x))),
    );

    // (t1*a.x+t2*b.x) + t3*c.x ≡ (t1*α.x+t2*β.x) + (t1*c.x+t2*c.x) + t3*c.x
    T::axiom_add_congruence_left(
        t1.mul(a.x).add(t2.mul(b.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(t1.mul(c.x).add(t2.mul(c.x))),
        t3.mul(c.x),
    );

    // Factor c.x terms: t1*c.x+t2*c.x ≡ (t1+t2)*c.x
    ring_lemmas::lemma_mul_distributes_right::<T>(t1, t2, c.x);
    T::axiom_eqv_symmetric(t1.add(t2).mul(c.x), t1.mul(c.x).add(t2.mul(c.x)));

    // (t1+t2)*c.x + t3*c.x ≡ (t1+t2+t3)*c.x
    ring_lemmas::lemma_mul_distributes_right::<T>(t1.add(t2), t3, c.x);
    T::axiom_eqv_symmetric(sum123.mul(c.x), t1.add(t2).mul(c.x).add(t3.mul(c.x)));

    // ((t1α.x+t2β.x) + (t1c.x+t2c.x)) + t3c.x
    // ≡ (t1α.x+t2β.x) + ((t1c.x+t2c.x) + t3c.x) [assoc]
    T::axiom_add_associative(
        t1.mul(al.x).add(t2.mul(be.x)), t1.mul(c.x).add(t2.mul(c.x)), t3.mul(c.x),
    );

    // Build chain: (t1c.x+t2c.x)+t3c.x ≡ (t1+t2)*c.x+t3c.x ≡ sum123*c.x
    T::axiom_add_congruence_left(
        t1.mul(c.x).add(t2.mul(c.x)), t1.add(t2).mul(c.x), t3.mul(c.x),
    );
    T::axiom_eqv_transitive(
        t1.mul(c.x).add(t2.mul(c.x)).add(t3.mul(c.x)),
        t1.add(t2).mul(c.x).add(t3.mul(c.x)),
        sum123.mul(c.x),
    );

    // Lift to: X + (t1c.x+t2c.x+t3c.x) ≡ X + sum123*c.x
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(al.x).add(t2.mul(be.x)),
        t1.mul(c.x).add(t2.mul(c.x)).add(t3.mul(c.x)),
        sum123.mul(c.x),
    );

    // Now chain: LHS+t3c.x ≡ ... + sum123*c.x → (t1α.x+t2β.x) + sum123*c.x
    T::axiom_eqv_transitive(
        t1.mul(al.x).add(t2.mul(be.x)).add(t1.mul(c.x).add(t2.mul(c.x))).add(t3.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(t1.mul(c.x).add(t2.mul(c.x)).add(t3.mul(c.x))),
        t1.mul(al.x).add(t2.mul(be.x)).add(sum123.mul(c.x)),
    );

    // Full chain for LHS ≡ (t1*α.x+t2*β.x) + sum123*c.x
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(t1.mul(c.x).add(t2.mul(c.x))).add(t3.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(sum123.mul(c.x)),
    );

    // Replace sum123 with area: sum123*c.x ≡ area*c.x
    T::axiom_mul_congruence_left(sum123, area, c.x);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(al.x).add(t2.mul(be.x)), sum123.mul(c.x), area.mul(c.x),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(sum123.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(area.mul(c.x)),
    );

    // Replace t1*α.x+t2*β.x with π.x*area (from Cramer)
    T::axiom_add_congruence_left(
        t1.mul(al.x).add(t2.mul(be.x)), pi.x.mul(area), area.mul(c.x),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)),
        t1.mul(al.x).add(t2.mul(be.x)).add(area.mul(c.x)),
        pi.x.mul(area).add(area.mul(c.x)),
    );

    // π.x*area + area*c.x ≡ area*π.x + area*c.x ≡ area*(π.x+c.x) ≡ area*p.x ≡ p.x*area
    T::axiom_mul_commutative(pi.x, area);
    T::axiom_add_congruence_left(pi.x.mul(area), area.mul(pi.x), area.mul(c.x));
    T::axiom_mul_distributes_left(area, pi.x, c.x);
    T::axiom_eqv_symmetric(area.mul(pi.x.add(c.x)), area.mul(pi.x).add(area.mul(c.x)));
    T::axiom_eqv_transitive(
        pi.x.mul(area).add(area.mul(c.x)),
        area.mul(pi.x).add(area.mul(c.x)),
        area.mul(pi.x.add(c.x)),
    );
    // π.x + c.x = sub2(p,c).x + c.x = p.x.sub(c.x).add(c.x) ≡ p.x
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(p.x, c.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(area, pi.x.add(c.x), p.x);
    T::axiom_eqv_transitive(
        pi.x.mul(area).add(area.mul(c.x)),
        area.mul(pi.x.add(c.x)),
        area.mul(p.x),
    );
    T::axiom_mul_commutative(area, p.x);
    T::axiom_eqv_transitive(
        pi.x.mul(area).add(area.mul(c.x)), area.mul(p.x), p.x.mul(area),
    );
    // Final x chain
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)),
        pi.x.mul(area).add(area.mul(c.x)),
        p.x.mul(area),
    );

    // ---- y-component integral identity (same structure) ----

    ring_lemmas::lemma_mul_congruence_right::<T>(t1, a.y, al.y.add(c.y));
    T::axiom_mul_distributes_left(t1, al.y, c.y);
    T::axiom_eqv_transitive(t1.mul(a.y), t1.mul(al.y.add(c.y)), t1.mul(al.y).add(t1.mul(c.y)));

    ring_lemmas::lemma_mul_congruence_right::<T>(t2, b.y, be.y.add(c.y));
    T::axiom_mul_distributes_left(t2, be.y, c.y);
    T::axiom_eqv_transitive(t2.mul(b.y), t2.mul(be.y.add(c.y)), t2.mul(be.y).add(t2.mul(c.y)));

    additive_group_lemmas::lemma_add_congruence::<T>(
        t1.mul(a.y), t1.mul(al.y).add(t1.mul(c.y)),
        t2.mul(b.y), t2.mul(be.y).add(t2.mul(c.y)),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        t1.mul(al.y), t1.mul(c.y), t2.mul(be.y), t2.mul(c.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)),
        t1.mul(al.y).add(t1.mul(c.y)).add(t2.mul(be.y).add(t2.mul(c.y))),
        t1.mul(al.y).add(t2.mul(be.y)).add(t1.mul(c.y).add(t2.mul(c.y))),
    );
    T::axiom_add_congruence_left(
        t1.mul(a.y).add(t2.mul(b.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(t1.mul(c.y).add(t2.mul(c.y))),
        t3.mul(c.y),
    );
    ring_lemmas::lemma_mul_distributes_right::<T>(t1, t2, c.y);
    T::axiom_eqv_symmetric(t1.add(t2).mul(c.y), t1.mul(c.y).add(t2.mul(c.y)));
    ring_lemmas::lemma_mul_distributes_right::<T>(t1.add(t2), t3, c.y);
    T::axiom_eqv_symmetric(sum123.mul(c.y), t1.add(t2).mul(c.y).add(t3.mul(c.y)));
    T::axiom_add_associative(
        t1.mul(al.y).add(t2.mul(be.y)), t1.mul(c.y).add(t2.mul(c.y)), t3.mul(c.y),
    );
    T::axiom_add_congruence_left(
        t1.mul(c.y).add(t2.mul(c.y)), t1.add(t2).mul(c.y), t3.mul(c.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(c.y).add(t2.mul(c.y)).add(t3.mul(c.y)),
        t1.add(t2).mul(c.y).add(t3.mul(c.y)),
        sum123.mul(c.y),
    );
    // Lift to: X + (t1c.y+t2c.y+t3c.y) ≡ X + sum123*c.y
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(al.y).add(t2.mul(be.y)),
        t1.mul(c.y).add(t2.mul(c.y)).add(t3.mul(c.y)),
        sum123.mul(c.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(al.y).add(t2.mul(be.y)).add(t1.mul(c.y).add(t2.mul(c.y))).add(t3.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(t1.mul(c.y).add(t2.mul(c.y)).add(t3.mul(c.y))),
        t1.mul(al.y).add(t2.mul(be.y)).add(sum123.mul(c.y)),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(t1.mul(c.y).add(t2.mul(c.y))).add(t3.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(sum123.mul(c.y)),
    );
    T::axiom_mul_congruence_left(sum123, area, c.y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(al.y).add(t2.mul(be.y)), sum123.mul(c.y), area.mul(c.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(sum123.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(area.mul(c.y)),
    );
    T::axiom_add_congruence_left(
        t1.mul(al.y).add(t2.mul(be.y)), pi.y.mul(area), area.mul(c.y),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)),
        t1.mul(al.y).add(t2.mul(be.y)).add(area.mul(c.y)),
        pi.y.mul(area).add(area.mul(c.y)),
    );
    T::axiom_mul_commutative(pi.y, area);
    T::axiom_add_congruence_left(pi.y.mul(area), area.mul(pi.y), area.mul(c.y));
    T::axiom_mul_distributes_left(area, pi.y, c.y);
    T::axiom_eqv_symmetric(area.mul(pi.y.add(c.y)), area.mul(pi.y).add(area.mul(c.y)));
    T::axiom_eqv_transitive(
        pi.y.mul(area).add(area.mul(c.y)),
        area.mul(pi.y).add(area.mul(c.y)),
        area.mul(pi.y.add(c.y)),
    );
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(p.y, c.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(area, pi.y.add(c.y), p.y);
    T::axiom_eqv_transitive(
        pi.y.mul(area).add(area.mul(c.y)), area.mul(pi.y.add(c.y)), area.mul(p.y),
    );
    T::axiom_mul_commutative(area, p.y);
    T::axiom_eqv_transitive(
        pi.y.mul(area).add(area.mul(c.y)), area.mul(p.y), p.y.mul(area),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)),
        pi.y.mul(area).add(area.mul(c.y)),
        p.y.mul(area),
    );
}

// =========================================================================
// Barycentric reconstruction
// =========================================================================

/// Barycentric reconstruction: p ≡ u*a + v*b + w*c
/// for normalized coordinates (u,v,w).
pub proof fn lemma_barycentric_reconstruction<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        !orient2d(a, b, c).eqv(T::zero()),
    ensures ({
        let (u, v, w) = barycentric_coords_2d(p, a, b, c);
        &&& p.x.eqv(u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x)))
        &&& p.y.eqv(u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)))
    }),
{
    let d = orient2d(a, b, c);
    let t1 = orient2d(b, c, p);
    let t2 = orient2d(c, a, p);
    let t3 = orient2d(a, b, p);
    let u = t1.div(d);
    let v = t2.div(d);
    let w = t3.div(d);

    // Integral identity: t1*a.k + t2*b.k + t3*c.k ≡ p.k*d
    lemma_barycentric_integral_identity::<T>(p, a, b, c);

    // --- x-component ---

    // Step 1: u*a.x ≡ t1*a.x/d, v*b.x ≡ t2*b.x/d, w*c.x ≡ t3*c.x/d
    lemma_div_mul_right::<T>(t1, d, a.x);
    lemma_div_mul_right::<T>(t2, d, b.x);
    lemma_div_mul_right::<T>(t3, d, c.x);

    // Step 2: Combine: u*a.x + v*b.x ≡ t1*a.x/d + t2*b.x/d
    additive_group_lemmas::lemma_add_congruence::<T>(
        u.mul(a.x), t1.mul(a.x).div(d),
        v.mul(b.x), t2.mul(b.x).div(d),
    );
    // (u*a.x+v*b.x) + w*c.x ≡ (t1*a.x/d+t2*b.x/d) + t3*c.x/d
    T::axiom_add_congruence_left(
        u.mul(a.x).add(v.mul(b.x)),
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)),
        w.mul(c.x),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)),
        w.mul(c.x),
        t3.mul(c.x).div(d),
    );
    T::axiom_eqv_transitive(
        u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x)),
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)).add(w.mul(c.x)),
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)).add(t3.mul(c.x).div(d)),
    );

    // Step 3: Combine fractions via div_distributes reversed
    field_lemmas::lemma_div_distributes_over_add::<T>(t1.mul(a.x), t2.mul(b.x), d);
    T::axiom_eqv_symmetric(
        t1.mul(a.x).add(t2.mul(b.x)).div(d),
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)),
    );
    T::axiom_add_congruence_left(
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)),
        t1.mul(a.x).add(t2.mul(b.x)).div(d),
        t3.mul(c.x).div(d),
    );
    field_lemmas::lemma_div_distributes_over_add::<T>(t1.mul(a.x).add(t2.mul(b.x)), t3.mul(c.x), d);
    T::axiom_eqv_symmetric(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
        t1.mul(a.x).add(t2.mul(b.x)).div(d).add(t3.mul(c.x).div(d)),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)).add(t3.mul(c.x).div(d)),
        t1.mul(a.x).add(t2.mul(b.x)).div(d).add(t3.mul(c.x).div(d)),
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
    );
    T::axiom_eqv_transitive(
        u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x)),
        t1.mul(a.x).div(d).add(t2.mul(b.x).div(d)).add(t3.mul(c.x).div(d)),
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
    );

    // Step 4: Integral identity + div congruence + mul_div_cancel
    // t1*a.x+t2*b.x+t3*c.x ≡ p.x*d, so (...)/d ≡ (p.x*d)/d ≡ p.x
    T::axiom_div_is_mul_recip(t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)), d);
    T::axiom_div_is_mul_recip(p.x.mul(d), d);
    T::axiom_mul_congruence_left(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)), p.x.mul(d), d.recip(),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).mul(d.recip()),
        p.x.mul(d).mul(d.recip()),
    );
    T::axiom_eqv_symmetric(p.x.mul(d).div(d), p.x.mul(d).mul(d.recip()));
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
        p.x.mul(d).mul(d.recip()),
        p.x.mul(d).div(d),
    );
    field_lemmas::lemma_mul_div_cancel::<T>(p.x, d);
    T::axiom_eqv_transitive(
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
        p.x.mul(d).div(d),
        p.x,
    );
    // LHS ≡ ... ≡ p.x
    T::axiom_eqv_transitive(
        u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x)),
        t1.mul(a.x).add(t2.mul(b.x)).add(t3.mul(c.x)).div(d),
        p.x,
    );
    T::axiom_eqv_symmetric(
        u.mul(a.x).add(v.mul(b.x)).add(w.mul(c.x)), p.x,
    );

    // --- y-component (same structure) ---

    lemma_div_mul_right::<T>(t1, d, a.y);
    lemma_div_mul_right::<T>(t2, d, b.y);
    lemma_div_mul_right::<T>(t3, d, c.y);

    additive_group_lemmas::lemma_add_congruence::<T>(
        u.mul(a.y), t1.mul(a.y).div(d),
        v.mul(b.y), t2.mul(b.y).div(d),
    );
    T::axiom_add_congruence_left(
        u.mul(a.y).add(v.mul(b.y)),
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)),
        w.mul(c.y),
    );
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)),
        w.mul(c.y),
        t3.mul(c.y).div(d),
    );
    T::axiom_eqv_transitive(
        u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)),
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)).add(w.mul(c.y)),
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)).add(t3.mul(c.y).div(d)),
    );

    field_lemmas::lemma_div_distributes_over_add::<T>(t1.mul(a.y), t2.mul(b.y), d);
    T::axiom_eqv_symmetric(
        t1.mul(a.y).add(t2.mul(b.y)).div(d),
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)),
    );
    T::axiom_add_congruence_left(
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)),
        t1.mul(a.y).add(t2.mul(b.y)).div(d),
        t3.mul(c.y).div(d),
    );
    field_lemmas::lemma_div_distributes_over_add::<T>(t1.mul(a.y).add(t2.mul(b.y)), t3.mul(c.y), d);
    T::axiom_eqv_symmetric(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
        t1.mul(a.y).add(t2.mul(b.y)).div(d).add(t3.mul(c.y).div(d)),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)).add(t3.mul(c.y).div(d)),
        t1.mul(a.y).add(t2.mul(b.y)).div(d).add(t3.mul(c.y).div(d)),
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
    );
    T::axiom_eqv_transitive(
        u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)),
        t1.mul(a.y).div(d).add(t2.mul(b.y).div(d)).add(t3.mul(c.y).div(d)),
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
    );

    T::axiom_div_is_mul_recip(t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)), d);
    T::axiom_div_is_mul_recip(p.y.mul(d), d);
    T::axiom_mul_congruence_left(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)), p.y.mul(d), d.recip(),
    );
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).mul(d.recip()),
        p.y.mul(d).mul(d.recip()),
    );
    T::axiom_eqv_symmetric(p.y.mul(d).div(d), p.y.mul(d).mul(d.recip()));
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
        p.y.mul(d).mul(d.recip()),
        p.y.mul(d).div(d),
    );
    field_lemmas::lemma_mul_div_cancel::<T>(p.y, d);
    T::axiom_eqv_transitive(
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
        p.y.mul(d).div(d),
        p.y,
    );
    T::axiom_eqv_transitive(
        u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)),
        t1.mul(a.y).add(t2.mul(b.y)).add(t3.mul(c.y)).div(d),
        p.y,
    );
    T::axiom_eqv_symmetric(
        u.mul(a.y).add(v.mul(b.y)).add(w.mul(c.y)), p.y,
    );
}

} // verus!
