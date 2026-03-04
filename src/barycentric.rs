use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
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

} // verus!
