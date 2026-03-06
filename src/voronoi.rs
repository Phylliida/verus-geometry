use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::norm_sq as vec2_norm_sq;
use crate::point2::*;

verus! {

// =========================================================================
// Spec functions
// =========================================================================

/// Squared distance between two 2D points: ||p - q||².
pub open spec fn sq_dist_2d<T: Ring>(p: Point2<T>, q: Point2<T>) -> T {
    vec2_norm_sq(sub2(p, q))
}

/// A point `center` is the circumcenter of triangle (a, b, c) if it is
/// equidistant from all three vertices.
pub open spec fn is_circumcenter_2d<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    &&& sq_dist_2d(center, a).eqv(sq_dist_2d(center, b))
    &&& sq_dist_2d(center, b).eqv(sq_dist_2d(center, c))
}

/// Point p is at least as close to a as to b (Voronoi half-plane test).
pub open spec fn voronoi_closer_to<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    sq_dist_2d(p, a).le(sq_dist_2d(p, b))
}

/// Point p is strictly closer to a than to b.
pub open spec fn voronoi_strictly_closer_to<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    sq_dist_2d(p, a).lt(sq_dist_2d(p, b))
}

/// Point p is in the Voronoi cell of site i: closer to sites[i] than to all other sites.
pub open spec fn in_voronoi_cell<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int, p: Point2<T>,
) -> bool {
    &&& 0 <= i < sites.len()
    &&& forall|j: int| 0 <= j < sites.len() ==>
            voronoi_closer_to(p, sites[i], #[trigger] sites[j])
}

/// Point p is strictly in the Voronoi cell of site i.
pub open spec fn in_voronoi_cell_strict<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int, p: Point2<T>,
) -> bool {
    &&& 0 <= i < sites.len()
    &&& forall|j: int| 0 <= j < sites.len() && j != i ==>
            voronoi_strictly_closer_to(p, sites[i], #[trigger] sites[j])
}

// =========================================================================
// Proof lemmas
// =========================================================================

/// If p is at least as close to a as to b, AND at least as close to b as to a,
/// then p is equidistant from a and b.
pub proof fn lemma_voronoi_closer_symmetric<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    requires
        voronoi_closer_to(p, a, b),
        voronoi_closer_to(p, b, a),
    ensures
        sq_dist_2d(p, a).eqv(sq_dist_2d(p, b)),
{
    // closer(p,a,b) means sq_dist(p,a) ≤ sq_dist(p,b)
    // closer(p,b,a) means sq_dist(p,b) ≤ sq_dist(p,a)
    // By trichotomy + le_iff: a ≤ b ∧ b ≤ a → a ≡ b
    let da = sq_dist_2d(p, a);
    let db = sq_dist_2d(p, b);
    ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(da, db);
    ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(db, da);
    // da ≤ db means da < db ∨ da ≡ db
    // db ≤ da means db < da ∨ db ≡ da
    // If da < db and db < da: contradiction by lt_asymmetric
    if da.lt(db) && db.lt(da) {
        ordered_ring_lemmas::lemma_lt_asymmetric::<T>(da, db);
    }
    // So at least one of da ≡ db or db ≡ da holds
    if db.eqv(da) {
        T::axiom_eqv_symmetric(db, da);
    }
}

/// Circumcenter is equidistant from all three vertices (trivial by definition).
pub proof fn lemma_circumcenter_equidistant<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        is_circumcenter_2d(center, a, b, c),
    ensures
        sq_dist_2d(center, a).eqv(sq_dist_2d(center, b)),
        sq_dist_2d(center, b).eqv(sq_dist_2d(center, c)),
{
    // Direct from definition.
}

/// Each site is in its own Voronoi cell (zero distance to itself is minimal).
pub proof fn lemma_voronoi_cell_nonempty<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int,
)
    requires
        0 <= i < sites.len(),
    ensures
        in_voronoi_cell(sites, i, sites[i]),
{
    // sq_dist(sites[i], sites[i]) = norm_sq(sub2(sites[i], sites[i]))
    // sub2(p, p) = (0, 0), norm_sq((0,0)) = 0
    // For any j: sq_dist(sites[i], sites[j]) = norm_sq(sub2(sites[i], sites[j]))
    // norm_sq is always ≥ 0 (sum of squares), so 0 ≤ sq_dist(sites[i], sites[j])

    let p = sites[i];
    let zero_vec = sub2(p, p);

    // p.x - p.x ≡ 0, p.y - p.y ≡ 0
    T::axiom_sub_is_add_neg(p.x, p.x);
    T::axiom_add_inverse_right(p.x);
    T::axiom_eqv_transitive(p.x.sub(p.x), p.x.add(p.x.neg()), T::zero());

    T::axiom_sub_is_add_neg(p.y, p.y);
    T::axiom_add_inverse_right(p.y);
    T::axiom_eqv_transitive(p.y.sub(p.y), p.y.add(p.y.neg()), T::zero());

    // zero_vec.x ≡ 0, zero_vec.y ≡ 0
    // zero_vec.x * zero_vec.x ≡ 0 * 0 ≡ 0
    verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence::<T>(
        zero_vec.x, T::zero(), zero_vec.x, T::zero(),
    );
    verus_algebra::lemmas::ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        zero_vec.x.mul(zero_vec.x), T::zero().mul(T::zero()), T::zero(),
    );

    verus_algebra::lemmas::ring_lemmas::lemma_mul_congruence::<T>(
        zero_vec.y, T::zero(), zero_vec.y, T::zero(),
    );
    T::axiom_eqv_transitive(
        zero_vec.y.mul(zero_vec.y), T::zero().mul(T::zero()), T::zero(),
    );

    // 0 + 0 ≡ 0
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    // norm_sq(zero_vec) = x² + y² ≡ 0 + 0 ≡ 0
    T::axiom_add_congruence_left(
        zero_vec.x.mul(zero_vec.x), T::zero(),
        zero_vec.y.mul(zero_vec.y),
    );
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::zero(), zero_vec.y.mul(zero_vec.y), T::zero(),
    );
    T::axiom_eqv_transitive(
        vec2_norm_sq(zero_vec),
        T::zero().add(zero_vec.y.mul(zero_vec.y)),
        T::zero().add(T::zero()),
    );
    T::axiom_eqv_transitive(
        vec2_norm_sq(zero_vec),
        T::zero().add(T::zero()),
        T::zero(),
    );

    // sq_dist(p, p) ≡ 0
    // For all j: 0 ≤ sq_dist(p, sites[j]) since norm_sq = sum of squares ≥ 0
    assert forall|j: int| 0 <= j < sites.len() implies
        voronoi_closer_to(p, p, #[trigger] sites[j])
    by {
        let q = sites[j];
        let v = sub2(p, q);
        // v.x² ≥ 0 and v.y² ≥ 0
        ordered_ring_lemmas::lemma_square_nonneg::<T>(v.x);
        ordered_ring_lemmas::lemma_square_nonneg::<T>(v.y);
        // 0 + 0 ≤ v.x² + v.y²
        ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), v.x.mul(v.x), T::zero(), v.y.mul(v.y),
        );
        // 0 ≡ 0 + 0, so 0 ≤ norm_sq(v)
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().add(T::zero()), T::zero(), vec2_norm_sq(v),
        );
        // sq_dist(p,p) ≡ 0 ≤ sq_dist(p,q), so sq_dist(p,p) ≤ sq_dist(p,q)
        T::axiom_eqv_symmetric(vec2_norm_sq(zero_vec), T::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero(), sq_dist_2d(p, p), sq_dist_2d(p, q),
        );
    }
}

/// Delaunay-Voronoi duality: if (a,b,c) is Delaunay (d outside circumcircle),
/// then circumcenter is closer to each vertex than to d.
/// Key theorem connecting incircle predicate to Voronoi distance.
#[verifier::external_body]
pub proof fn lemma_delaunay_voronoi_duality<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
    center: Point2<T>,
)
    requires
        is_circumcenter_2d(center, a, b, c),
        crate::incircle::incircle2d_negative(a, b, c, d),
    ensures
        voronoi_strictly_closer_to(center, a, d),
{
    // assume(false) — requires algebraic identity connecting incircle2d determinant
    // to squared-distance comparison (~300 lines, deferred)
}

} // verus!
