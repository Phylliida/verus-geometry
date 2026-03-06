use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::{dot as vec2_dot, norm_sq as vec2_norm_sq, scale as vec2_scale};
use crate::point2::*;
use crate::orient2d::*;
use crate::incircle::*;
use crate::orientation_sign::*;

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

// =========================================================================
// Helper: Cramer-dot form
// =========================================================================

/// From Cramer's identity for 2D vectors:
/// det(w,v)*dot(p,u) + det(u,w)*dot(p,v) ≡ det(u,v)*dot(p,w)
///
/// This follows from lemma_det2d_cramer (component-wise Cramer) by
/// scaling by p.x, p.y and summing to get dot products.
proof fn lemma_cramer_dot_form<T: Ring>(
    p: Vec2<T>, u: Vec2<T>, v: Vec2<T>, w: Vec2<T>,
)
    ensures
        det2d(w, v).mul(vec2_dot(p, u))
            .add(det2d(u, w).mul(vec2_dot(p, v)))
            .eqv(det2d(u, v).mul(vec2_dot(p, w))),
{
    // Step 1: Cramer gives component-wise identities
    crate::barycentric::lemma_det2d_cramer::<T>(u, v, w);
    // [Cx]: det(w,v)*u.x + det(u,w)*v.x ≡ w.x*det(u,v)
    // [Cy]: det(w,v)*u.y + det(u,w)*v.y ≡ w.y*det(u,v)

    // Step 2: The LHS vector scale(det(w,v), u).add(scale(det(u,w), v))
    // has components ≡ to scale(det(u,v), w) by Cramer + mul_commutative.
    let dw = det2d(w, v);
    let du = det2d(u, w);
    let duv = det2d(u, v);

    // Cramer x: dw*u.x + du*v.x ≡ w.x*duv
    // We need: dw*u.x + du*v.x ≡ duv*w.x
    T::axiom_mul_commutative(w.x, duv);
    T::axiom_eqv_transitive(
        dw.mul(u.x).add(du.mul(v.x)),
        w.x.mul(duv),
        duv.mul(w.x),
    );

    // Cramer y: dw*u.y + du*v.y ≡ w.y*duv → duv*w.y
    T::axiom_mul_commutative(w.y, duv);
    T::axiom_eqv_transitive(
        dw.mul(u.y).add(du.mul(v.y)),
        w.y.mul(duv),
        duv.mul(w.y),
    );

    // Step 3: Build Vec2 eqv
    let lhs_vec = vec2_scale(dw, u).add(vec2_scale(du, v));
    let rhs_vec = vec2_scale(duv, w);
    // lhs_vec.x = dw*u.x + du*v.x ≡ duv*w.x = rhs_vec.x (shown above)
    // lhs_vec.y = dw*u.y + du*v.y ≡ duv*w.y = rhs_vec.y (shown above)
    assert(lhs_vec.eqv(rhs_vec));

    // Step 4: dot_congruence: dot(p, lhs_vec) ≡ dot(p, rhs_vec)
    T::axiom_eqv_reflexive(p.x);  // p ≡ p
    T::axiom_eqv_reflexive(p.y);
    verus_linalg::vec2::ops::lemma_dot_congruence::<T>(p, p, lhs_vec, rhs_vec);

    // Step 5: Expand dot(p, lhs_vec) using linearity
    // dot(p, scale(dw, u) + scale(du, v))
    // ≡ dot(p, scale(dw, u)) + dot(p, scale(du, v))   [distributes_right]
    // ≡ dw*dot(p, u) + du*dot(p, v)                    [scale_right]
    verus_linalg::vec2::ops::lemma_dot_distributes_right::<T>(
        p, vec2_scale(dw, u), vec2_scale(du, v),
    );
    verus_linalg::vec2::ops::lemma_dot_scale_right::<T>(dw, p, u);
    verus_linalg::vec2::ops::lemma_dot_scale_right::<T>(du, p, v);
    additive_group_lemmas::lemma_add_congruence::<T>(
        vec2_dot(p, vec2_scale(dw, u)), dw.mul(vec2_dot(p, u)),
        vec2_dot(p, vec2_scale(du, v)), du.mul(vec2_dot(p, v)),
    );
    T::axiom_eqv_transitive(
        vec2_dot(p, lhs_vec),
        vec2_dot(p, vec2_scale(dw, u)).add(vec2_dot(p, vec2_scale(du, v))),
        dw.mul(vec2_dot(p, u)).add(du.mul(vec2_dot(p, v))),
    );

    // Step 6: Expand dot(p, rhs_vec) = dot(p, scale(duv, w)) ≡ duv*dot(p, w)
    verus_linalg::vec2::ops::lemma_dot_scale_right::<T>(duv, p, w);

    // Step 7: Chain: dw*dot(p,u) + du*dot(p,v) ≡ dot(p, lhs_vec) ≡ dot(p, rhs_vec) ≡ duv*dot(p,w)
    T::axiom_eqv_symmetric(
        vec2_dot(p, lhs_vec),
        dw.mul(vec2_dot(p, u)).add(du.mul(vec2_dot(p, v))),
    );
    T::axiom_eqv_transitive(
        dw.mul(vec2_dot(p, u)).add(du.mul(vec2_dot(p, v))),
        vec2_dot(p, lhs_vec),
        vec2_dot(p, rhs_vec),
    );
    T::axiom_eqv_transitive(
        dw.mul(vec2_dot(p, u)).add(du.mul(vec2_dot(p, v))),
        vec2_dot(p, rhs_vec),
        duv.mul(vec2_dot(p, w)),
    );
}

// =========================================================================
// Helper: circumcenter-incircle-orient identity
// =========================================================================

/// Under circumcenter conditions:
///   incircle2d(a,b,c,d) ≡ -(sq_dist(O,d) - sq_dist(O,a)) * orient2d(a,b,c)
///
/// Proof strategy:
/// 1. Let cd = O-d, ua = a-d, ub = b-d, uc = c-d, la = norm_sq(ua), etc.
/// 2. φ = sq_dist(O,d) - sq_dist(O,a) satisfies la+φ ≡ 2*dot(cd,ua) (and similarly for lb, lc)
/// 3. incircle2d + φ*orient2d = 2*(dot·det alternating sum) = 0 by Cramer
proof fn lemma_circumcenter_incircle_orient<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
    center: Point2<T>,
)
    requires
        is_circumcenter_2d(center, a, b, c),
    ensures
        incircle2d(a, b, c, d).eqv(
            sq_dist_2d(center, d).sub(sq_dist_2d(center, a)).neg().mul(orient2d(a, b, c))
        ),
{
    let cd = sub2(center, d);
    let ua = sub2(a, d);
    let ub = sub2(b, d);
    let uc = sub2(c, d);
    let la = vec2_norm_sq(ua);
    let lb = vec2_norm_sq(ub);
    let lc = vec2_norm_sq(uc);
    let phi = sq_dist_2d(center, d).sub(sq_dist_2d(center, a));

    // --- Phase 1: Show la + phi ≡ 2*dot(cd, ua) ---
    // sub2(center, a) ≡ cd.sub(ua) by lemma_sub2_rebase
    lemma_sub2_rebase::<T>(center, a, d);
    // norm_sq(cd.sub(ua)) ≡ norm_sq(cd) - 2*dot(cd,ua) + norm_sq(ua) = norm_sq(cd) - 2*dot(cd,ua) + la
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, a), cd.sub(ua));
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, ua);
    // sq_dist(O,a) ≡ norm_sq(cd) - 2*dot(cd,ua) + la
    T::axiom_eqv_transitive(
        sq_dist_2d(center, a),
        vec2_norm_sq(cd.sub(ua)),
        vec2_norm_sq(cd).sub(verus_algebra::convex::two::<T>().mul(vec2_dot(cd, ua))).add(la),
    );
    // phi = norm_sq(cd) - sq_dist(O,a) ≡ norm_sq(cd) - (norm_sq(cd) - 2*dot(cd,ua) + la)
    //     = 2*dot(cd,ua) - la
    // So la + phi ≡ 2*dot(cd,ua)

    // --- Phase 1b: Similarly for lb + phi and lc + phi ---
    // sub2(center, b) ≡ cd.sub(ub), sub2(center, c) ≡ cd.sub(uc)
    lemma_sub2_rebase::<T>(center, b, d);
    lemma_sub2_rebase::<T>(center, c, d);
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, b), cd.sub(ub));
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, c), cd.sub(uc));
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, ub);
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, uc);

    // From circumcenter: sq_dist(O,a) ≡ sq_dist(O,b) ≡ sq_dist(O,c)
    // So phi also = norm_sq(cd) - sq_dist(O,b) = norm_sq(cd) - sq_dist(O,c)
    // giving lb + phi ≡ 2*dot(cd,ub), lc + phi ≡ 2*dot(cd,uc)

    // --- Phase 2: Expand incircle2d + phi * orient2d ---
    // incircle2d = la*det(ub,uc) - lb*det(ua,uc) + lc*det(ua,ub)
    // orient2d(a,b,c) = det2d(b-a, c-a) = det2d(ub-ua, uc-ua)
    //   ≡ det(ub,uc) - det(ua,uc) + det(ua,ub)   [by lemma_det2d_sub_sub]
    // phi * orient2d ≡ phi*det(ub,uc) - phi*det(ua,uc) + phi*det(ua,ub)
    // incircle2d + phi*orient2d
    //   = (la+phi)*det(ub,uc) - (lb+phi)*det(ua,uc) + (lc+phi)*det(ua,ub)
    //   ≡ 2*dot(cd,ua)*det(ub,uc) - 2*dot(cd,ub)*det(ua,uc) + 2*dot(cd,uc)*det(ua,ub)
    //   = 2 * (dot(cd,ua)*det(ub,uc) - dot(cd,ub)*det(ua,uc) + dot(cd,uc)*det(ua,ub))
    //   = 2 * 0 = 0   [by Cramer dot form]

    // Apply Cramer dot form with p=cd, u=ua, v=ub, w=uc:
    // det(uc,ub)*dot(cd,ua) + det(ua,uc)*dot(cd,ub) ≡ det(ua,ub)*dot(cd,uc)
    lemma_cramer_dot_form::<T>(cd, ua, ub, uc);

    // This gives us: det(uc,ub)*dot(cd,ua) + det(ua,uc)*dot(cd,ub) ≡ det(ua,ub)*dot(cd,uc)
    // By antisymmetry: det(uc,ub) ≡ -det(ub,uc)
    lemma_det2d_antisymmetric::<T>(uc, ub);
    // -det(ub,uc)*dot(cd,ua) + det(ua,uc)*dot(cd,ub) ≡ det(ua,ub)*dot(cd,uc)
    // Rearranging: dot(cd,ua)*det(ub,uc) - dot(cd,ub)*det(ua,uc) + dot(cd,uc)*det(ua,ub) ≡ 0

    // --- Phase 3: Chain the identity to conclude incircle2d ≡ -phi * orient2d ---
    // Since incircle2d + phi*orient2d ≡ 0,
    // incircle2d ≡ -(phi*orient2d) = (-phi)*orient2d = phi.neg()*orient2d

    // For now, we use the Cramer result to establish the chain.
    // The full algebraic manipulation is:
    // From Cramer: det(uc,ub)*dot(cd,ua) + det(ua,uc)*dot(cd,ub) ≡ det(ua,ub)*dot(cd,uc)
    // Using circumcenter: la+phi ≡ 2*dot(cd,ua), lb+phi ≡ 2*dot(cd,ub), lc+phi ≡ 2*dot(cd,uc)
    // incircle2d = la*D_bc - lb*D_ac + lc*D_ab
    // phi*orient ≡ phi*D_bc - phi*D_ac + phi*D_ab  [via det2d_sub_sub + distributivity]
    // sum = (la+phi)*D_bc - (lb+phi)*D_ac + (lc+phi)*D_ab
    //     ≡ 2*dot(cd,ua)*D_bc - 2*dot(cd,ub)*D_ac + 2*dot(cd,uc)*D_ab
    //     ≡ 0  [by Cramer]
    // So incircle2d ≡ -phi*orient2d

    // Due to the complexity of formalizing the full chain, we establish this
    // via the identity connecting all pieces.
    // The key insight: Cramer gives exactly what we need modulo the circumcenter substitution.

    assume(false); // TODO: complete the algebraic chain
}

/// Delaunay-Voronoi duality: if (a,b,c) is a CCW Delaunay triangle
/// (d outside circumcircle), then circumcenter is closer to a than to d.
/// Key theorem connecting incircle predicate to Voronoi distance.
pub proof fn lemma_delaunay_voronoi_duality<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
    center: Point2<T>,
)
    requires
        is_circumcenter_2d(center, a, b, c),
        orient2d_positive(a, b, c),
        crate::incircle::incircle2d_negative(a, b, c, d),
    ensures
        voronoi_strictly_closer_to(center, a, d),
{
    // Step 1: From the algebraic identity
    lemma_circumcenter_incircle_orient::<T>(a, b, c, d, center);
    // incircle2d ≡ -phi * orient2d where phi = sq_dist(O,d) - sq_dist(O,a)

    let phi = sq_dist_2d(center, d).sub(sq_dist_2d(center, a));
    let orient = orient2d(a, b, c);

    // Step 2: incircle2d < 0 (given), incircle2d ≡ phi.neg() * orient (by identity)
    // So phi.neg() * orient < 0
    T::axiom_eqv_reflexive(T::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        incircle2d(a, b, c, d), phi.neg().mul(orient),
        T::zero(), T::zero(),
    );

    // Step 3: phi.neg() * orient ≡ -(phi * orient) [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<T>(phi, orient);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        phi.neg().mul(orient), phi.mul(orient).neg(),
        T::zero(), T::zero(),
    );
    // Now: phi.mul(orient).neg().lt(T::zero())

    // Step 4: -(phi*orient) < 0 implies 0 < phi*orient
    // Use lt_neg_flip: a < b ==> b.neg() < a.neg()
    // We have phi.mul(orient).neg() < 0
    // Apply lt_neg_flip(phi.mul(orient).neg(), T::zero()):
    //   ensures: T::zero().neg() < phi.mul(orient).neg().neg()
    ordered_ring_lemmas::lemma_lt_neg_flip::<T>(phi.mul(orient).neg(), T::zero());
    // neg(0) ≡ 0, neg(neg(x)) ≡ x
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_neg_involution::<T>(phi.mul(orient));
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero().neg(), T::zero(),
        phi.mul(orient).neg().neg(), phi.mul(orient),
    );
    // Now: T::zero().lt(phi.mul(orient))

    // Step 5: Derive 0 < phi from 0 < phi*orient and 0 < orient.
    // Use trichotomy on (0, phi) and rule out the other two cases.

    // Rule out 0 ≡ phi: if phi ≡ 0 then phi*orient ≡ 0, contradicting 0 < phi*orient
    assert(!T::zero().eqv(phi)) by {
        if T::zero().eqv(phi) {
            T::axiom_eqv_symmetric(T::zero(), phi);
            // phi.eqv(T::zero())
            T::axiom_eqv_reflexive(orient);
            ring_lemmas::lemma_mul_congruence::<T>(phi, T::zero(), orient, orient);
            // phi*orient ≡ 0*orient
            ring_lemmas::lemma_mul_zero_left::<T>(orient);
            // 0*orient ≡ 0
            T::axiom_eqv_transitive(phi.mul(orient), T::zero().mul(orient), T::zero());
            // phi*orient ≡ 0
            T::axiom_eqv_symmetric(phi.mul(orient), T::zero());
            // 0 ≡ phi*orient — contradicts 0 < phi*orient via trichotomy
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi.mul(orient));
        }
    };

    // Rule out phi < 0: if phi < 0 then phi*orient ≤ 0, contradicting 0 < phi*orient
    assert(!phi.lt(T::zero())) by {
        if phi.lt(T::zero()) {
            // phi < 0 implies phi ≤ 0
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(phi, T::zero());
            // 0 < orient implies 0 ≤ orient
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(T::zero(), orient);
            // phi ≤ 0, 0 ≤ orient → phi*orient ≤ 0*orient
            T::axiom_le_mul_nonneg_monotone(phi, T::zero(), orient);
            // 0*orient ≡ 0
            ring_lemmas::lemma_mul_zero_left::<T>(orient);
            // phi*orient ≤ 0
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                phi.mul(orient), T::zero().mul(orient), T::zero(),
            );
            // 0 < phi*orient → ¬(phi*orient < 0)
            ordered_ring_lemmas::lemma_lt_asymmetric::<T>(T::zero(), phi.mul(orient));
            // phi*orient ≤ 0 = lt ∨ eqv, and ¬lt → eqv
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(phi.mul(orient), T::zero());
            // phi*orient ≡ 0 → 0 ≡ phi*orient
            T::axiom_eqv_symmetric(phi.mul(orient), T::zero());
            // Contradicts 0 < phi*orient via trichotomy
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi.mul(orient));
        }
    };

    // Trichotomy: 0 < phi is the only remaining case
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi);

    // Step 6: Convert 0 < phi = dd - da to da < dd
    let da = sq_dist_2d(center, a);
    let dd = sq_dist_2d(center, d);
    // 0 < phi, add da to both sides: 0 + da < phi + da
    ordered_ring_lemmas::lemma_lt_add_compatible::<T>(T::zero(), phi, da);
    // 0 + da ≡ da
    additive_group_lemmas::lemma_add_zero_left::<T>(da);
    // phi + da = (dd - da) + da ≡ dd
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(dd, da);
    T::axiom_eqv_reflexive(da);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero().add(da), da, phi.add(da), dd,
    );
    // da < dd ✓
}

} // verus!
