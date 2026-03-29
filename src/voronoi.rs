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

//  =========================================================================
//  Spec functions
//  =========================================================================

///  Squared distance between two 2D points: ||p - q||².
pub open spec fn sq_dist_2d<T: Ring>(p: Point2<T>, q: Point2<T>) -> T {
    vec2_norm_sq(sub2(p, q))
}

///  A point `center` is the circumcenter of triangle (a, b, c) if it is
///  equidistant from all three vertices.
pub open spec fn is_circumcenter_2d<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    &&& sq_dist_2d(center, a).eqv(sq_dist_2d(center, b))
    &&& sq_dist_2d(center, b).eqv(sq_dist_2d(center, c))
}

///  Point p is at least as close to a as to b (Voronoi half-plane test).
pub open spec fn voronoi_closer_to<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    sq_dist_2d(p, a).le(sq_dist_2d(p, b))
}

///  Point p is strictly closer to a than to b.
pub open spec fn voronoi_strictly_closer_to<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    sq_dist_2d(p, a).lt(sq_dist_2d(p, b))
}

///  Point p is in the Voronoi cell of site i: closer to sites[i] than to all other sites.
pub open spec fn in_voronoi_cell<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int, p: Point2<T>,
) -> bool {
    &&& 0 <= i < sites.len()
    &&& forall|j: int| 0 <= j < sites.len() ==>
            voronoi_closer_to(p, sites[i], #[trigger] sites[j])
}

///  Point p is strictly in the Voronoi cell of site i.
pub open spec fn in_voronoi_cell_strict<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int, p: Point2<T>,
) -> bool {
    &&& 0 <= i < sites.len()
    &&& forall|j: int| 0 <= j < sites.len() && j != i ==>
            voronoi_strictly_closer_to(p, sites[i], #[trigger] sites[j])
}

//  =========================================================================
//  Proof lemmas
//  =========================================================================

///  If p is at least as close to a as to b, AND at least as close to b as to a,
///  then p is equidistant from a and b.
pub proof fn lemma_voronoi_closer_symmetric<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    requires
        voronoi_closer_to(p, a, b),
        voronoi_closer_to(p, b, a),
    ensures
        sq_dist_2d(p, a).eqv(sq_dist_2d(p, b)),
{
    //  closer(p,a,b) means sq_dist(p,a) ≤ sq_dist(p,b)
    //  closer(p,b,a) means sq_dist(p,b) ≤ sq_dist(p,a)
    //  By trichotomy + le_iff: a ≤ b ∧ b ≤ a → a ≡ b
    let da = sq_dist_2d(p, a);
    let db = sq_dist_2d(p, b);
    ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(da, db);
    ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(db, da);
    //  da ≤ db means da < db ∨ da ≡ db
    //  db ≤ da means db < da ∨ db ≡ da
    //  If da < db and db < da: contradiction by lt_asymmetric
    if da.lt(db) && db.lt(da) {
        ordered_ring_lemmas::lemma_lt_asymmetric::<T>(da, db);
    }
    //  So at least one of da ≡ db or db ≡ da holds
    if db.eqv(da) {
        T::axiom_eqv_symmetric(db, da);
    }
}

///  Circumcenter is equidistant from all three vertices (trivial by definition).
pub proof fn lemma_circumcenter_equidistant<T: OrderedRing>(
    center: Point2<T>, a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        is_circumcenter_2d(center, a, b, c),
    ensures
        sq_dist_2d(center, a).eqv(sq_dist_2d(center, b)),
        sq_dist_2d(center, b).eqv(sq_dist_2d(center, c)),
{
    //  Direct from definition.
}

///  Each site is in its own Voronoi cell (zero distance to itself is minimal).
pub proof fn lemma_voronoi_cell_nonempty<T: OrderedRing>(
    sites: Seq<Point2<T>>, i: int,
)
    requires
        0 <= i < sites.len(),
    ensures
        in_voronoi_cell(sites, i, sites[i]),
{
    //  sq_dist(sites[i], sites[i]) = norm_sq(sub2(sites[i], sites[i]))
    //  sub2(p, p) = (0, 0), norm_sq((0,0)) = 0
    //  For any j: sq_dist(sites[i], sites[j]) = norm_sq(sub2(sites[i], sites[j]))
    //  norm_sq is always ≥ 0 (sum of squares), so 0 ≤ sq_dist(sites[i], sites[j])

    let p = sites[i];
    let zero_vec = sub2(p, p);

    //  p.x - p.x ≡ 0, p.y - p.y ≡ 0
    T::axiom_sub_is_add_neg(p.x, p.x);
    T::axiom_add_inverse_right(p.x);
    T::axiom_eqv_transitive(p.x.sub(p.x), p.x.add(p.x.neg()), T::zero());

    T::axiom_sub_is_add_neg(p.y, p.y);
    T::axiom_add_inverse_right(p.y);
    T::axiom_eqv_transitive(p.y.sub(p.y), p.y.add(p.y.neg()), T::zero());

    //  zero_vec.x ≡ 0, zero_vec.y ≡ 0
    //  zero_vec.x * zero_vec.x ≡ 0 * 0 ≡ 0
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

    //  0 + 0 ≡ 0
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    //  norm_sq(zero_vec) = x² + y² ≡ 0 + 0 ≡ 0
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

    //  sq_dist(p, p) ≡ 0
    //  For all j: 0 ≤ sq_dist(p, sites[j]) since norm_sq = sum of squares ≥ 0
    assert forall|j: int| 0 <= j < sites.len() implies
        voronoi_closer_to(p, p, #[trigger] sites[j])
    by {
        let q = sites[j];
        let v = sub2(p, q);
        //  v.x² ≥ 0 and v.y² ≥ 0
        ordered_ring_lemmas::lemma_square_nonneg::<T>(v.x);
        ordered_ring_lemmas::lemma_square_nonneg::<T>(v.y);
        //  0 + 0 ≤ v.x² + v.y²
        ordered_ring_lemmas::lemma_le_add_both::<T>(
            T::zero(), v.x.mul(v.x), T::zero(), v.y.mul(v.y),
        );
        //  0 ≡ 0 + 0, so 0 ≤ norm_sq(v)
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero().add(T::zero()), T::zero(), vec2_norm_sq(v),
        );
        //  sq_dist(p,p) ≡ 0 ≤ sq_dist(p,q), so sq_dist(p,p) ≤ sq_dist(p,q)
        T::axiom_eqv_symmetric(vec2_norm_sq(zero_vec), T::zero());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(
            T::zero(), sq_dist_2d(p, p), sq_dist_2d(p, q),
        );
    }
}

//  =========================================================================
//  Helper: Cramer-dot form
//  =========================================================================

///  From Cramer's identity for 2D vectors:
///  det(w,v)*dot(p,u) + det(u,w)*dot(p,v) ≡ det(u,v)*dot(p,w)
///
///  This follows from lemma_det2d_cramer (component-wise Cramer) by
///  scaling by p.x, p.y and summing to get dot products.
proof fn lemma_cramer_dot_form<T: Ring>(
    p: Vec2<T>, u: Vec2<T>, v: Vec2<T>, w: Vec2<T>,
)
    ensures
        det2d(w, v).mul(vec2_dot(p, u))
            .add(det2d(u, w).mul(vec2_dot(p, v)))
            .eqv(det2d(u, v).mul(vec2_dot(p, w))),
{
    //  Step 1: Cramer gives component-wise identities
    crate::barycentric::lemma_det2d_cramer::<T>(u, v, w);
    //  [Cx]: det(w,v)*u.x + det(u,w)*v.x ≡ w.x*det(u,v)
    //  [Cy]: det(w,v)*u.y + det(u,w)*v.y ≡ w.y*det(u,v)

    //  Step 2: The LHS vector scale(det(w,v), u).add(scale(det(u,w), v))
    //  has components ≡ to scale(det(u,v), w) by Cramer + mul_commutative.
    let dw = det2d(w, v);
    let du = det2d(u, w);
    let duv = det2d(u, v);

    //  Cramer x: dw*u.x + du*v.x ≡ w.x*duv
    //  We need: dw*u.x + du*v.x ≡ duv*w.x
    T::axiom_mul_commutative(w.x, duv);
    T::axiom_eqv_transitive(
        dw.mul(u.x).add(du.mul(v.x)),
        w.x.mul(duv),
        duv.mul(w.x),
    );

    //  Cramer y: dw*u.y + du*v.y ≡ w.y*duv → duv*w.y
    T::axiom_mul_commutative(w.y, duv);
    T::axiom_eqv_transitive(
        dw.mul(u.y).add(du.mul(v.y)),
        w.y.mul(duv),
        duv.mul(w.y),
    );

    //  Step 3: Build Vec2 eqv
    let lhs_vec = vec2_scale(dw, u).add(vec2_scale(du, v));
    let rhs_vec = vec2_scale(duv, w);
    //  lhs_vec.x = dw*u.x + du*v.x ≡ duv*w.x = rhs_vec.x (shown above)
    //  lhs_vec.y = dw*u.y + du*v.y ≡ duv*w.y = rhs_vec.y (shown above)
    assert(lhs_vec.eqv(rhs_vec));

    //  Step 4: dot_congruence: dot(p, lhs_vec) ≡ dot(p, rhs_vec)
    T::axiom_eqv_reflexive(p.x);  //  p ≡ p
    T::axiom_eqv_reflexive(p.y);
    verus_linalg::vec2::ops::lemma_dot_congruence::<T>(p, p, lhs_vec, rhs_vec);

    //  Step 5: Expand dot(p, lhs_vec) using linearity
    //  dot(p, scale(dw, u) + scale(du, v))
    //  ≡ dot(p, scale(dw, u)) + dot(p, scale(du, v))   [distributes_right]
    //  ≡ dw*dot(p, u) + du*dot(p, v)                    [scale_right]
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

    //  Step 6: Expand dot(p, rhs_vec) = dot(p, scale(duv, w)) ≡ duv*dot(p, w)
    verus_linalg::vec2::ops::lemma_dot_scale_right::<T>(duv, p, w);

    //  Step 7: Chain: dw*dot(p,u) + du*dot(p,v) ≡ dot(p, lhs_vec) ≡ dot(p, rhs_vec) ≡ duv*dot(p,w)
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

//  =========================================================================
//  Helper: phi + lift ≡ tw (circumcenter distance identity)
//  =========================================================================

///  Given sq_dist(O,v) ≡ ncd - tw + l and phi ≡ ncd - sq_dist(O,v),
///  proves phi + l ≡ tw.
///
///  This is the key algebraic step: from the norm_sq_sub_expand identity
///  for each vertex v, the circumcenter "phi" shift satisfies phi + lift(v) ≡ 2*dot(cd,v).
proof fn lemma_phi_plus_lift_vertex<T: Ring>(
    ncd: T, tw: T, l: T, sq_dist_v: T, phi: T,
)
    requires
        sq_dist_v.eqv(ncd.sub(tw).add(l)),
        phi.eqv(ncd.sub(sq_dist_v)),
    ensures
        phi.add(l).eqv(tw),
{
    let k = ncd.sub(tw);

    //  (A) phi + sq_dist_v ≡ ncd
    T::axiom_eqv_reflexive(sq_dist_v);
    additive_group_lemmas::lemma_add_congruence::<T>(
        phi, ncd.sub(sq_dist_v), sq_dist_v, sq_dist_v,
    );
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(ncd, sq_dist_v);
    T::axiom_eqv_transitive(
        phi.add(sq_dist_v), ncd.sub(sq_dist_v).add(sq_dist_v), ncd,
    );

    //  (B) phi + (k + l) ≡ ncd  [since sq_dist_v ≡ k + l]
    additive_group_lemmas::lemma_add_congruence_right::<T>(phi, sq_dist_v, k.add(l));
    T::axiom_eqv_symmetric(phi.add(sq_dist_v), phi.add(k.add(l)));
    T::axiom_eqv_transitive(phi.add(k.add(l)), phi.add(sq_dist_v), ncd);

    //  (C) k + tw ≡ ncd
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(ncd, tw);

    //  (D) phi + (k+l) ≡ k + (phi+l)  [rearrange via commutativity + associativity]
    T::axiom_add_commutative(phi, k.add(l));
    T::axiom_add_associative(k, l, phi);
    T::axiom_add_commutative(l, phi);
    additive_group_lemmas::lemma_add_congruence_right::<T>(k, l.add(phi), phi.add(l));
    T::axiom_eqv_transitive(
        phi.add(k.add(l)), k.add(l).add(phi), k.add(l.add(phi)),
    );
    T::axiom_eqv_transitive(
        phi.add(k.add(l)), k.add(l.add(phi)), k.add(phi.add(l)),
    );

    //  (E) k + (phi+l) ≡ ncd  [combine (B) and (D)]
    T::axiom_eqv_symmetric(phi.add(k.add(l)), k.add(phi.add(l)));
    T::axiom_eqv_transitive(k.add(phi.add(l)), phi.add(k.add(l)), ncd);

    //  (F) k + (phi+l) ≡ k + tw  [combine (E) and (C)]
    T::axiom_eqv_symmetric(k.add(tw), ncd);
    T::axiom_eqv_transitive(k.add(phi.add(l)), ncd, k.add(tw));

    //  Conclude by left cancellation
    additive_group_lemmas::lemma_add_left_cancel::<T>(phi.add(l), tw, k);
}

//  =========================================================================
//  Helper: Cramer alternating dot·det sum is zero
//  =========================================================================

///  From Cramer's dot form, the alternating sum of dot·det products vanishes:
///    dot(cd,ua)*det(ub,uc) - dot(cd,ub)*det(ua,uc) + dot(cd,uc)*det(ua,ub) ≡ 0
proof fn lemma_cramer_alternating_dot_zero<T: Ring>(
    cd: Vec2<T>, ua: Vec2<T>, ub: Vec2<T>, uc: Vec2<T>,
)
    ensures
        vec2_dot(cd, ua).mul(det2d(ub, uc))
            .sub(vec2_dot(cd, ub).mul(det2d(ua, uc)))
            .add(vec2_dot(cd, uc).mul(det2d(ua, ub)))
            .eqv(T::zero()),
{
    let D_bc = det2d(ub, uc);
    let D_ac = det2d(ua, uc);
    let D_ab = det2d(ua, ub);
    let da = vec2_dot(cd, ua);
    let db = vec2_dot(cd, ub);
    let dc = vec2_dot(cd, uc);
    let I1 = da.mul(D_bc);
    let I2 = db.mul(D_ac);
    let I3 = dc.mul(D_ab);

    //  --- Cramer dot form: det(uc,ub)*da + D_ac*db ≡ D_ab*dc ---
    lemma_cramer_dot_form::<T>(cd, ua, ub, uc);

    //  --- Convert Cramer term 1: det2d(uc,ub)*da ≡ -I1 ---
    lemma_det2d_antisymmetric::<T>(uc, ub);
    //  det2d(uc,ub) ≡ -D_bc
    T::axiom_eqv_reflexive(da);
    ring_lemmas::lemma_mul_congruence::<T>(det2d(uc, ub), D_bc.neg(), da, da);
    //  det2d(uc,ub)*da ≡ (-D_bc)*da
    ring_lemmas::lemma_mul_neg_left::<T>(D_bc, da);
    //  (-D_bc)*da ≡ -(D_bc*da)
    T::axiom_eqv_transitive(det2d(uc, ub).mul(da), D_bc.neg().mul(da), D_bc.mul(da).neg());
    T::axiom_mul_commutative(D_bc, da);
    additive_group_lemmas::lemma_neg_congruence::<T>(D_bc.mul(da), da.mul(D_bc));
    T::axiom_eqv_transitive(det2d(uc, ub).mul(da), D_bc.mul(da).neg(), I1.neg());
    //  det2d(uc,ub)*da ≡ -I1

    //  --- Convert Cramer term 2: D_ac*db ≡ I2 ---
    T::axiom_mul_commutative(D_ac, db);

    //  --- Convert Cramer RHS: D_ab*dc ≡ I3 ---
    T::axiom_mul_commutative(D_ab, dc);

    //  --- Chain: (-I1) + I2 ≡ I3 ---
    additive_group_lemmas::lemma_add_congruence::<T>(
        det2d(uc, ub).mul(da), I1.neg(),
        D_ac.mul(db), I2,
    );
    //  Cramer_LHS ≡ (-I1) + I2
    T::axiom_eqv_symmetric(
        det2d(uc, ub).mul(da).add(D_ac.mul(db)),
        I1.neg().add(I2),
    );
    T::axiom_eqv_transitive(
        I1.neg().add(I2),
        det2d(uc, ub).mul(da).add(D_ac.mul(db)),
        D_ab.mul(dc),
    );
    T::axiom_eqv_transitive(I1.neg().add(I2), D_ab.mul(dc), I3);
    //  (-I1) + I2 ≡ I3

    //  --- Derive I3 - I2 ≡ -I1 ---
    T::axiom_eqv_reflexive(I2);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        I1.neg().add(I2), I3, I2, I2,
    );
    //  (-I1 + I2) - I2 ≡ I3 - I2
    additive_group_lemmas::lemma_add_then_sub_cancel::<T>(I1.neg(), I2);
    //  (-I1 + I2) - I2 ≡ -I1
    T::axiom_eqv_symmetric(I1.neg().add(I2).sub(I2), I3.sub(I2));
    T::axiom_eqv_transitive(I3.sub(I2), I1.neg().add(I2).sub(I2), I1.neg());
    //  I3 - I2 ≡ -I1

    //  --- I1 + (I3 - I2) ≡ 0 ---
    additive_group_lemmas::lemma_add_congruence_right::<T>(I1, I3.sub(I2), I1.neg());
    T::axiom_add_inverse_right(I1);
    T::axiom_eqv_transitive(I1.add(I3.sub(I2)), I1.add(I1.neg()), T::zero());

    //  --- Convert I1.sub(I2).add(I3) to I1.add(I3.sub(I2)) ---
    T::axiom_sub_is_add_neg(I1, I2);
    T::axiom_eqv_reflexive(I3);
    additive_group_lemmas::lemma_add_congruence::<T>(
        I1.sub(I2), I1.add(I2.neg()), I3, I3,
    );
    T::axiom_add_associative(I1, I2.neg(), I3);
    T::axiom_eqv_transitive(
        I1.sub(I2).add(I3),
        I1.add(I2.neg()).add(I3),
        I1.add(I2.neg().add(I3)),
    );
    T::axiom_add_commutative(I2.neg(), I3);
    T::axiom_sub_is_add_neg(I3, I2);
    T::axiom_eqv_symmetric(I3.sub(I2), I3.add(I2.neg()));
    T::axiom_eqv_transitive(I2.neg().add(I3), I3.add(I2.neg()), I3.sub(I2));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        I1, I2.neg().add(I3), I3.sub(I2),
    );
    T::axiom_eqv_transitive(
        I1.sub(I2).add(I3),
        I1.add(I2.neg().add(I3)),
        I1.add(I3.sub(I2)),
    );

    //  --- Final chain: I1.sub(I2).add(I3) ≡ 0 ---
    T::axiom_eqv_transitive(I1.sub(I2).add(I3), I1.add(I3.sub(I2)), T::zero());
}

//  =========================================================================
//  Helper: alternating sum addition (zip of two a-b+c sums)
//  =========================================================================

///  (a-b+c) + (p-q+r) ≡ (a+p) - (b+q) + (c+r)
///  Used to decompose incircle + phi*orient into pairwise sums.
proof fn lemma_alternating_sum_add<T: Ring>(
    a: T, b: T, c: T, p: T, q: T, r: T,
)
    ensures
        a.sub(b).add(c).add(p.sub(q).add(r)).eqv(
            a.add(p).sub(b.add(q)).add(c.add(r))
        ),
{
    let nb = b.neg();
    let nq = q.neg();

    //  Phase 1: Convert subs → add+neg
    T::axiom_sub_is_add_neg(a, b);   //  a-b ≡ a+nb
    T::axiom_sub_is_add_neg(p, q);   //  p-q ≡ p+nq

    T::axiom_eqv_reflexive(c);
    additive_group_lemmas::lemma_add_congruence::<T>(a.sub(b), a.add(nb), c, c);
    //  (a-b)+c ≡ (a+nb)+c

    T::axiom_eqv_reflexive(r);
    additive_group_lemmas::lemma_add_congruence::<T>(p.sub(q), p.add(nq), r, r);
    //  (p-q)+r ≡ (p+nq)+r

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b).add(c), a.add(nb).add(c),
        p.sub(q).add(r), p.add(nq).add(r),
    );
    //  LHS ≡ ((a+nb)+c) + ((p+nq)+r)  =: L1

    //  Phase 2: Rearrange L1 → L2 using add_rearrange_2x2
    //  ((a+nb)+c) + ((p+nq)+r) ≡ ((a+nb)+(p+nq)) + (c+r)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.add(nb), c, p.add(nq), r,
    );

    T::axiom_eqv_transitive(
        a.sub(b).add(c).add(p.sub(q).add(r)),       //  LHS
        a.add(nb).add(c).add(p.add(nq).add(r)),     //  L1
        a.add(nb).add(p.add(nq)).add(c.add(r)),     //  L2
    );

    //  Phase 3: Rearrange inner pair (a+nb)+(p+nq) → (a+p)+(nb+nq)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, nb, p, nq);

    //  Phase 4: Combine negs: nb+nq ≡ -(b+q)
    additive_group_lemmas::lemma_neg_add::<T>(b, q);
    //  -(b+q) ≡ nb+nq
    T::axiom_eqv_symmetric(b.add(q).neg(), nb.add(nq));
    //  nb+nq ≡ -(b+q)

    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(p), nb.add(nq), b.add(q).neg(),
    );
    //  (a+p)+(nb+nq) ≡ (a+p)+(-(b+q))

    //  Chain: (a+nb)+(p+nq) ≡ (a+p)+(nb+nq) ≡ (a+p)+(-(b+q))
    T::axiom_eqv_transitive(
        a.add(nb).add(p.add(nq)),
        a.add(p).add(nb.add(nq)),
        a.add(p).add(b.add(q).neg()),
    );

    //  Phase 5: (a+p)+(-(b+q)) ≡ (a+p).sub(b+q) via sub_is_add_neg reversed
    T::axiom_sub_is_add_neg(a.add(p), b.add(q));
    T::axiom_eqv_symmetric(
        a.add(p).sub(b.add(q)),
        a.add(p).add(b.add(q).neg()),
    );
    T::axiom_eqv_transitive(
        a.add(nb).add(p.add(nq)),
        a.add(p).add(b.add(q).neg()),
        a.add(p).sub(b.add(q)),
    );

    //  Phase 6: Thread into L2 → RHS
    //  L2 = ((a+nb)+(p+nq)) + (c+r), RHS = ((a+p).sub(b+q)) + (c+r)
    T::axiom_eqv_reflexive(c.add(r));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(nb).add(p.add(nq)), a.add(p).sub(b.add(q)),
        c.add(r), c.add(r),
    );
    //  L2 ≡ RHS

    //  Final: LHS ≡ L2 ≡ RHS
    T::axiom_eqv_transitive(
        a.sub(b).add(c).add(p.sub(q).add(r)),
        a.add(nb).add(p.add(nq)).add(c.add(r)),
        a.add(p).sub(b.add(q)).add(c.add(r)),
    );
}

//  =========================================================================
//  Helper: factor common left multiplier from alternating sum
//  =========================================================================

///  k*a - k*b + k*c ≡ k*(a - b + c)
proof fn lemma_factor_alternating_sum<T: Ring>(
    k: T, a: T, b: T, c: T,
)
    ensures
        k.mul(a).sub(k.mul(b)).add(k.mul(c)).eqv(
            k.mul(a.sub(b).add(c))
        ),
{
    //  k*(a-b) ≡ k*a - k*b
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(k, a, b);
    T::axiom_eqv_symmetric(k.mul(a.sub(b)), k.mul(a).sub(k.mul(b)));
    //  k*a - k*b ≡ k*(a-b)

    //  (k*a - k*b) + k*c ≡ k*(a-b) + k*c
    T::axiom_eqv_reflexive(k.mul(c));
    additive_group_lemmas::lemma_add_congruence::<T>(
        k.mul(a).sub(k.mul(b)), k.mul(a.sub(b)),
        k.mul(c), k.mul(c),
    );

    //  k*((a-b)+c) ≡ k*(a-b) + k*c [left distributivity]
    T::axiom_mul_distributes_left(k, a.sub(b), c);
    T::axiom_eqv_symmetric(k.mul(a.sub(b).add(c)), k.mul(a.sub(b)).add(k.mul(c)));

    //  Chain: (k*a - k*b) + k*c ≡ k*(a-b) + k*c ≡ k*(a-b+c)
    T::axiom_eqv_transitive(
        k.mul(a).sub(k.mul(b)).add(k.mul(c)),
        k.mul(a.sub(b)).add(k.mul(c)),
        k.mul(a.sub(b).add(c)),
    );
}

//  =========================================================================
//  Helper: orient2d decomposition relative to a base point
//  =========================================================================

///  orient2d(a,b,c) ≡ det2d(ub,uc) - det2d(ua,uc) + det2d(ua,ub)
///  where uv = sub2(v, d).
proof fn lemma_orient2d_rebase<T: Ring>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
    {
        let ua = sub2(a, d);
        let ub = sub2(b, d);
        let uc = sub2(c, d);
        orient2d(a, b, c).eqv(
            det2d(ub, uc).sub(det2d(ua, uc)).add(det2d(ua, ub))
        )
    },
{
    let ua = sub2(a, d);
    let ub = sub2(b, d);
    let uc = sub2(c, d);
    let D_bc = det2d(ub, uc);
    let D_ac = det2d(ua, uc);
    let D_ab = det2d(ua, ub);

    //  Step 1: sub2(b,a) ≡ ub - ua, sub2(c,a) ≡ uc - ua
    lemma_sub2_rebase::<T>(b, a, d);
    lemma_sub2_rebase::<T>(c, a, d);

    //  Step 2: orient2d = det2d(sub2(b,a), sub2(c,a)) ≡ det2d(ub-ua, uc-ua)
    lemma_det2d_congruence::<T>(sub2(b, a), ub.sub(ua), sub2(c, a), uc.sub(ua));

    //  Step 3: det2d(ub-ua, uc-ua) ≡ (D_bc - det2d(ub,ua)) - D_ac  [det2d_sub_sub]
    crate::incircle::lemma_det2d_sub_sub::<T>(ua, ub, uc);
    T::axiom_eqv_transitive(
        orient2d(a, b, c),
        det2d(ub.sub(ua), uc.sub(ua)),
        D_bc.sub(det2d(ub, ua)).sub(D_ac),
    );

    //  Step 4: det2d(ub,ua) ≡ -det2d(ua,ub) = -D_ab  [antisymmetry]
    lemma_det2d_antisymmetric::<T>(ub, ua);

    //  Step 5: D_bc - det2d(ub,ua) ≡ D_bc - (-D_ab) ≡ D_bc + D_ab  [sub_congruence + sub_neg_is_add]
    T::axiom_eqv_reflexive(D_bc);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        D_bc, D_bc, det2d(ub, ua), D_ab.neg(),
    );
    crate::incircle::lemma_sub_neg_is_add::<T>(D_bc, D_ab);
    T::axiom_eqv_transitive(
        D_bc.sub(det2d(ub, ua)),
        D_bc.sub(D_ab.neg()),
        D_bc.add(D_ab),
    );

    //  Step 6: (D_bc - det2d(ub,ua)) - D_ac ≡ (D_bc + D_ab) - D_ac  [sub_congruence]
    T::axiom_eqv_reflexive(D_ac);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        D_bc.sub(det2d(ub, ua)), D_bc.add(D_ab), D_ac, D_ac,
    );
    T::axiom_eqv_transitive(
        orient2d(a, b, c),
        D_bc.sub(det2d(ub, ua)).sub(D_ac),
        D_bc.add(D_ab).sub(D_ac),
    );

    //  Step 7: (D_bc + D_ab) - D_ac ≡ (D_bc - D_ac) + D_ab  [add_sub_rearrange]
    crate::intersection3d::lemma_add_sub_rearrange::<T>(D_bc, D_ab, D_ac);
    T::axiom_eqv_transitive(
        orient2d(a, b, c),
        D_bc.add(D_ab).sub(D_ac),
        D_bc.sub(D_ac).add(D_ab),
    );
}

//  =========================================================================
//  Helper: circumcenter-incircle-orient identity
//  =========================================================================

///  Under circumcenter conditions:
///    incircle2d(a,b,c,d) ≡ -(sq_dist(O,d) - sq_dist(O,a)) * orient2d(a,b,c)
///
///  Proof strategy:
///  1. Let cd = O-d, ua = a-d, ub = b-d, uc = c-d, la = norm_sq(ua), etc.
///  2. φ = sq_dist(O,d) - sq_dist(O,a) satisfies la+φ ≡ 2*dot(cd,ua) (and similarly for lb, lc)
///  3. incircle2d + φ*orient2d = 2*(dot·det alternating sum) = 0 by Cramer
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

    //  --- Phase 1: Show la + phi ≡ 2*dot(cd, ua) ---
    //  sub2(center, a) ≡ cd.sub(ua) by lemma_sub2_rebase
    lemma_sub2_rebase::<T>(center, a, d);
    //  norm_sq(cd.sub(ua)) ≡ norm_sq(cd) - 2*dot(cd,ua) + norm_sq(ua) = norm_sq(cd) - 2*dot(cd,ua) + la
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, a), cd.sub(ua));
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, ua);
    //  sq_dist(O,a) ≡ norm_sq(cd) - 2*dot(cd,ua) + la
    T::axiom_eqv_transitive(
        sq_dist_2d(center, a),
        vec2_norm_sq(cd.sub(ua)),
        vec2_norm_sq(cd).sub(verus_algebra::convex::two::<T>().mul(vec2_dot(cd, ua))).add(la),
    );
    //  phi = norm_sq(cd) - sq_dist(O,a) ≡ norm_sq(cd) - (norm_sq(cd) - 2*dot(cd,ua) + la)
    //      = 2*dot(cd,ua) - la
    //  So la + phi ≡ 2*dot(cd,ua)

    //  --- Phase 1b: Similarly for lb + phi and lc + phi ---
    //  sub2(center, b) ≡ cd.sub(ub), sub2(center, c) ≡ cd.sub(uc)
    lemma_sub2_rebase::<T>(center, b, d);
    lemma_sub2_rebase::<T>(center, c, d);
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, b), cd.sub(ub));
    verus_linalg::vec2::ops::lemma_norm_sq_congruence::<T>(sub2(center, c), cd.sub(uc));
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, ub);
    verus_linalg::vec2::ops::lemma_norm_sq_sub_expand::<T>(cd, uc);

    //  Complete transitivity chains for sq_dist(O,b) and sq_dist(O,c)
    let ncd = vec2_norm_sq(cd);
    let tw_a = verus_algebra::convex::two::<T>().mul(vec2_dot(cd, ua));
    let tw_b = verus_algebra::convex::two::<T>().mul(vec2_dot(cd, ub));
    let tw_c = verus_algebra::convex::two::<T>().mul(vec2_dot(cd, uc));
    let D_bc = det2d(ub, uc);
    let D_ac = det2d(ua, uc);
    let D_ab = det2d(ua, ub);

    T::axiom_eqv_transitive(
        sq_dist_2d(center, b), vec2_norm_sq(cd.sub(ub)), ncd.sub(tw_b).add(lb),
    );
    T::axiom_eqv_transitive(
        sq_dist_2d(center, c), vec2_norm_sq(cd.sub(uc)), ncd.sub(tw_c).add(lc),
    );

    //  --- Phase 2: phi + lv ≡ tw_v for each vertex ---
    //  For vertex a: phi = ncd - sq_dist(O,a) definitionally
    T::axiom_eqv_reflexive(phi);
    lemma_phi_plus_lift_vertex::<T>(ncd, tw_a, la, sq_dist_2d(center, a), phi);

    //  For vertex b: circumcenter gives sq_dist(O,a) ≡ sq_dist(O,b)
    T::axiom_eqv_reflexive(ncd);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        ncd, ncd, sq_dist_2d(center, a), sq_dist_2d(center, b),
    );
    lemma_phi_plus_lift_vertex::<T>(ncd, tw_b, lb, sq_dist_2d(center, b), phi);

    //  For vertex c: sq_dist(O,a) ≡ sq_dist(O,c) by transitivity
    T::axiom_eqv_transitive(
        sq_dist_2d(center, a), sq_dist_2d(center, b), sq_dist_2d(center, c),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        ncd, ncd, sq_dist_2d(center, a), sq_dist_2d(center, c),
    );
    lemma_phi_plus_lift_vertex::<T>(ncd, tw_c, lc, sq_dist_2d(center, c), phi);

    //  --- Phase 3: Expand phi*orient into phi*D_bc - phi*D_ac + phi*D_ab ---
    lemma_orient2d_rebase::<T>(a, b, c, d);
    T::axiom_eqv_reflexive(phi);
    ring_lemmas::lemma_mul_congruence::<T>(
        phi, phi, orient2d(a, b, c), D_bc.sub(D_ac).add(D_ab),
    );
    //  phi*orient ≡ phi*(D_bc - D_ac + D_ab)
    //  Reverse of factor_alternating_sum: phi*(D_bc-D_ac+D_ab) ≡ phi*D_bc - phi*D_ac + phi*D_ab
    lemma_factor_alternating_sum::<T>(phi, D_bc, D_ac, D_ab);
    T::axiom_eqv_symmetric(
        phi.mul(D_bc).sub(phi.mul(D_ac)).add(phi.mul(D_ab)),
        phi.mul(D_bc.sub(D_ac).add(D_ab)),
    );
    T::axiom_eqv_transitive(
        phi.mul(orient2d(a, b, c)),
        phi.mul(D_bc.sub(D_ac).add(D_ab)),
        phi.mul(D_bc).sub(phi.mul(D_ac)).add(phi.mul(D_ab)),
    );

    //  --- Phase 4: Combine incircle + phi*orient via alternating_sum_add ---
    //  incircle = la*D_bc - lb*D_ac + lc*D_ab (by spec unfolding)
    //  phi_expanded = phi*D_bc - phi*D_ac + phi*D_ab
    T::axiom_eqv_reflexive(incircle2d(a, b, c, d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        incircle2d(a, b, c, d), incircle2d(a, b, c, d),
        phi.mul(orient2d(a, b, c)),
        phi.mul(D_bc).sub(phi.mul(D_ac)).add(phi.mul(D_ab)),
    );
    //  incircle + phi*orient ≡ incircle + phi_expanded

    //  By Helper 3: (a-b+c) + (p-q+r) ≡ (a+p) - (b+q) + (c+r)
    lemma_alternating_sum_add::<T>(
        la.mul(D_bc), lb.mul(D_ac), lc.mul(D_ab),
        phi.mul(D_bc), phi.mul(D_ac), phi.mul(D_ab),
    );

    T::axiom_eqv_transitive(
        incircle2d(a, b, c, d).add(phi.mul(orient2d(a, b, c))),
        incircle2d(a, b, c, d).add(phi.mul(D_bc).sub(phi.mul(D_ac)).add(phi.mul(D_ab))),
        la.mul(D_bc).add(phi.mul(D_bc))
            .sub(lb.mul(D_ac).add(phi.mul(D_ac)))
            .add(lc.mul(D_ab).add(phi.mul(D_ab))),
    );

    //  --- Phase 5: Factor each pair: lv*D + phi*D ≡ (lv+phi)*D ≡ tw_v*D ---
    //  Vertex a pair
    ring_lemmas::lemma_mul_distributes_right::<T>(la, phi, D_bc);
    T::axiom_eqv_symmetric(la.add(phi).mul(D_bc), la.mul(D_bc).add(phi.mul(D_bc)));
    T::axiom_add_commutative(la, phi);
    T::axiom_eqv_transitive(la.add(phi), phi.add(la), tw_a);
    T::axiom_eqv_reflexive(D_bc);
    ring_lemmas::lemma_mul_congruence::<T>(la.add(phi), tw_a, D_bc, D_bc);
    T::axiom_eqv_transitive(
        la.mul(D_bc).add(phi.mul(D_bc)), la.add(phi).mul(D_bc), tw_a.mul(D_bc),
    );

    //  Vertex b pair
    ring_lemmas::lemma_mul_distributes_right::<T>(lb, phi, D_ac);
    T::axiom_eqv_symmetric(lb.add(phi).mul(D_ac), lb.mul(D_ac).add(phi.mul(D_ac)));
    T::axiom_add_commutative(lb, phi);
    T::axiom_eqv_transitive(lb.add(phi), phi.add(lb), tw_b);
    T::axiom_eqv_reflexive(D_ac);
    ring_lemmas::lemma_mul_congruence::<T>(lb.add(phi), tw_b, D_ac, D_ac);
    T::axiom_eqv_transitive(
        lb.mul(D_ac).add(phi.mul(D_ac)), lb.add(phi).mul(D_ac), tw_b.mul(D_ac),
    );

    //  Vertex c pair
    ring_lemmas::lemma_mul_distributes_right::<T>(lc, phi, D_ab);
    T::axiom_eqv_symmetric(lc.add(phi).mul(D_ab), lc.mul(D_ab).add(phi.mul(D_ab)));
    T::axiom_add_commutative(lc, phi);
    T::axiom_eqv_transitive(lc.add(phi), phi.add(lc), tw_c);
    T::axiom_eqv_reflexive(D_ab);
    ring_lemmas::lemma_mul_congruence::<T>(lc.add(phi), tw_c, D_ab, D_ab);
    T::axiom_eqv_transitive(
        lc.mul(D_ab).add(phi.mul(D_ab)), lc.add(phi).mul(D_ab), tw_c.mul(D_ab),
    );

    //  Combine: paired_form ≡ tw_a*D_bc - tw_b*D_ac + tw_c*D_ab
    additive_group_lemmas::lemma_sub_congruence::<T>(
        la.mul(D_bc).add(phi.mul(D_bc)), tw_a.mul(D_bc),
        lb.mul(D_ac).add(phi.mul(D_ac)), tw_b.mul(D_ac),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        la.mul(D_bc).add(phi.mul(D_bc)).sub(lb.mul(D_ac).add(phi.mul(D_ac))),
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)),
        lc.mul(D_ab).add(phi.mul(D_ab)),
        tw_c.mul(D_ab),
    );

    //  --- Phase 6: Factor two() from cramer sum ---
    let two = verus_algebra::convex::two::<T>();
    let I1 = vec2_dot(cd, ua).mul(D_bc);
    let I2 = vec2_dot(cd, ub).mul(D_ac);
    let I3 = vec2_dot(cd, uc).mul(D_ab);

    //  tw_v*D = (two*dot)*D ≡ two*(dot*D) by associativity
    T::axiom_mul_associative(two, vec2_dot(cd, ua), D_bc);
    T::axiom_eqv_symmetric(two.mul(I1), tw_a.mul(D_bc));
    T::axiom_mul_associative(two, vec2_dot(cd, ub), D_ac);
    T::axiom_eqv_symmetric(two.mul(I2), tw_b.mul(D_ac));
    T::axiom_mul_associative(two, vec2_dot(cd, uc), D_ab);
    T::axiom_eqv_symmetric(two.mul(I3), tw_c.mul(D_ab));

    //  cramer_sum ≡ two*I1 - two*I2 + two*I3
    additive_group_lemmas::lemma_sub_congruence::<T>(
        tw_a.mul(D_bc), two.mul(I1), tw_b.mul(D_ac), two.mul(I2),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)), two.mul(I1).sub(two.mul(I2)),
        tw_c.mul(D_ab), two.mul(I3),
    );

    //  two*I1 - two*I2 + two*I3 ≡ two*(I1 - I2 + I3) by factor_alternating_sum
    lemma_factor_alternating_sum::<T>(two, I1, I2, I3);
    T::axiom_eqv_transitive(
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)).add(tw_c.mul(D_ab)),
        two.mul(I1).sub(two.mul(I2)).add(two.mul(I3)),
        two.mul(I1.sub(I2).add(I3)),
    );

    //  --- Phase 7: Cramer zero: I1 - I2 + I3 ≡ 0 ---
    lemma_cramer_alternating_dot_zero::<T>(cd, ua, ub, uc);
    T::axiom_eqv_reflexive(two);
    ring_lemmas::lemma_mul_congruence::<T>(two, two, I1.sub(I2).add(I3), T::zero());
    T::axiom_mul_zero_right(two);
    T::axiom_eqv_transitive(two.mul(I1.sub(I2).add(I3)), two.mul(T::zero()), T::zero());
    //  cramer_sum ≡ 0
    T::axiom_eqv_transitive(
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)).add(tw_c.mul(D_ab)),
        two.mul(I1.sub(I2).add(I3)),
        T::zero(),
    );

    //  --- Phase 8: Chain all: incircle + phi*orient ≡ paired ≡ cramer ≡ 0 ---
    T::axiom_eqv_transitive(
        incircle2d(a, b, c, d).add(phi.mul(orient2d(a, b, c))),
        la.mul(D_bc).add(phi.mul(D_bc))
            .sub(lb.mul(D_ac).add(phi.mul(D_ac)))
            .add(lc.mul(D_ab).add(phi.mul(D_ab))),
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)).add(tw_c.mul(D_ab)),
    );
    T::axiom_eqv_transitive(
        incircle2d(a, b, c, d).add(phi.mul(orient2d(a, b, c))),
        tw_a.mul(D_bc).sub(tw_b.mul(D_ac)).add(tw_c.mul(D_ab)),
        T::zero(),
    );

    //  --- Phase 9: Conclude incircle ≡ phi.neg() * orient ---
    //  phi*orient + incircle ≡ 0 (by commutativity)
    T::axiom_add_commutative(
        phi.mul(orient2d(a, b, c)), incircle2d(a, b, c, d),
    );
    T::axiom_eqv_transitive(
        phi.mul(orient2d(a, b, c)).add(incircle2d(a, b, c, d)),
        incircle2d(a, b, c, d).add(phi.mul(orient2d(a, b, c))),
        T::zero(),
    );
    //  By neg_unique: incircle ≡ -(phi*orient)
    additive_group_lemmas::lemma_neg_unique::<T>(
        phi.mul(orient2d(a, b, c)), incircle2d(a, b, c, d),
    );
    //  -(phi*orient) ≡ phi.neg()*orient by mul_neg_left (reversed)
    ring_lemmas::lemma_mul_neg_left::<T>(phi, orient2d(a, b, c));
    T::axiom_eqv_symmetric(
        phi.neg().mul(orient2d(a, b, c)),
        phi.mul(orient2d(a, b, c)).neg(),
    );
    T::axiom_eqv_transitive(
        incircle2d(a, b, c, d),
        phi.mul(orient2d(a, b, c)).neg(),
        phi.neg().mul(orient2d(a, b, c)),
    );
}

///  Delaunay-Voronoi duality: if (a,b,c) is a CCW Delaunay triangle
///  (d outside circumcircle), then circumcenter is closer to a than to d.
///  Key theorem connecting incircle predicate to Voronoi distance.
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
    //  Step 1: From the algebraic identity
    lemma_circumcenter_incircle_orient::<T>(a, b, c, d, center);
    //  incircle2d ≡ -phi * orient2d where phi = sq_dist(O,d) - sq_dist(O,a)

    let phi = sq_dist_2d(center, d).sub(sq_dist_2d(center, a));
    let orient = orient2d(a, b, c);

    //  Step 2: incircle2d < 0 (given), incircle2d ≡ phi.neg() * orient (by identity)
    //  So phi.neg() * orient < 0
    T::axiom_eqv_reflexive(T::zero());
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        incircle2d(a, b, c, d), phi.neg().mul(orient),
        T::zero(), T::zero(),
    );

    //  Step 3: phi.neg() * orient ≡ -(phi * orient) [mul_neg_left]
    ring_lemmas::lemma_mul_neg_left::<T>(phi, orient);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        phi.neg().mul(orient), phi.mul(orient).neg(),
        T::zero(), T::zero(),
    );
    //  Now: phi.mul(orient).neg().lt(T::zero())

    //  Step 4: -(phi*orient) < 0 implies 0 < phi*orient
    //  Use lt_neg_flip: a < b ==> b.neg() < a.neg()
    //  We have phi.mul(orient).neg() < 0
    //  Apply lt_neg_flip(phi.mul(orient).neg(), T::zero()):
    //    ensures: T::zero().neg() < phi.mul(orient).neg().neg()
    ordered_ring_lemmas::lemma_lt_neg_flip::<T>(phi.mul(orient).neg(), T::zero());
    //  neg(0) ≡ 0, neg(neg(x)) ≡ x
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_neg_involution::<T>(phi.mul(orient));
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero().neg(), T::zero(),
        phi.mul(orient).neg().neg(), phi.mul(orient),
    );
    //  Now: T::zero().lt(phi.mul(orient))

    //  Step 5: Derive 0 < phi from 0 < phi*orient and 0 < orient.
    //  Use trichotomy on (0, phi) and rule out the other two cases.

    //  Rule out 0 ≡ phi: if phi ≡ 0 then phi*orient ≡ 0, contradicting 0 < phi*orient
    assert(!T::zero().eqv(phi)) by {
        if T::zero().eqv(phi) {
            T::axiom_eqv_symmetric(T::zero(), phi);
            //  phi.eqv(T::zero())
            T::axiom_eqv_reflexive(orient);
            ring_lemmas::lemma_mul_congruence::<T>(phi, T::zero(), orient, orient);
            //  phi*orient ≡ 0*orient
            ring_lemmas::lemma_mul_zero_left::<T>(orient);
            //  0*orient ≡ 0
            T::axiom_eqv_transitive(phi.mul(orient), T::zero().mul(orient), T::zero());
            //  phi*orient ≡ 0
            T::axiom_eqv_symmetric(phi.mul(orient), T::zero());
            //  0 ≡ phi*orient — contradicts 0 < phi*orient via trichotomy
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi.mul(orient));
        }
    };

    //  Rule out phi < 0: if phi < 0 then phi*orient ≤ 0, contradicting 0 < phi*orient
    assert(!phi.lt(T::zero())) by {
        if phi.lt(T::zero()) {
            //  phi < 0 implies phi ≤ 0
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(phi, T::zero());
            //  0 < orient implies 0 ≤ orient
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(T::zero(), orient);
            //  phi ≤ 0, 0 ≤ orient → phi*orient ≤ 0*orient
            T::axiom_le_mul_nonneg_monotone(phi, T::zero(), orient);
            //  0*orient ≡ 0
            ring_lemmas::lemma_mul_zero_left::<T>(orient);
            //  phi*orient ≤ 0
            ordered_ring_lemmas::lemma_le_congruence_right::<T>(
                phi.mul(orient), T::zero().mul(orient), T::zero(),
            );
            //  0 < phi*orient → ¬(phi*orient < 0)
            ordered_ring_lemmas::lemma_lt_asymmetric::<T>(T::zero(), phi.mul(orient));
            //  phi*orient ≤ 0 = lt ∨ eqv, and ¬lt → eqv
            ordered_ring_lemmas::lemma_le_iff_lt_or_eqv::<T>(phi.mul(orient), T::zero());
            //  phi*orient ≡ 0 → 0 ≡ phi*orient
            T::axiom_eqv_symmetric(phi.mul(orient), T::zero());
            //  Contradicts 0 < phi*orient via trichotomy
            ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi.mul(orient));
        }
    };

    //  Trichotomy: 0 < phi is the only remaining case
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), phi);

    //  Step 6: Convert 0 < phi = dd - da to da < dd
    let da = sq_dist_2d(center, a);
    let dd = sq_dist_2d(center, d);
    //  0 < phi, add da to both sides: 0 + da < phi + da
    ordered_ring_lemmas::lemma_lt_add_compatible::<T>(T::zero(), phi, da);
    //  0 + da ≡ da
    additive_group_lemmas::lemma_add_zero_left::<T>(da);
    //  phi + da = (dd - da) + da ≡ dd
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(dd, da);
    T::axiom_eqv_reflexive(da);
    ordered_ring_lemmas::lemma_lt_congruence_both::<T>(
        T::zero().add(da), da, phi.add(da), dd,
    );
    //  da < dd ✓
}

} //  verus!
