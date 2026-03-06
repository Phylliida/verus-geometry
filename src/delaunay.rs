use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use crate::point2::*;
use crate::point3::*;
use crate::orientation_sign::*;
use crate::incircle::*;
use crate::insphere::*;

verus! {

// =========================================================================
// 2D Delaunay predicates
// =========================================================================

/// An edge (a,b) shared by triangles (a,b,c) and (b,a,d) is locally Delaunay
/// if d is NOT strictly inside the circumcircle of (a,b,c).
pub open spec fn is_locally_delaunay_edge_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    !incircle2d_positive(a, b, c, d)
}

/// The edge needs a Delaunay flip if d IS strictly inside the circumcircle.
pub open spec fn is_delaunay_flip_needed_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d_positive(a, b, c, d)
}

/// Four points are cocircular (d lies on circumcircle of a,b,c).
pub open spec fn is_cocircular_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
) -> bool {
    incircle2d_cocircular(a, b, c, d)
}

// =========================================================================
// 3D Delaunay predicates
// =========================================================================

/// An edge is locally Delaunay in 3D if e is NOT strictly inside the circumsphere of (a,b,c,d).
pub open spec fn is_locally_delaunay_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    !insphere3d_positive(a, b, c, d, e)
}

/// A Delaunay flip is needed in 3D if e IS strictly inside the circumsphere.
pub open spec fn is_delaunay_flip_needed_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    insphere3d_positive(a, b, c, d, e)
}

/// Five points are cospherical.
pub open spec fn is_cospherical_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
) -> bool {
    insphere3d_cospherical(a, b, c, d, e)
}

// =========================================================================
// 2D Delaunay lemmas
// =========================================================================

/// Cocircular points are automatically locally Delaunay.
pub proof fn lemma_cocircular_implies_delaunay_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        is_cocircular_2d(a, b, c, d),
    ensures
        is_locally_delaunay_edge_2d(a, b, c, d),
{
    // cocircular means incircle2d ≡ 0, so not positive
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    // incircle2d_cocircular → incircle2d.eqv(zero) → !incircle2d_positive
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), incircle2d(a, b, c, d));
    // zero ≡ incircle2d, so !(zero < incircle2d)
    T::axiom_eqv_symmetric(incircle2d(a, b, c, d), T::zero());
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), incircle2d(a, b, c, d));
}

/// Delaunay and flip_needed are logical negations.
pub proof fn lemma_delaunay_negation_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        is_locally_delaunay_edge_2d(a, b, c, d) == !is_delaunay_flip_needed_2d(a, b, c, d),
{
    // Both unfold to !incircle2d_positive vs incircle2d_positive — trivially equal.
}

/// Delaunay is preserved under cyclic permutation (a,b,c) → (b,c,a).
pub proof fn lemma_delaunay_cyclic_abc_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        is_locally_delaunay_edge_2d(b, c, a, d) == is_locally_delaunay_edge_2d(a, b, c, d),
{
    lemma_incircle2d_sign_cyclic_abc::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(b, c, a, d);
}

/// Delaunay is preserved under cyclic permutation (a,b,c) → (c,a,b).
pub proof fn lemma_delaunay_cyclic_cab_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    ensures
        is_locally_delaunay_edge_2d(c, a, b, d) == is_locally_delaunay_edge_2d(a, b, c, d),
{
    lemma_incircle2d_sign_cyclic_cab::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(c, a, b, d);
}

/// If flip is needed for (a,b,c,d), then it's NOT needed for (b,a,c,d) — swapping
/// the shared edge vertices reverses the incircle sign.
pub proof fn lemma_flip_needed_swap_ab_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        is_delaunay_flip_needed_2d(a, b, c, d),
    ensures
        !is_delaunay_flip_needed_2d(b, a, c, d),
{
    lemma_incircle2d_sign_swap_ab::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(a, b, c, d);
    lemma_incircle2d_sign_matches::<T>(b, a, c, d);
}

/// After flipping edge (a,b) to (c,d), the new configuration is Delaunay.
/// Key theorem for Lawson's flip algorithm convergence.
#[verifier::external_body]
pub proof fn lemma_delaunay_flip_symmetric_2d<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>, d: Point2<T>,
)
    requires
        is_delaunay_flip_needed_2d(a, b, c, d),
    ensures
        is_locally_delaunay_edge_2d(c, d, b, a),
{
    // assume(false) — requires algebraic identity connecting incircle2d(a,b,c,d)
    // to incircle2d(c,d,b,a) via reference-point swap
}

// =========================================================================
// 3D Delaunay lemmas
// =========================================================================

/// Cospherical points are automatically locally Delaunay in 3D.
pub proof fn lemma_cospherical_implies_delaunay_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    requires
        is_cospherical_3d(a, b, c, d, e),
    ensures
        is_locally_delaunay_3d(a, b, c, d, e),
{
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), insphere3d(a, b, c, d, e));
    T::axiom_eqv_symmetric(insphere3d(a, b, c, d, e), T::zero());
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), insphere3d(a, b, c, d, e));
}

/// Delaunay 3D is preserved under cyclic permutation (b,c,d) → (c,d,b).
pub proof fn lemma_delaunay_cycle_bcd_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        is_locally_delaunay_3d(a, c, d, b, e) == is_locally_delaunay_3d(a, b, c, d, e),
{
    lemma_insphere3d_sign_cycle_bcd::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, c, d, b, e);
}

/// Delaunay 3D is preserved under cyclic permutation (a,b,c) → (b,c,a).
pub proof fn lemma_delaunay_cycle_abc_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    ensures
        is_locally_delaunay_3d(b, c, a, d, e) == is_locally_delaunay_3d(a, b, c, d, e),
{
    lemma_insphere3d_sign_cycle_abc::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(a, b, c, d, e);
    lemma_insphere3d_sign_matches::<T>(b, c, a, d, e);
}

/// Lawson's theorem for 3D: after a bistellar flip, the new configuration is Delaunay.
#[verifier::external_body]
pub proof fn lemma_flip_reverses_delaunay_3d<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>, e: Point3<T>,
)
    requires
        is_delaunay_flip_needed_3d(a, b, c, d, e),
    ensures
        is_locally_delaunay_3d(b, c, d, a, e),
{
    // assume(false) — Lawson's theorem requires convex combination argument
}

} // verus!
