use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use crate::point2::*;
use crate::point3::*;
use crate::orient2d::*;
use crate::orient3d::{orient3d, lemma_orient3d_swap_cd, lemma_orient3d_swap_bc};
use crate::orientation_sign::*;

verus! {

// =========================================================================
// 3.1 — Point vs. line (2D)
// =========================================================================

/// Point p is strictly left of the directed line a→b.
pub open spec fn point_left_of_line<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    orient2d_positive(a, b, p)
}

/// Point p is strictly right of the directed line a→b.
pub open spec fn point_right_of_line<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    orient2d_negative(a, b, p)
}

/// Point p lies on the line through a and b.
pub open spec fn point_on_line<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> bool {
    orient2d_zero(a, b, p)
}

/// Exactly one of left, right, on-line holds.
pub proof fn lemma_point_line_trichotomy<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    ensures
        point_left_of_line(p, a, b) || point_right_of_line(p, a, b) || point_on_line(p, a, b),
        !(point_left_of_line(p, a, b) && point_right_of_line(p, a, b)),
        !(point_left_of_line(p, a, b) && point_on_line(p, a, b)),
        !(point_right_of_line(p, a, b) && point_on_line(p, a, b)),
{
    lemma_orient2d_trichotomy::<T>(a, b, p);
}

/// Swapping a, b flips left and right.
pub proof fn lemma_point_line_swap_ab<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
)
    ensures
        point_left_of_line(p, a, b) == point_right_of_line(p, b, a),
        point_right_of_line(p, a, b) == point_left_of_line(p, b, a),
        point_on_line(p, a, b) == point_on_line(p, b, a),
{
    // orient2d(a, b, p) and orient2d(b, a, p):
    // By swap_bc on orient2d(b, a, p) = orient2d(b, p, a) after cyclic?
    // Actually: orient2d(b, a, p). We need to relate this to orient2d(a, b, p).
    // orient2d(a, b, p) = det2d(b-a, p-a)
    // orient2d(b, a, p) = det2d(a-b, p-b)
    // Use swap_bc: orient2d(a, p, b) ≡ -orient2d(a, b, p)
    // Then cyclic: orient2d(a, p, b) ≡ orient2d(p, b, a) ≡ orient2d(b, a, p)
    // So orient2d(b, a, p) ≡ -orient2d(a, b, p)

    // Step 1: orient2d(a, p, b) ≡ -orient2d(a, b, p)
    lemma_orient2d_swap_bc::<T>(a, b, p);
    // Step 2: orient2d(b, a, p) ≡ orient2d(a, p, b) via cyclic twice
    // cyclic: orient2d(a, p, b) ≡ orient2d(p, b, a)
    lemma_orient2d_cyclic::<T>(a, p, b);
    // cyclic: orient2d(p, b, a) ≡ orient2d(b, a, p)
    lemma_orient2d_cyclic::<T>(p, b, a);
    // So orient2d(a, p, b) ≡ orient2d(p, b, a) ≡ orient2d(b, a, p)
    T::axiom_eqv_transitive(
        orient2d(a, p, b),
        orient2d(p, b, a),
        orient2d(b, a, p),
    );
    // orient2d(b, a, p) ≡ orient2d(a, p, b) ≡ -orient2d(a, b, p)
    T::axiom_eqv_symmetric(orient2d(a, p, b), orient2d(b, a, p));
    T::axiom_eqv_transitive(
        orient2d(b, a, p),
        orient2d(a, p, b),
        orient2d(a, b, p).neg(),
    );

    // Now use lemma_neg_flips_sign
    lemma_neg_flips_sign::<T>(orient2d(b, a, p), orient2d(a, b, p));
}

// =========================================================================
// 3.2 — Point vs. plane (3D)
// =========================================================================

/// Point p is strictly above the oriented plane (a, b, c).
pub open spec fn point_above_plane<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    orient3d_positive(a, b, c, p)
}

/// Point p is strictly below the oriented plane (a, b, c).
pub open spec fn point_below_plane<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    orient3d_negative(a, b, c, p)
}

/// Point p lies on the plane through a, b, c.
pub open spec fn point_on_plane<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    orient3d_zero(a, b, c, p)
}

/// Exactly one of above, below, on-plane holds.
pub proof fn lemma_point_plane_trichotomy<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        point_above_plane(p, a, b, c) || point_below_plane(p, a, b, c) || point_on_plane(p, a, b, c),
        !(point_above_plane(p, a, b, c) && point_below_plane(p, a, b, c)),
        !(point_above_plane(p, a, b, c) && point_on_plane(p, a, b, c)),
        !(point_below_plane(p, a, b, c) && point_on_plane(p, a, b, c)),
{
    lemma_orient3d_trichotomy::<T>(a, b, c, p);
}

/// Swapping b, c flips above and below.
pub proof fn lemma_point_plane_swap_bc<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        point_above_plane(p, a, b, c) == point_below_plane(p, a, c, b),
        point_below_plane(p, a, b, c) == point_above_plane(p, a, c, b),
        point_on_plane(p, a, b, c) == point_on_plane(p, a, c, b),
{
    // orient3d(a, c, b, p) ≡ -orient3d(a, b, c, p)
    lemma_orient3d_swap_bc::<T>(a, b, c, p);
    lemma_neg_flips_sign::<T>(orient3d(a, c, b, p), orient3d(a, b, c, p));
}

/// Swapping c, d in the plane definition flips above and below.
pub proof fn lemma_point_plane_swap_cd_plane<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        // Swap the last two plane vertices (b, c → c, b is done above via swap_bc)
        // Here: swap c with p-slot? No — this swaps the plane's c,d where d=p
        // orient3d(a, b, c, p) and orient3d(a, b, p, c):
        point_above_plane(p, a, b, c) == point_below_plane(c, a, b, p),
        point_below_plane(p, a, b, c) == point_above_plane(c, a, b, p),
        point_on_plane(p, a, b, c) == point_on_plane(c, a, b, p),
{
    // orient3d(a, b, p, c) ≡ -orient3d(a, b, c, p)
    lemma_orient3d_swap_cd::<T>(a, b, c, p);
    lemma_neg_flips_sign::<T>(orient3d(a, b, p, c), orient3d(a, b, c, p));
}

// =========================================================================
// 3.3 — Segment-plane crossing
// =========================================================================

/// Segment (d, e) strictly crosses the oriented plane (a, b, c):
/// the endpoints are on opposite sides.
pub open spec fn segment_crosses_plane_strict<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    (point_above_plane(d, a, b, c) && point_below_plane(e, a, b, c))
    || (point_below_plane(d, a, b, c) && point_above_plane(e, a, b, c))
}

/// If the segment strictly crosses, d is not on the plane.
pub proof fn lemma_crossing_implies_d_not_on_plane<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures
        !point_on_plane(d, a, b, c),
{
    lemma_orient3d_trichotomy::<T>(a, b, c, d);
}

/// If the segment strictly crosses, e is not on the plane.
pub proof fn lemma_crossing_implies_e_not_on_plane<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures
        !point_on_plane(e, a, b, c),
{
    lemma_orient3d_trichotomy::<T>(a, b, c, e);
}

/// If the segment strictly crosses, d and e have opposite orientation signs.
pub proof fn lemma_crossing_implies_opposite_signs<T: OrderedRing>(
    d: Point3<T>, e: Point3<T>,
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        segment_crosses_plane_strict(d, e, a, b, c),
    ensures
        orient3d_sign(a, b, c, d) != orient3d_sign(a, b, c, e),
        orient3d_sign(a, b, c, d) != OrientationSign::Zero,
        orient3d_sign(a, b, c, e) != OrientationSign::Zero,
{
    lemma_orient3d_sign_matches::<T>(a, b, c, d);
    lemma_orient3d_sign_matches::<T>(a, b, c, e);
    lemma_orient3d_trichotomy::<T>(a, b, c, d);
    lemma_orient3d_trichotomy::<T>(a, b, c, e);
}

} // verus!
