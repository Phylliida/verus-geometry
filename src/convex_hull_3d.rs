use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point3::*;
use crate::orient3d::*;
use crate::orientation_sign::*;
use crate::sidedness::*;

verus! {

// =========================================================================
// Spec functions
// =========================================================================

/// All points in `points` are on or below the oriented plane (a, b, c).
/// "Below" means orient3d(a, b, c, p) ≤ 0 (non-positive).
pub open spec fn all_points_on_or_below_plane<T: OrderedRing>(
    points: Seq<Point3<T>>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    forall|i: int| 0 <= i < points.len() ==> !orient3d_positive(a, b, c, #[trigger] points[i])
}

/// Triangle (points[a_idx], points[b_idx], points[c_idx]) is a convex hull face:
/// all points are on the non-positive side of the oriented plane.
pub open spec fn is_convex_hull_face<T: OrderedRing>(
    points: Seq<Point3<T>>, a_idx: int, b_idx: int, c_idx: int,
) -> bool {
    &&& 0 <= a_idx < points.len()
    &&& 0 <= b_idx < points.len()
    &&& 0 <= c_idx < points.len()
    &&& all_points_on_or_below_plane(points, points[a_idx], points[b_idx], points[c_idx])
}

/// Point p is visible from face (a, b, c) — on the strictly positive side.
pub open spec fn point_visible_from_face<T: OrderedRing>(
    p: Point3<T>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
) -> bool {
    orient3d_positive(a, b, c, p)
}

/// A set of face triples forms a convex hull of the given points.
pub open spec fn is_point_set_convex_hull<T: OrderedRing>(
    face_triples: Seq<(int, int, int)>, points: Seq<Point3<T>>,
) -> bool {
    forall|i: int| 0 <= i < face_triples.len() ==> {
        let (a, b, c) = #[trigger] face_triples[i];
        is_convex_hull_face(points, a, b, c)
    }
}

// =========================================================================
// Proof lemmas
// =========================================================================

/// A hull face vertex is on its own plane (orient3d degenerate).
pub proof fn lemma_vertex_on_hull_face<T: Ring>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        orient3d(a, b, c, a).eqv(T::zero()),
{
    // orient3d(a, b, c, a) has d=a, which gives sub3(a,a) = zero vec → determinant 0
    crate::orient3d::lemma_orient3d_degenerate_da::<T>(a, b, c);
}

/// Swapping b and c on a hull face reverses orientation: if all points are on the
/// non-positive side of (a,b,c), they are on the non-negative side of (a,c,b).
pub proof fn lemma_opposite_face_orientation<T: OrderedRing>(
    points: Seq<Point3<T>>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    requires
        all_points_on_or_below_plane(points, a, b, c),
    ensures
        forall|i: int| 0 <= i < points.len() ==>
            !orient3d_negative(a, c, b, #[trigger] points[i]),
{
    assert forall|i: int| 0 <= i < points.len() implies
        !orient3d_negative(a, c, b, #[trigger] points[i])
    by {
        // !orient3d_positive(a,b,c, p[i])
        // orient3d(a,c,b,d) ≡ -orient3d(a,b,c,d) by swap_bc
        lemma_orient3d_swap_bc::<T>(a, b, c, points[i]);
        crate::orientation_sign::lemma_neg_flips_sign::<T>(
            orient3d(a, c, b, points[i]), orient3d(a, b, c, points[i]),
        );
        // orient3d_positive(a,b,c,p) ↔ orient3d_negative(a,c,b,p)
    }
}

/// Convex hull face predicate is translation-invariant.
pub proof fn lemma_convex_hull_face_translation<T: OrderedRing>(
    points: Seq<Point3<T>>, a: Point3<T>, b: Point3<T>, c: Point3<T>,
    t: verus_linalg::vec3::Vec3<T>,
)
    requires
        all_points_on_or_below_plane(points, a, b, c),
    ensures
        all_points_on_or_below_plane(
            Seq::new(points.len(), |i: int| crate::point3::add_vec3(points[i], t)),
            crate::point3::add_vec3(a, t),
            crate::point3::add_vec3(b, t),
            crate::point3::add_vec3(c, t),
        ),
{
    let at = crate::point3::add_vec3(a, t);
    let bt = crate::point3::add_vec3(b, t);
    let ct = crate::point3::add_vec3(c, t);
    let translated = Seq::new(points.len(), |i: int| crate::point3::add_vec3(points[i], t));

    assert forall|i: int| 0 <= i < translated.len() implies
        !orient3d_positive(at, bt, ct, #[trigger] translated[i])
    by {
        let pt = crate::point3::add_vec3(points[i], t);
        assert(translated[i] == pt);
        lemma_orient3d_translation::<T>(a, b, c, points[i], t);
        // orient3d(at,bt,ct,pt) ≡ orient3d(a,b,c,p[i])
        crate::orientation_sign::lemma_scalar_sign_congruence::<T>(
            orient3d(at, bt, ct, pt),
            orient3d(a, b, c, points[i]),
        );
    }
}

} // verus!
