use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::point2::*;
use crate::orient2d::*;
use crate::convex_polygon::polygon_next_index;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// Winding contribution of a single directed edge (p0→p1) with respect to
/// query point q, using the standard crossing-number rule:
///
///   +1  if p0.y ≤ q.y < p1.y  AND  orient2d(p0, p1, q) > 0   (upward left-crossing)
///   -1  if p1.y ≤ q.y < p0.y  AND  orient2d(p0, p1, q) < 0   (downward right-crossing)
///    0  otherwise
pub open spec fn winding_edge<T: OrderedRing>(
    q: Point2<T>, p0: Point2<T>, p1: Point2<T>,
) -> int {
    let o = orient2d(p0, p1, q);
    if p0.y.le(q.y) && q.y.lt(p1.y) && T::zero().lt(o) {
        1int
    } else if p1.y.le(q.y) && q.y.lt(p0.y) && o.lt(T::zero()) {
        -1int
    } else {
        0int
    }
}

/// Recursive prefix sum of winding contributions for edges [0, k).
pub open spec fn winding_number_prefix<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
) -> int
    recommends
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        let i = k - 1;
        let j = polygon_next_index(polygon.len() as int, i);
        winding_number_prefix(q, polygon, i)
            + winding_edge(q, polygon[i], polygon[j])
    }
}

/// Winding number of query point q with respect to polygon.
pub open spec fn winding_number<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> int
    recommends polygon.len() >= 3,
{
    winding_number_prefix(q, polygon, polygon.len() as int)
}

/// Point is inside polygon (nonzero winding number).
pub open spec fn point_in_polygon<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    winding_number(q, polygon) != 0int
}

/// Point is outside polygon (zero winding number).
pub open spec fn point_outside_polygon<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
) -> bool
    recommends polygon.len() >= 3,
{
    winding_number(q, polygon) == 0int
}

// ---------------------------------------------------------------------------
// Prefix unfold lemma
// ---------------------------------------------------------------------------

/// Adding one more edge contribution to the winding prefix sum.
pub proof fn lemma_winding_prefix_unfold<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 < k <= polygon.len(),
    ensures
        winding_number_prefix(q, polygon, k) ==
            winding_number_prefix(q, polygon, k - 1)
                + winding_edge(
                    q,
                    polygon[k - 1],
                    polygon[polygon_next_index(polygon.len() as int, k - 1)]
                ),
{
    // Direct from definition
}

// ---------------------------------------------------------------------------
// Cyclic shift
// ---------------------------------------------------------------------------

/// Cyclic shift of polygon vertices by 1: shift[i] = poly[next(i)].
pub open spec fn shift_polygon_1<T: OrderedRing>(poly: Seq<Point2<T>>) -> Seq<Point2<T>>
    recommends poly.len() >= 3,
{
    let n = poly.len() as int;
    Seq::new(poly.len(), |i: int| poly[polygon_next_index(n, i)])
}

/// Helper: for 0 ≤ k ≤ n-1, shifted prefix = original prefix shifted by 1 minus first edge.
proof fn lemma_winding_cyclic_shift_1_prefix<T: OrderedRing>(
    q: Point2<T>, poly: Seq<Point2<T>>, k: int,
)
    requires
        poly.len() >= 3,
        0 <= k <= poly.len() - 1,
    ensures
        winding_number_prefix(q, shift_polygon_1(poly), k) ==
            winding_number_prefix(q, poly, k + 1)
                - winding_edge(q, poly[0],
                    poly[polygon_next_index(poly.len() as int, 0)]),
    decreases k,
{
    let n = poly.len() as int;
    let shift = shift_polygon_1(poly);
    let e0 = winding_edge(q, poly[0], poly[polygon_next_index(n, 0)]);

    if k == 0 {
        // LHS: winding_number_prefix(q, shift, 0) == 0
        assert(winding_number_prefix(q, shift, 0) == 0int);
        // RHS: winding_number_prefix(q, poly, 1) - e0
        //     = (winding_number_prefix(q, poly, 0) + e0) - e0 = 0
        assert(winding_number_prefix(q, poly, 0) == 0int);
        assert(polygon_next_index(n, 0) == (if n > 1 { 1int } else { 0int }));
        assert(winding_number_prefix(q, poly, 1)
            == winding_number_prefix(q, poly, 0)
                + winding_edge(q, poly[0], poly[polygon_next_index(n, 0)]));
        assert(winding_number_prefix(q, poly, 1) == e0);
    } else {
        lemma_winding_cyclic_shift_1_prefix::<T>(q, poly, k - 1);

        let idx = k - 1;
        assert(shift.len() == poly.len());
        assert(0 <= idx && idx < shift.len());
        assert(0 <= k && k < shift.len());

        // polygon_next_index(n, idx) = k because idx = k-1 and k <= n-1 means idx < n-1
        assert(polygon_next_index(n, idx) == k);

        // Seq::new: shift[i] = poly[next(i)]
        assert(shift[idx] == poly[polygon_next_index(n, idx)]);
        assert(shift[idx] == poly[k]);
        let next_k = polygon_next_index(n, k);
        assert(0 <= next_k && next_k < poly.len());
        assert(shift[k] == poly[next_k]);

        // The shifted edge at idx = original edge at k
        let ek = winding_edge(q, poly[k], poly[next_k]);
        assert(winding_edge(q, shift[idx], shift[k]) == ek);

        // Shifted prefix unfolds
        assert(polygon_next_index(shift.len() as int, idx) == k);
        assert(winding_number_prefix(q, shift, k)
            == winding_number_prefix(q, shift, idx) + winding_edge(q, shift[idx], shift[k]));

        // By IH: shifted_prefix(idx) = original_prefix(k) - e0
        // So: shifted_prefix(k) = (original_prefix(k) - e0) + ek
        assert(winding_number_prefix(q, shift, k)
            == (winding_number_prefix(q, poly, k) - e0) + ek);

        // original_prefix(k+1) = original_prefix(k) + ek
        assert(winding_number_prefix(q, poly, k + 1)
            == winding_number_prefix(q, poly, k) + ek);
    }
}

/// Winding number is invariant under cyclic shift by 1.
pub proof fn lemma_winding_cyclic_shift_1<T: OrderedRing>(
    q: Point2<T>, poly: Seq<Point2<T>>,
)
    requires
        poly.len() >= 3,
    ensures
        winding_number(q, shift_polygon_1(poly)) == winding_number(q, poly),
{
    let n = poly.len() as int;
    let shift = shift_polygon_1(poly);
    let e0 = winding_edge(q, poly[0], poly[polygon_next_index(n, 0)]);

    // shifted_prefix(n-1) == original_prefix(n) - e0
    lemma_winding_cyclic_shift_1_prefix::<T>(q, poly, n - 1);

    // The last shifted edge: (shift[n-1], shift[0]) = (poly[0], poly[1]) = e0
    assert(shift[n - 1] == poly[polygon_next_index(n, n - 1)]);
    assert(polygon_next_index(n, n - 1) == 0);
    assert(shift[0] == poly[polygon_next_index(n, 0)]);

    // shifted_prefix(n) = shifted_prefix(n-1) + e0 = (original_prefix(n) - e0) + e0
}

// ---------------------------------------------------------------------------
// Winding-zero lemmas: y out of range
// ---------------------------------------------------------------------------

/// Helper: winding prefix is zero when all vertices are at or below query y.
proof fn lemma_winding_prefix_zero_above<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
        forall |i: int| 0 <= i < polygon.len() ==> polygon[i].y.le(q.y),
    ensures
        winding_number_prefix(q, polygon, k) == 0,
    decreases k,
{
    if k > 0 {
        lemma_winding_prefix_zero_above::<T>(q, polygon, k - 1);
        let idx = k - 1;
        let j = polygon_next_index(polygon.len() as int, idx);
        assert(0 <= j < polygon.len() as int);
        let p0 = polygon[idx];
        let p1 = polygon[j];
        // p0.y.le(q.y) and p1.y.le(q.y) from the quantifier
        // Need: !q.y.lt(p0.y) and !q.y.lt(p1.y) to make both branches 0
        T::axiom_lt_iff_le_and_not_eqv(q.y, p0.y);
        T::axiom_lt_iff_le_and_not_eqv(q.y, p1.y);
        if q.y.le(p0.y) {
            T::axiom_le_antisymmetric(p0.y, q.y);
            T::axiom_eqv_symmetric(p0.y, q.y);
        }
        if q.y.le(p1.y) {
            T::axiom_le_antisymmetric(p1.y, q.y);
            T::axiom_eqv_symmetric(p1.y, q.y);
        }
    }
}

/// If query point is at or above all polygon vertices (y-wise), winding number is 0.
pub proof fn lemma_winding_zero_above<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
)
    requires
        polygon.len() >= 3,
        forall |i: int| 0 <= i < polygon.len() ==> polygon[i].y.le(q.y),
    ensures
        winding_number(q, polygon) == 0,
{
    lemma_winding_prefix_zero_above::<T>(q, polygon, polygon.len() as int);
}

/// Helper: winding prefix is zero when query y is strictly below all vertices.
proof fn lemma_winding_prefix_zero_below<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
        forall |i: int| 0 <= i < polygon.len() ==> q.y.lt(polygon[i].y),
    ensures
        winding_number_prefix(q, polygon, k) == 0,
    decreases k,
{
    if k > 0 {
        lemma_winding_prefix_zero_below::<T>(q, polygon, k - 1);
        let idx = k - 1;
        let j = polygon_next_index(polygon.len() as int, idx);
        assert(0 <= j < polygon.len() as int);
        let p0 = polygon[idx];
        let p1 = polygon[j];
        // q.y.lt(p0.y) and q.y.lt(p1.y) from the quantifier
        // Need: !p0.y.le(q.y) and !p1.y.le(q.y)
        T::axiom_lt_iff_le_and_not_eqv(q.y, p0.y);
        T::axiom_lt_iff_le_and_not_eqv(q.y, p1.y);
        if p0.y.le(q.y) {
            T::axiom_le_antisymmetric(q.y, p0.y);
            // q.y.eqv(p0.y), but q.y.lt(p0.y) requires !q.y.eqv(p0.y) — contradiction
        }
        if p1.y.le(q.y) {
            T::axiom_le_antisymmetric(q.y, p1.y);
        }
    }
}

/// If query point is strictly below all polygon vertices (y-wise), winding number is 0.
pub proof fn lemma_winding_zero_below<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
)
    requires
        polygon.len() >= 3,
        forall |i: int| 0 <= i < polygon.len() ==> q.y.lt(polygon[i].y),
    ensures
        winding_number(q, polygon) == 0,
{
    lemma_winding_prefix_zero_below::<T>(q, polygon, polygon.len() as int);
}

// ---------------------------------------------------------------------------
// Winding number bounded
// ---------------------------------------------------------------------------

/// Each edge contributes -1, 0, or +1 to the winding number.
pub proof fn lemma_winding_edge_bounded<T: OrderedRing>(
    q: Point2<T>, p0: Point2<T>, p1: Point2<T>,
)
    ensures
        -1 <= winding_edge(q, p0, p1) <= 1,
{
    // Direct from definition (three branches: 1, -1, 0)
}

/// The winding prefix sum is bounded: |prefix(k)| ≤ k.
proof fn lemma_winding_prefix_bounded<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>, k: int,
)
    requires
        polygon.len() >= 3,
        0 <= k <= polygon.len(),
    ensures
        -k <= winding_number_prefix(q, polygon, k) <= k,
    decreases k,
{
    if k > 0 {
        lemma_winding_prefix_bounded::<T>(q, polygon, k - 1);
        let idx = k - 1;
        let j = polygon_next_index(polygon.len() as int, idx);
        lemma_winding_edge_bounded::<T>(q, polygon[idx], polygon[j]);
    }
}

/// The winding number is bounded by the number of polygon edges.
pub proof fn lemma_winding_number_bounded<T: OrderedRing>(
    q: Point2<T>, polygon: Seq<Point2<T>>,
)
    requires
        polygon.len() >= 3,
    ensures
        -(polygon.len() as int) <= winding_number(q, polygon) <= (polygon.len() as int),
{
    lemma_winding_prefix_bounded::<T>(q, polygon, polygon.len() as int);
}

} // verus!
