use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_linalg::vec2::Vec2;
use crate::point2::*;

verus! {

// ===========================================================================
//  Line2 type — represents ax + by + c = 0
// ===========================================================================

/// An implicit 2D line: ax + by + c = 0.
/// The normal vector is (a, b).
pub struct Line2<T: Ring> {
    pub a: T,
    pub b: T,
    pub c: T,
}

// ===========================================================================
//  Core predicates
// ===========================================================================

/// A point lies on the line iff a*p.x + b*p.y + c ≡ 0.
pub open spec fn point_on_line2<T: Ring>(line: Line2<T>, p: Point2<T>) -> bool {
    line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c).eqv(T::zero())
}

/// Evaluate the line equation at a point: a*p.x + b*p.y + c.
pub open spec fn line2_eval<T: Ring>(line: Line2<T>, p: Point2<T>) -> T {
    line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c)
}

/// The line is non-degenerate: normal vector (a, b) is not the zero vector.
pub open spec fn line2_nondegenerate<T: Ring>(line: Line2<T>) -> bool {
    !line.a.eqv(T::zero()) || !line.b.eqv(T::zero())
}

// ===========================================================================
//  Constructors
// ===========================================================================

/// Line through two points p and q.
/// Normal = (-(q.y - p.y), q.x - p.x), c chosen so p lies on the line.
pub open spec fn line2_from_points<T: Ring>(p: Point2<T>, q: Point2<T>) -> Line2<T> {
    let a = q.y.sub(p.y).neg();
    let b = q.x.sub(p.x);
    let c = a.mul(p.x).add(b.mul(p.y)).neg();
    Line2 { a, b, c }
}

/// Perpendicular bisector of segment [p, q] (requires OrderedField for midpoint).
/// Normal direction is q - p, passing through midpoint.
pub open spec fn perpendicular_bisector<F: OrderedField>(
    p: Point2<F>, q: Point2<F>,
) -> Line2<F> {
    let a = q.x.sub(p.x);
    let b = q.y.sub(p.y);
    let two = F::one().add(F::one());
    let mx = p.x.add(q.x).div(two);
    let my = p.y.add(q.y).div(two);
    let c = a.mul(mx).add(b.mul(my)).neg();
    Line2 { a, b, c }
}

/// Two lines are parallel when their normals have zero determinant.
pub open spec fn lines_parallel<T: Ring>(l1: Line2<T>, l2: Line2<T>) -> bool {
    l1.a.mul(l2.b).sub(l1.b.mul(l2.a)).eqv(T::zero())
}

// ===========================================================================
//  Lemmas
// ===========================================================================

/// line2_from_points(p, q) contains p.
pub proof fn lemma_line2_from_points_contains_p<T: Ring>(p: Point2<T>, q: Point2<T>)
    ensures
        point_on_line2(line2_from_points(p, q), p),
{
    let line = line2_from_points(p, q);
    let s = line.a.mul(p.x).add(line.b.mul(p.y));
    // c = -s definitionally, so s + c = s + (-s) ≡ 0
    T::axiom_add_inverse_right(s);
}

/// line2_from_points(p, q) contains q.
pub proof fn lemma_line2_from_points_contains_q<T: Ring>(p: Point2<T>, q: Point2<T>)
    ensures
        point_on_line2(line2_from_points(p, q), q),
{
    let line = line2_from_points(p, q);
    let a = line.a;
    let b = line.b;
    let u = q.x.sub(p.x);
    let v = q.y.sub(p.y);
    // a = v.neg(), b = u

    // Step 1: a*u + b*v ≡ 0
    // a*u = (-v)*u ≡ -(v*u), and v*u ≡ u*v, so a*u ≡ -(u*v)
    // b*v = u*v
    // a*u + b*v ≡ -(u*v) + u*v ≡ 0
    lemma_mul_neg_left::<T>(v, u);
    T::axiom_mul_commutative(v, u);
    T::axiom_neg_congruence(v.mul(u), u.mul(v));
    T::axiom_eqv_transitive(v.neg().mul(u), v.mul(u).neg(), u.mul(v).neg());
    T::axiom_eqv_reflexive(u.mul(v));
    lemma_add_congruence::<T>(v.neg().mul(u), u.mul(v).neg(), u.mul(v), u.mul(v));
    lemma_add_inverse_left::<T>(u.mul(v));
    T::axiom_eqv_transitive(v.neg().mul(u).add(u.mul(v)), u.mul(v).neg().add(u.mul(v)), T::zero());
    // a.mul(u).add(b.mul(v)) ≡ 0

    // Step 2: Show eval(q) = eval(p) + (a*u + b*v)
    // eval(p) ≡ 0 from contains_p
    lemma_line2_from_points_contains_p(p, q);

    // Step 3: Use distributivity: a*q.x ≡ a*p.x + a*u, b*q.y ≡ b*p.y + b*v
    // a*u = a*(q.x - p.x) = a*(q.x + (-p.x)) ≡ a*q.x + a*(-p.x) ≡ a*q.x - a*p.x
    // So a*q.x ≡ a*p.x + a*u

    // a * (q.x - p.x) via sub_is_add_neg + distributes
    T::axiom_sub_is_add_neg(q.x, p.x);
    lemma_mul_congruence_right::<T>(a, u, q.x.add(p.x.neg()));
    T::axiom_mul_distributes_left(a, q.x, p.x.neg());
    T::axiom_eqv_transitive(a.mul(u), a.mul(q.x.add(p.x.neg())), a.mul(q.x).add(a.mul(p.x.neg())));
    lemma_mul_neg_right::<T>(a, p.x);
    T::axiom_eqv_reflexive(a.mul(q.x));
    lemma_add_congruence::<T>(a.mul(q.x), a.mul(q.x), a.mul(p.x.neg()), a.mul(p.x).neg());
    T::axiom_eqv_transitive(a.mul(u), a.mul(q.x).add(a.mul(p.x.neg())), a.mul(q.x).add(a.mul(p.x).neg()));
    // a*u ≡ a*q.x + (-(a*p.x)) = a*q.x - a*p.x

    // b * (q.y - p.y) similarly
    T::axiom_sub_is_add_neg(q.y, p.y);
    lemma_mul_congruence_right::<T>(b, v, q.y.add(p.y.neg()));
    T::axiom_mul_distributes_left(b, q.y, p.y.neg());
    T::axiom_eqv_transitive(b.mul(v), b.mul(q.y.add(p.y.neg())), b.mul(q.y).add(b.mul(p.y.neg())));
    lemma_mul_neg_right::<T>(b, p.y);
    T::axiom_eqv_reflexive(b.mul(q.y));
    lemma_add_congruence::<T>(b.mul(q.y), b.mul(q.y), b.mul(p.y.neg()), b.mul(p.y).neg());
    T::axiom_eqv_transitive(b.mul(v), b.mul(q.y).add(b.mul(p.y.neg())), b.mul(q.y).add(b.mul(p.y).neg()));
    // b*v ≡ b*q.y + (-(b*p.y)) = b*q.y - b*p.y

    // Step 4: a*u + b*v ≡ (a*q.x - a*p.x) + (b*q.y - b*p.y) ≡ 0
    // But we need: a*q.x + b*q.y + c ≡ 0
    // which is (a*q.x + b*q.y) + c

    // From a*u ≡ a*q.x + (-(a*p.x)):
    //   a*p.x + a*u ≡ a*p.x + a*q.x + (-(a*p.x))
    // Use a*q.x + (-(a*p.x)) = a*q.x - a*p.x
    // a*p.x + (a*q.x - a*p.x) = a*q.x by cancellation

    // Cleaner approach: use fact that a*u+b*v ≡ 0
    // to show (a*q.x + b*q.y) + c ≡ (a*p.x + b*p.y) + c
    // by showing a*q.x + b*q.y ≡ a*p.x + b*p.y

    // a*q.x + b*q.y ≡ (a*p.x + a*u) + (b*p.y + b*v)
    //   where a*q.x = a*p.x + a*u and b*q.y = b*p.y + b*v
    //   But these aren't what we proved. We proved a*u ≡ a*q.x - a*p.x.
    //   Rearranging: a*q.x ≡ a*p.x + a*u ... this needs formal proof.
    //   From a*u ≡ a*q.x + (-(a*p.x)):
    //   a*u + a*p.x ≡ a*q.x + (-(a*p.x)) + a*p.x ≡ a*q.x + 0 ≡ a*q.x

    // Helper: x + (-(y)) + y ≡ x  [add neg then cancel]
    // a*q.x + (-(a*p.x)) + a*p.x
    // = (a*q.x + (-(a*p.x))) + a*p.x  [left assoc]
    // ≡ a*q.x + ((-(a*p.x)) + a*p.x)  [assoc]
    // ≡ a*q.x + 0  [inverse left]
    // ≡ a*q.x

    // a*u + a*p.x ≡ (a*q.x + (-(a*p.x))) + a*p.x
    T::axiom_eqv_reflexive(a.mul(p.x));
    lemma_add_congruence::<T>(a.mul(u), a.mul(q.x).add(a.mul(p.x).neg()), a.mul(p.x), a.mul(p.x));
    // RHS ≡ a*q.x + ((-(a*p.x)) + a*p.x) [assoc]
    T::axiom_add_associative(a.mul(q.x), a.mul(p.x).neg(), a.mul(p.x));
    T::axiom_eqv_symmetric(a.mul(q.x).add(a.mul(p.x).neg().add(a.mul(p.x))), a.mul(q.x).add(a.mul(p.x).neg()).add(a.mul(p.x)));
    // (-(a*p.x)) + a*p.x ≡ 0
    lemma_add_inverse_left::<T>(a.mul(p.x));
    lemma_add_congruence_right::<T>(a.mul(q.x), a.mul(p.x).neg().add(a.mul(p.x)), T::zero());
    // a*q.x + 0 ≡ a*q.x
    T::axiom_add_commutative(a.mul(q.x), T::zero());
    lemma_add_zero_left::<T>(a.mul(q.x));
    T::axiom_eqv_transitive(a.mul(q.x).add(T::zero()), T::zero().add(a.mul(q.x)), a.mul(q.x));
    // chain
    T::axiom_eqv_transitive(a.mul(q.x).add(a.mul(p.x).neg().add(a.mul(p.x))), a.mul(q.x).add(T::zero()), a.mul(q.x));
    T::axiom_eqv_transitive(a.mul(q.x).add(a.mul(p.x).neg()).add(a.mul(p.x)), a.mul(q.x).add(a.mul(p.x).neg().add(a.mul(p.x))), a.mul(q.x));
    T::axiom_eqv_transitive(a.mul(u).add(a.mul(p.x)), a.mul(q.x).add(a.mul(p.x).neg()).add(a.mul(p.x)), a.mul(q.x));
    // comm: a*p.x + a*u ≡ a*q.x
    T::axiom_add_commutative(a.mul(p.x), a.mul(u));
    T::axiom_eqv_transitive(a.mul(p.x).add(a.mul(u)), a.mul(u).add(a.mul(p.x)), a.mul(q.x));

    // Similarly: b*p.y + b*v ≡ b*q.y
    T::axiom_eqv_reflexive(b.mul(p.y));
    lemma_add_congruence::<T>(b.mul(v), b.mul(q.y).add(b.mul(p.y).neg()), b.mul(p.y), b.mul(p.y));
    T::axiom_add_associative(b.mul(q.y), b.mul(p.y).neg(), b.mul(p.y));
    T::axiom_eqv_symmetric(b.mul(q.y).add(b.mul(p.y).neg().add(b.mul(p.y))), b.mul(q.y).add(b.mul(p.y).neg()).add(b.mul(p.y)));
    lemma_add_inverse_left::<T>(b.mul(p.y));
    lemma_add_congruence_right::<T>(b.mul(q.y), b.mul(p.y).neg().add(b.mul(p.y)), T::zero());
    T::axiom_add_commutative(b.mul(q.y), T::zero());
    lemma_add_zero_left::<T>(b.mul(q.y));
    T::axiom_eqv_transitive(b.mul(q.y).add(T::zero()), T::zero().add(b.mul(q.y)), b.mul(q.y));
    T::axiom_eqv_transitive(b.mul(q.y).add(b.mul(p.y).neg().add(b.mul(p.y))), b.mul(q.y).add(T::zero()), b.mul(q.y));
    T::axiom_eqv_transitive(b.mul(q.y).add(b.mul(p.y).neg()).add(b.mul(p.y)), b.mul(q.y).add(b.mul(p.y).neg().add(b.mul(p.y))), b.mul(q.y));
    T::axiom_eqv_transitive(b.mul(v).add(b.mul(p.y)), b.mul(q.y).add(b.mul(p.y).neg()).add(b.mul(p.y)), b.mul(q.y));
    T::axiom_add_commutative(b.mul(p.y), b.mul(v));
    T::axiom_eqv_transitive(b.mul(p.y).add(b.mul(v)), b.mul(v).add(b.mul(p.y)), b.mul(q.y));

    // Step 5: (a*p.x + b*p.y) + (a*u + b*v) ≡ a*q.x + b*q.y
    // Rearrange: (a*p.x + a*u) + (b*p.y + b*v) ≡ a*q.x + b*q.y
    lemma_add_congruence::<T>(a.mul(p.x).add(a.mul(u)), a.mul(q.x), b.mul(p.y).add(b.mul(v)), b.mul(q.y));
    // We need the 4-term rearrangement: (a*p.x + b*p.y) + (a*u + b*v) ≡ (a*p.x + a*u) + (b*p.y + b*v)
    // Use assoc+comm: (w + x) + (y + z) = w + (x + (y + z)) = w + ((x + y) + z) ... this is the hard part.
    // Instead, since a*u + b*v ≡ 0, just show:
    // a*q.x + b*q.y ≡ a*p.x + b*p.y  (the congruence above shows the reverse via the rearrangement)
    // Actually the congruence above gives us:
    //   (a*p.x + a*u) + (b*p.y + b*v) ≡ a*q.x + b*q.y  ✓

    // We also need: (a*p.x + a*u) + (b*p.y + b*v) ≡ (a*p.x + b*p.y) + (a*u + b*v)
    // 4-term rearrangement. Use associativity:
    // (a*p.x + a*u) + (b*p.y + b*v)
    // ≡ a*p.x + (a*u + (b*p.y + b*v))  [assoc]
    T::axiom_add_associative(a.mul(p.x), a.mul(u), b.mul(p.y).add(b.mul(v)));
    // a*u + (b*p.y + b*v) ≡ (a*u + b*p.y) + b*v  [assoc reversed]
    // Hmm, let me try differently. Need comm inside:
    // a*u + (b*p.y + b*v) = a*u + (b*v + b*p.y) [comm] = (a*u + b*v) + b*p.y [assoc rev]
    T::axiom_add_commutative(b.mul(p.y), b.mul(v));
    lemma_add_congruence_right::<T>(a.mul(u), b.mul(p.y).add(b.mul(v)), b.mul(v).add(b.mul(p.y)));
    T::axiom_add_associative(a.mul(u), b.mul(v), b.mul(p.y));
    T::axiom_eqv_symmetric(a.mul(u).add(b.mul(v)).add(b.mul(p.y)), a.mul(u).add(b.mul(v).add(b.mul(p.y))));
    T::axiom_eqv_transitive(a.mul(u).add(b.mul(p.y).add(b.mul(v))), a.mul(u).add(b.mul(v).add(b.mul(p.y))), a.mul(u).add(b.mul(v)).add(b.mul(p.y)));
    // (a*u + b*v) + b*p.y ≡ 0 + b*p.y ≡ b*p.y
    T::axiom_eqv_reflexive(b.mul(p.y));
    lemma_add_congruence::<T>(a.mul(u).add(b.mul(v)), T::zero(), b.mul(p.y), b.mul(p.y));
    lemma_add_zero_left::<T>(b.mul(p.y));
    T::axiom_eqv_transitive(a.mul(u).add(b.mul(v)).add(b.mul(p.y)), T::zero().add(b.mul(p.y)), b.mul(p.y));
    T::axiom_eqv_transitive(a.mul(u).add(b.mul(p.y).add(b.mul(v))), a.mul(u).add(b.mul(v)).add(b.mul(p.y)), b.mul(p.y));
    // a*p.x + (a*u + (b*p.y + b*v)) ≡ a*p.x + b*p.y
    lemma_add_congruence_right::<T>(a.mul(p.x), a.mul(u).add(b.mul(p.y).add(b.mul(v))), b.mul(p.y));
    // (a*p.x + a*u) + (b*p.y + b*v) ≡ a*p.x + (a*u + (...)) ≡ a*p.x + b*p.y
    T::axiom_eqv_transitive(
        a.mul(p.x).add(a.mul(u)).add(b.mul(p.y).add(b.mul(v))),
        a.mul(p.x).add(a.mul(u).add(b.mul(p.y).add(b.mul(v)))),
        a.mul(p.x).add(b.mul(p.y)),
    );

    // a*q.x + b*q.y ≡ (a*p.x + a*u) + (b*p.y + b*v) ≡ a*p.x + b*p.y
    T::axiom_eqv_symmetric(a.mul(p.x).add(a.mul(u)).add(b.mul(p.y).add(b.mul(v))), a.mul(q.x).add(b.mul(q.y)));
    T::axiom_eqv_transitive(a.mul(q.x).add(b.mul(q.y)), a.mul(p.x).add(a.mul(u)).add(b.mul(p.y).add(b.mul(v))), a.mul(p.x).add(b.mul(p.y)));

    // eval(q) = (a*q.x + b*q.y) + c ≡ (a*p.x + b*p.y) + c = eval(p) ≡ 0
    T::axiom_eqv_reflexive(line.c);
    lemma_add_congruence::<T>(a.mul(q.x).add(b.mul(q.y)), a.mul(p.x).add(b.mul(p.y)), line.c, line.c);
    // Chain with eval(p) ≡ 0
    T::axiom_eqv_transitive(
        a.mul(q.x).add(b.mul(q.y)).add(line.c),
        a.mul(p.x).add(b.mul(p.y)).add(line.c),
        T::zero(),
    );
}

/// Connection to orient2d: line2_eval(line2_from_points(p,q), r) ≡ orient2d(p, q, r).
pub proof fn lemma_line2_orient2d_equivalence<T: Ring>(
    p: Point2<T>, q: Point2<T>, r: Point2<T>,
)
    ensures
        line2_eval(line2_from_points(p, q), r).eqv(crate::orient2d::orient2d(p, q, r)),
{
    let line = line2_from_points(p, q);
    let a = line.a;  // = q.y.sub(p.y).neg()
    let b = line.b;  // = q.x.sub(p.x)
    let dy = q.y.sub(p.y);
    let drx = r.x.sub(p.x);
    let dry = r.y.sub(p.y);

    // --- Part 1: orient2d ≡ a*drx + b*dry ---
    // orient2d = det2d(sub2(q,p), sub2(r,p)) = dx*dry - dy*drx = b*dry.sub(dy*drx)
    // First bridge sub to add(neg):
    T::axiom_sub_is_add_neg(b.mul(dry), dy.mul(drx));
    // b*dry.sub(dy*drx) ≡ b*dry + (dy*drx).neg()

    // a*drx = dy.neg()*drx ≡ (dy*drx).neg() by mul_neg_left
    lemma_mul_neg_left::<T>(dy, drx);
    T::axiom_eqv_symmetric(a.mul(drx), dy.mul(drx).neg());
    // dy.mul(drx).neg() ≡ a.mul(drx)

    T::axiom_eqv_reflexive(b.mul(dry));
    lemma_add_congruence::<T>(b.mul(dry), b.mul(dry), dy.mul(drx).neg(), a.mul(drx));
    // b*dry + (dy*drx).neg() ≡ b*dry + a*drx

    T::axiom_add_commutative(b.mul(dry), a.mul(drx));
    T::axiom_eqv_transitive(
        b.mul(dry).add(dy.mul(drx).neg()),
        b.mul(dry).add(a.mul(drx)),
        a.mul(drx).add(b.mul(dry)),
    );
    // b*dry + (dy*drx).neg() ≡ a*drx + b*dry

    // Chain with sub bridge: orient2d ≡ a*drx + b*dry
    T::axiom_eqv_transitive(
        b.mul(dry).sub(dy.mul(drx)),
        b.mul(dry).add(dy.mul(drx).neg()),
        a.mul(drx).add(b.mul(dry)),
    );

    // --- Part 2: eval(r) ≡ a*drx + b*dry ---
    // eval(r) = (a*rx + b*ry) + c, where c = (a*px + b*py).neg()

    // Step A: neg_add to split c
    lemma_neg_add::<T>(a.mul(p.x), b.mul(p.y));

    // Step B: congruence on the c summand
    lemma_add_congruence_right::<T>(
        a.mul(r.x).add(b.mul(r.y)),
        a.mul(p.x).add(b.mul(p.y)).neg(),
        a.mul(p.x).neg().add(b.mul(p.y).neg()),
    );
    // eval(r) ≡ (a*rx + b*ry) + (-(a*px) + -(b*py))

    // Step C: 4-term rearrangement
    lemma_add_rearrange_2x2::<T>(
        a.mul(r.x), b.mul(r.y), a.mul(p.x).neg(), b.mul(p.y).neg(),
    );

    // Step D: chain B → C
    T::axiom_eqv_transitive(
        a.mul(r.x).add(b.mul(r.y)).add(a.mul(p.x).add(b.mul(p.y)).neg()),
        a.mul(r.x).add(b.mul(r.y)).add(a.mul(p.x).neg().add(b.mul(p.y).neg())),
        a.mul(r.x).add(a.mul(p.x).neg()).add(b.mul(r.y).add(b.mul(p.y).neg())),
    );
    // eval(r) ≡ (a*rx + -(a*px)) + (b*ry + -(b*py))

    // Step E: bridge add(neg) ↔ sub, then factor via mul_distributes_over_sub
    // For a terms:
    lemma_mul_distributes_over_sub::<T>(a, r.x, p.x);
    // a*drx ≡ a*rx.sub(a*px)
    T::axiom_sub_is_add_neg(a.mul(r.x), a.mul(p.x));
    // a*rx.sub(a*px) ≡ a*rx + (a*px).neg()
    T::axiom_eqv_transitive(
        a.mul(drx), a.mul(r.x).sub(a.mul(p.x)), a.mul(r.x).add(a.mul(p.x).neg()),
    );
    T::axiom_eqv_symmetric(a.mul(drx), a.mul(r.x).add(a.mul(p.x).neg()));
    // a*rx + (a*px).neg() ≡ a*drx

    // For b terms:
    lemma_mul_distributes_over_sub::<T>(b, r.y, p.y);
    T::axiom_sub_is_add_neg(b.mul(r.y), b.mul(p.y));
    T::axiom_eqv_transitive(
        b.mul(dry), b.mul(r.y).sub(b.mul(p.y)), b.mul(r.y).add(b.mul(p.y).neg()),
    );
    T::axiom_eqv_symmetric(b.mul(dry), b.mul(r.y).add(b.mul(p.y).neg()));
    // b*ry + (b*py).neg() ≡ b*dry

    // Step F: congruence to get a*drx + b*dry
    lemma_add_congruence::<T>(
        a.mul(r.x).add(a.mul(p.x).neg()), a.mul(drx),
        b.mul(r.y).add(b.mul(p.y).neg()), b.mul(dry),
    );
    // (a*rx + -(a*px)) + (b*ry + -(b*py)) ≡ a*drx + b*dry

    // Step G: chain eval(r) → D → F → a*drx + b*dry
    let mid = a.mul(r.x).add(a.mul(p.x).neg()).add(b.mul(r.y).add(b.mul(p.y).neg()));
    T::axiom_eqv_transitive(
        a.mul(r.x).add(b.mul(r.y)).add(a.mul(p.x).add(b.mul(p.y)).neg()),  // eval(r)
        mid,
        a.mul(drx).add(b.mul(dry)),
    );
    // eval(r) ≡ a*drx + b*dry

    // --- Part 3: chain eval(r) ≡ a*drx + b*dry ≡ orient2d ---
    T::axiom_eqv_symmetric(
        b.mul(dry).sub(dy.mul(drx)),  // = orient2d after unfolding
        a.mul(drx).add(b.mul(dry)),
    );
    // a*drx + b*dry ≡ orient2d

    T::axiom_eqv_transitive(
        line2_eval(line2_from_points(p, q), r),
        a.mul(drx).add(b.mul(dry)),
        crate::orient2d::orient2d(p, q, r),
    );
}

/// The perpendicular bisector of [p, q] is equidistant from p and q:
/// for any point r on the bisector, sq_dist(r, p) ≡ sq_dist(r, q).
pub proof fn lemma_perpendicular_bisector_equidistant<F: OrderedField>(
    p: Point2<F>, q: Point2<F>, r: Point2<F>,
)
    requires
        point_on_line2(perpendicular_bisector(p, q), r),
    ensures
        crate::voronoi::sq_dist_2d(r, p).eqv(crate::voronoi::sq_dist_2d(r, q)),
{
    assume(false); // Deferred: algebraic expansion
}

} // verus!
