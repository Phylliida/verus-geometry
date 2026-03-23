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

/// Reflect a point across the line through `line_a` and `line_b`.
/// Formula: p' = 2 * proj(p, line) - p, where proj is the orthogonal projection
/// of p onto the line through (line_a, line_b).
pub open spec fn reflect_point_across_line<F: OrderedField>(
    p: Point2<F>, line_a: Point2<F>, line_b: Point2<F>,
) -> Point2<F> {
    let d = sub2(line_b, line_a);
    let pa = sub2(p, line_a);
    let dot_dd = d.x.mul(d.x).add(d.y.mul(d.y));
    let dot_pad = pa.x.mul(d.x).add(pa.y.mul(d.y));
    let t = dot_pad.div(dot_dd);
    let two = F::one().add(F::one());
    let proj_x = line_a.x.add(t.mul(d.x));
    let proj_y = line_a.y.add(t.mul(d.y));
    Point2 {
        x: two.mul(proj_x).sub(p.x),
        y: two.mul(proj_y).sub(p.y),
    }
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
    use verus_algebra::convex::{two, lemma_two_nonzero};
    use verus_algebra::lemmas::field_lemmas::lemma_div_mul_cancel;

    // Setup
    let a = q.x.sub(p.x);
    let b = q.y.sub(p.y);
    let two_val = two::<F>();
    let mx = p.x.add(q.x).div(two_val);
    let my = p.y.add(q.y).div(two_val);
    let M = a.mul(mx).add(b.mul(my));
    let S = a.mul(r.x).add(b.mul(r.y));

    // Extract line condition: S ≡ M
    // point_on_line2 gives S.add(M.neg()) ≡ 0, bridge to S.sub(M) ≡ 0
    F::axiom_sub_is_add_neg(S, M);
    F::axiom_eqv_transitive(S.sub(M), S.add(M.neg()), F::zero());
    crate::collinearity::lemma_sub_zero_implies_eqv(S, M);

    // Squared-distance components
    let xp_sq = r.x.sub(p.x).mul(r.x.sub(p.x));
    let yp_sq = r.y.sub(p.y).mul(r.y.sub(p.y));
    let xq_sq = r.x.sub(q.x).mul(r.x.sub(q.x));
    let yq_sq = r.y.sub(q.y).mul(r.y.sub(q.y));
    let dist_p = xp_sq.add(yp_sq);  // = sq_dist_2d(r, p)
    let dist_q = xq_sq.add(yq_sq);  // = sq_dist_2d(r, q)
    let px_sq = p.x.mul(p.x);
    let qx_sq = q.x.mul(q.x);
    let py_sq = p.y.mul(p.y);
    let qy_sq = q.y.mul(q.y);
    let norm_sq_q = qx_sq.add(qy_sq);
    let norm_sq_p = px_sq.add(py_sq);
    let T1 = two_val.mul(a).mul(r.x);
    let D1 = px_sq.sub(qx_sq);
    let T2 = two_val.mul(b).mul(r.y);
    let D2 = py_sq.sub(qy_sq);

    // Step 1: dist_p - dist_q ≡ (xp_sq - xq_sq) + (yp_sq - yq_sq)
    crate::circle_circle_proofs::lemma_sum_sub_rearrange(xp_sq, yp_sq, xq_sq, yq_sq);

    // Step 2: Apply sq_diff to each coordinate
    crate::circle_circle_proofs::lemma_sq_diff(r.x, p.x, q.x);
    crate::circle_circle_proofs::lemma_sq_diff(r.y, p.y, q.y);
    lemma_add_congruence::<F>(
        xp_sq.sub(xq_sq), T1.add(D1),
        yp_sq.sub(yq_sq), T2.add(D2),
    );

    // Step 3: Rearrange (T1+D1)+(T2+D2) ≡ (T1+T2)+(D1+D2)
    lemma_add_rearrange_2x2::<F>(T1, D1, T2, D2);

    // Chain: dist_p - dist_q ≡ (T1+T2)+(D1+D2)
    F::axiom_eqv_transitive(
        dist_p.sub(dist_q),
        xp_sq.sub(xq_sq).add(yp_sq.sub(yq_sq)),
        T1.add(D1).add(T2.add(D2)),
    );
    F::axiom_eqv_transitive(
        dist_p.sub(dist_q),
        T1.add(D1).add(T2.add(D2)),
        T1.add(T2).add(D1.add(D2)),
    );

    // Step 4: Factor T1+T2 ≡ two*S
    F::axiom_mul_associative(two_val, a, r.x);
    F::axiom_mul_associative(two_val, b, r.y);
    lemma_add_congruence::<F>(
        T1, two_val.mul(a.mul(r.x)),
        T2, two_val.mul(b.mul(r.y)),
    );
    F::axiom_mul_distributes_left(two_val, a.mul(r.x), b.mul(r.y));
    F::axiom_eqv_symmetric(
        two_val.mul(a.mul(r.x).add(b.mul(r.y))),
        two_val.mul(a.mul(r.x)).add(two_val.mul(b.mul(r.y))),
    );
    F::axiom_eqv_transitive(
        T1.add(T2),
        two_val.mul(a.mul(r.x)).add(two_val.mul(b.mul(r.y))),
        two_val.mul(S),
    );

    // Step 5: two*S ≡ two*M (from line condition S ≡ M)
    lemma_mul_congruence_right::<F>(two_val, S, M);
    F::axiom_eqv_transitive(T1.add(T2), two_val.mul(S), two_val.mul(M));

    // Step 6: two*M ≡ a*(p.x+q.x) + b*(p.y+q.y) [clear midpoint division]
    F::axiom_mul_distributes_left(two_val, a.mul(mx), b.mul(my));
    lemma_two_nonzero::<F>();

    // Clear x: two*(a*mx) ≡ a*(p.x+q.x)
    crate::line_intersection::lemma_mul_div_assoc(a, p.x.add(q.x), two_val);
    lemma_mul_congruence_right::<F>(two_val, a.mul(mx), a.mul(p.x.add(q.x)).div(two_val));
    F::axiom_mul_commutative(two_val, a.mul(p.x.add(q.x)).div(two_val));
    lemma_div_mul_cancel(a.mul(p.x.add(q.x)), two_val);
    F::axiom_eqv_transitive(
        two_val.mul(a.mul(p.x.add(q.x)).div(two_val)),
        a.mul(p.x.add(q.x)).div(two_val).mul(two_val),
        a.mul(p.x.add(q.x)),
    );
    F::axiom_eqv_transitive(
        two_val.mul(a.mul(mx)),
        two_val.mul(a.mul(p.x.add(q.x)).div(two_val)),
        a.mul(p.x.add(q.x)),
    );

    // Clear y: two*(b*my) ≡ b*(p.y+q.y)
    crate::line_intersection::lemma_mul_div_assoc(b, p.y.add(q.y), two_val);
    lemma_mul_congruence_right::<F>(two_val, b.mul(my), b.mul(p.y.add(q.y)).div(two_val));
    F::axiom_mul_commutative(two_val, b.mul(p.y.add(q.y)).div(two_val));
    lemma_div_mul_cancel(b.mul(p.y.add(q.y)), two_val);
    F::axiom_eqv_transitive(
        two_val.mul(b.mul(p.y.add(q.y)).div(two_val)),
        b.mul(p.y.add(q.y)).div(two_val).mul(two_val),
        b.mul(p.y.add(q.y)),
    );
    F::axiom_eqv_transitive(
        two_val.mul(b.mul(my)),
        two_val.mul(b.mul(p.y.add(q.y)).div(two_val)),
        b.mul(p.y.add(q.y)),
    );

    // two*M ≡ a*(px+qx) + b*(py+qy)
    lemma_add_congruence::<F>(
        two_val.mul(a.mul(mx)), a.mul(p.x.add(q.x)),
        two_val.mul(b.mul(my)), b.mul(p.y.add(q.y)),
    );
    F::axiom_eqv_transitive(
        two_val.mul(M),
        two_val.mul(a.mul(mx)).add(two_val.mul(b.mul(my))),
        a.mul(p.x.add(q.x)).add(b.mul(p.y.add(q.y))),
    );

    // Step 7: a*(px+qx) ≡ qx²-px² and b*(py+qy) ≡ qy²-py² via difference of squares
    F::axiom_add_commutative(p.x, q.x);
    lemma_mul_congruence_right::<F>(a, p.x.add(q.x), q.x.add(p.x));
    lemma_square_sub::<F>(q.x, p.x);
    F::axiom_eqv_transitive(
        a.mul(p.x.add(q.x)), a.mul(q.x.add(p.x)),
        qx_sq.sub(px_sq),
    );

    F::axiom_add_commutative(p.y, q.y);
    lemma_mul_congruence_right::<F>(b, p.y.add(q.y), q.y.add(p.y));
    lemma_square_sub::<F>(q.y, p.y);
    F::axiom_eqv_transitive(
        b.mul(p.y.add(q.y)), b.mul(q.y.add(p.y)),
        qy_sq.sub(py_sq),
    );

    // Chain: two*M ≡ (qx²-px²)+(qy²-py²) ≡ norm_sq_q - norm_sq_p
    lemma_add_congruence::<F>(
        a.mul(p.x.add(q.x)), qx_sq.sub(px_sq),
        b.mul(p.y.add(q.y)), qy_sq.sub(py_sq),
    );
    crate::circle_circle_proofs::lemma_diff_sum_rearrange(qx_sq, px_sq, qy_sq, py_sq);
    F::axiom_eqv_transitive(
        two_val.mul(M),
        a.mul(p.x.add(q.x)).add(b.mul(p.y.add(q.y))),
        qx_sq.sub(px_sq).add(qy_sq.sub(py_sq)),
    );
    F::axiom_eqv_transitive(
        two_val.mul(M),
        qx_sq.sub(px_sq).add(qy_sq.sub(py_sq)),
        norm_sq_q.sub(norm_sq_p),
    );

    // Step 8: T1+T2 ≡ norm_sq_q - norm_sq_p
    F::axiom_eqv_transitive(T1.add(T2), two_val.mul(M), norm_sq_q.sub(norm_sq_p));

    // Step 9: D1+D2 ≡ norm_sq_p - norm_sq_q
    crate::circle_circle_proofs::lemma_diff_sum_rearrange(px_sq, qx_sq, py_sq, qy_sq);

    // Step 10: (T1+T2)+(D1+D2) ≡ 0 via telescoping cancellation
    lemma_add_congruence::<F>(
        T1.add(T2), norm_sq_q.sub(norm_sq_p),
        D1.add(D2), norm_sq_p.sub(norm_sq_q),
    );
    lemma_sub_add_sub::<F>(norm_sq_q, norm_sq_p, norm_sq_q);
    lemma_sub_self::<F>(norm_sq_q);
    F::axiom_eqv_transitive(
        norm_sq_q.sub(norm_sq_p).add(norm_sq_p.sub(norm_sq_q)),
        norm_sq_q.sub(norm_sq_q),
        F::zero(),
    );

    // Chain: dist_p - dist_q ≡ 0
    F::axiom_eqv_transitive(
        dist_p.sub(dist_q),
        T1.add(T2).add(D1.add(D2)),
        norm_sq_q.sub(norm_sq_p).add(norm_sq_p.sub(norm_sq_q)),
    );
    F::axiom_eqv_transitive(
        dist_p.sub(dist_q),
        norm_sq_q.sub(norm_sq_p).add(norm_sq_p.sub(norm_sq_q)),
        F::zero(),
    );

    // Conclude: dist_p ≡ dist_q
    crate::collinearity::lemma_sub_zero_implies_eqv(dist_p, dist_q);
}

// ===========================================================================
//  Linear system uniqueness for symmetric decomposition
// ===========================================================================

/// If dx*u + dy*v ≡ 0 and -dy*u + dx*v ≡ 0 and dx²+dy² ≢ 0,
/// then u ≡ 0 and v ≡ 0.
///
/// This is the uniqueness of the trivial solution of the 2×2 system
/// with coefficient matrix [[dx, dy], [-dy, dx]] (rotation matrix scaled by |d|).
proof fn lemma_2x2_trivial_solution<F: OrderedField>(
    dx: F, dy: F, u: F, v: F,
)
    requires
        // dx*u + dy*v ≡ 0
        dx.mul(u).add(dy.mul(v)).eqv(F::zero()),
        // -dy*u + dx*v ≡ 0
        dy.neg().mul(u).add(dx.mul(v)).eqv(F::zero()),
        // det ≢ 0
        !dx.mul(dx).add(dy.mul(dy)).eqv(F::zero()),
    ensures
        u.eqv(F::zero()),
        v.eqv(F::zero()),
{
    let dot_dd = dx.mul(dx).add(dy.mul(dy));
    // From eq1: dx*u + dy*v ≡ 0
    // Multiply by dx: dx²*u + dx*dy*v ≡ 0
    lemma_mul_congruence_right::<F>(dx, dx.mul(u).add(dy.mul(v)), F::zero());
    // dx * 0 ≡ 0: use commutative + mul_zero_left
    F::axiom_mul_commutative(dx, F::zero());
    lemma_mul_zero_left::<F>(dx);
    F::axiom_eqv_transitive(dx.mul(F::zero()), F::zero().mul(dx), F::zero());
    F::axiom_eqv_transitive(
        dx.mul(dx.mul(u).add(dy.mul(v))),
        dx.mul(F::zero()),
        F::zero());
    // Distribute: dx*(dx*u + dy*v) ≡ dx*(dx*u) + dx*(dy*v) ≡ (dx*dx)*u + (dx*dy)*v
    F::axiom_mul_distributes_left(dx, dx.mul(u), dy.mul(v));
    F::axiom_mul_associative(dx, dx, u);
    F::axiom_mul_associative(dx, dy, v);
    F::axiom_eqv_symmetric(dx.mul(dx).mul(u), dx.mul(dx.mul(u)));
    F::axiom_eqv_symmetric(dx.mul(dy).mul(v), dx.mul(dy.mul(v)));
    lemma_add_congruence::<F>(
        dx.mul(dx.mul(u)), dx.mul(dx).mul(u),
        dx.mul(dy.mul(v)), dx.mul(dy).mul(v));
    F::axiom_eqv_transitive(
        dx.mul(dx.mul(u).add(dy.mul(v))),
        dx.mul(dx.mul(u)).add(dx.mul(dy.mul(v))),
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)));
    // So dx²*u + (dx*dy)*v ≡ 0
    // Chain: dx²*u + (dx*dy)*v ≡ dx*(dx*u+dy*v) [reverse of distribute] ≡ 0
    F::axiom_eqv_symmetric(
        dx.mul(dx.mul(u).add(dy.mul(v))),
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)));
    F::axiom_eqv_transitive(
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)),
        dx.mul(dx.mul(u).add(dy.mul(v))),
        F::zero());

    // From eq2: -dy*u + dx*v ≡ 0
    // Multiply by dy: -dy²*u + dx*dy*v ≡ 0
    // Actually multiply eq2 by dy: dy*(-dy*u + dx*v) ≡ 0
    lemma_mul_congruence_right::<F>(dy, dy.neg().mul(u).add(dx.mul(v)), F::zero());
    F::axiom_mul_commutative(dy, F::zero());
    lemma_mul_zero_left::<F>(dy);
    F::axiom_eqv_transitive(dy.mul(F::zero()), F::zero().mul(dy), F::zero());
    F::axiom_eqv_transitive(
        dy.mul(dy.neg().mul(u).add(dx.mul(v))),
        dy.mul(F::zero()),
        F::zero());
    F::axiom_mul_distributes_left(dy, dy.neg().mul(u), dx.mul(v));
    F::axiom_mul_associative(dy, dy.neg(), u);
    F::axiom_mul_associative(dy, dx, v);
    F::axiom_eqv_symmetric(dy.mul(dy.neg()).mul(u), dy.mul(dy.neg().mul(u)));
    F::axiom_eqv_symmetric(dy.mul(dx).mul(v), dy.mul(dx.mul(v)));
    lemma_add_congruence::<F>(
        dy.mul(dy.neg().mul(u)), dy.mul(dy.neg()).mul(u),
        dy.mul(dx.mul(v)), dy.mul(dx).mul(v));
    F::axiom_eqv_transitive(
        dy.mul(dy.neg().mul(u).add(dx.mul(v))),
        dy.mul(dy.neg().mul(u)).add(dy.mul(dx.mul(v))),
        dy.mul(dy.neg()).mul(u).add(dy.mul(dx).mul(v)));
    // So (dy*(-dy))*u + (dy*dx)*v ≡ 0
    F::axiom_eqv_symmetric(
        dy.mul(dy.neg().mul(u).add(dx.mul(v))),
        dy.mul(dy.neg()).mul(u).add(dy.mul(dx).mul(v)));
    F::axiom_eqv_transitive(
        dy.mul(dy.neg()).mul(u).add(dy.mul(dx).mul(v)),
        dy.mul(dy.neg().mul(u).add(dx.mul(v))),
        F::zero());

    // dy*(-dy) ≡ -(dy*dy) by lemma_mul_neg_right or commute+neg_left
    verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_right::<F>(dy, dy);
    // dy*(-dy) ≡ -(dy*dy)
    F::axiom_mul_congruence_left(dy.mul(dy.neg()), dy.mul(dy).neg(), u);
    // So -(dy²)*u + (dy*dx)*v ≡ 0

    // dy*dx ≡ dx*dy by commutativity
    F::axiom_mul_commutative(dy, dx);
    F::axiom_mul_congruence_left(dy.mul(dx), dx.mul(dy), v);
    // So -(dy²)*u + (dx*dy)*v ≡ 0
    lemma_add_congruence::<F>(
        dy.mul(dy.neg()).mul(u), dy.mul(dy).neg().mul(u),
        dy.mul(dx).mul(v), dx.mul(dy).mul(v));
    // Chain: -(dy²)*u + (dx*dy)*v ≡ (dy*-dy)*u + (dy*dx)*v ≡ 0
    F::axiom_eqv_symmetric(
        dy.mul(dy.neg()).mul(u).add(dy.mul(dx).mul(v)),
        dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v)));
    F::axiom_eqv_transitive(
        dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v)),
        dy.mul(dy.neg()).mul(u).add(dy.mul(dx).mul(v)),
        F::zero());

    // Now subtract eq_scaled_2 from eq_scaled_1:
    // (dx²*u + (dx*dy)*v) - (-(dy²)*u + (dx*dy)*v)
    // = dx²*u + dy²*u = (dx² + dy²)*u = dot_dd * u
    // Both ≡ 0, so their difference ≡ 0.
    lemma_sub_congruence::<F>(
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)),
        F::zero(),
        dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v)),
        F::zero());
    lemma_sub_self::<F>(F::zero());
    F::axiom_eqv_transitive(
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)).sub(
            dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v))),
        F::zero().sub(F::zero()),
        F::zero());

    // Now simplify the LHS: (A + C) - (B + C) = A - B where
    // A = dx²*u, B = -(dy²)*u, C = (dx*dy)*v
    // A - B = dx²*u - (-(dy²)*u) = dx²*u + dy²*u = (dx²+dy²)*u
    // Need: (A+C) - (B+C) ≡ A - B
    // This is: a+c - (b+c) ≡ a - b
    lemma_add_sub_cancel_common::<F>(
        dx.mul(dx).mul(u),
        dy.mul(dy).neg().mul(u),
        dx.mul(dy).mul(v));
    // So dx²*u - (-(dy²)*u) ≡ 0

    // dx²*u - (-(dy²)*u) = dx²*u + dy²*u (sub neg = add)
    // -(-(dy²)) = dy²
    F::axiom_sub_is_add_neg(dx.mul(dx).mul(u), dy.mul(dy).neg().mul(u));
    // dx²*u + (-(-(dy²)*u))
    // -(-(dy²)*u) ≡ dy²*u by neg_involution on mul + neg
    lemma_neg_involution::<F>(dy.mul(dy).mul(u));
    lemma_mul_neg_left::<F>(dy.mul(dy), u);
    // -(dy²) * u ≡ -(dy²*u)
    F::axiom_neg_congruence(dy.mul(dy).neg().mul(u), dy.mul(dy).mul(u).neg());
    // -(-(dy²)*u) ≡ -(-(dy²*u)) ≡ dy²*u
    F::axiom_eqv_transitive(
        dy.mul(dy).neg().mul(u).neg(),
        dy.mul(dy).mul(u).neg().neg(),
        dy.mul(dy).mul(u));
    // So dx²*u.sub(-(dy²)*u) ≡ dx²*u.add(dy²*u)
    lemma_add_congruence_right::<F>(
        dx.mul(dx).mul(u),
        dy.mul(dy).neg().mul(u).neg(),
        dy.mul(dy).mul(u));
    // Using sub = add neg:
    F::axiom_eqv_transitive(
        dx.mul(dx).mul(u).sub(dy.mul(dy).neg().mul(u)),
        dx.mul(dx).mul(u).add(dy.mul(dy).neg().mul(u).neg()),
        dx.mul(dx).mul(u).add(dy.mul(dy).mul(u)));

    // Factor: dx²*u + dy²*u = (dx²+dy²)*u
    F::axiom_eqv_symmetric(
        dx.mul(dx).add(dy.mul(dy)).mul(u),
        dx.mul(dx).mul(u).add(dy.mul(dy).mul(u)));
    // By right-distributivity (derived from left + commutativity):
    // (a+b)*c = a*c + b*c
    verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(
        dx.mul(dx), dy.mul(dy), u);

    // Chain to dot_dd*u ≡ 0:
    // We have: dx²*u.sub(-(dy²)*u) ≡ (A+C).sub(B+C) ≡ 0
    // (from lemma_add_sub_cancel_common + sub_congruence)
    // And: dx²*u.sub(-(dy²)*u) ≡ dx²*u + dy²*u (from sub-neg = add above)
    // And: dx²*u + dy²*u ≡ dot_dd*u (from distributes_right)
    // So: dot_dd*u ≡ dx²*u + dy²*u ≡ dx²*u.sub(-(dy²)*u)
    //     And: dx²*u.sub(-(dy²)*u) ≡ (A+C).sub(B+C) ≡ 0
    // Combine:
    F::axiom_eqv_symmetric(
        dx.mul(dx).mul(u).sub(dy.mul(dy).neg().mul(u)),
        dx.mul(dx).mul(u).add(dy.mul(dy).mul(u)));
    F::axiom_eqv_transitive(
        dot_dd.mul(u),
        dx.mul(dx).mul(u).add(dy.mul(dy).mul(u)),
        dx.mul(dx).mul(u).sub(dy.mul(dy).neg().mul(u)));
    // dx²*u.sub(-(dy²)*u) ≡ (A+C)-(B+C) by cancel_common
    F::axiom_eqv_symmetric(
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)).sub(
            dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v))),
        dx.mul(dx).mul(u).sub(dy.mul(dy).neg().mul(u)));
    F::axiom_eqv_transitive(
        dot_dd.mul(u),
        dx.mul(dx).mul(u).sub(dy.mul(dy).neg().mul(u)),
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)).sub(
            dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v))));
    F::axiom_eqv_transitive(dot_dd.mul(u),
        dx.mul(dx).mul(u).add(dx.mul(dy).mul(v)).sub(
            dy.mul(dy).neg().mul(u).add(dx.mul(dy).mul(v))),
        F::zero());

    // dot_dd * u ≡ 0, dot_dd ≢ 0 → u ≡ 0
    // Need: dot_dd.mul(u).eqv(dot_dd.mul(F::zero()))
    F::axiom_mul_commutative(dot_dd, F::zero());
    lemma_mul_zero_left::<F>(dot_dd);
    F::axiom_eqv_symmetric(F::zero().mul(dot_dd), F::zero());
    F::axiom_eqv_transitive(dot_dd.mul(F::zero()), F::zero().mul(dot_dd), F::zero());
    F::axiom_eqv_symmetric(dot_dd.mul(F::zero()), F::zero());
    // dot_dd*u ≡ 0 ≡ dot_dd*0
    F::axiom_eqv_transitive(dot_dd.mul(u), F::zero(), dot_dd.mul(F::zero()));
    verus_algebra::lemmas::field_lemmas::lemma_mul_cancel_left::<F>(u, F::zero(), dot_dd);

    // Now v: substitute u ≡ 0 into eq1: dx*0 + dy*v ≡ 0 → dy*v ≡ 0
    // From eq2: -dy*0 + dx*v ≡ 0 → dx*v ≡ 0
    // Then (dx²+dy²)*v ≡ 0 by same argument, cancel → v ≡ 0
    // Simpler: from eq1, dx*u ≡ 0, so dy*v ≡ 0 - dx*u ≡ 0 - 0 ≡ 0
    // And from eq2, dx*v ≡ 0 similarly.
    // Then dx²*v + dy²*v = dot_dd*v ≡ 0, cancel.
    lemma_mul_congruence_right::<F>(dx, u, F::zero());
    // dx*u ≡ dx*0 ≡ 0
    F::axiom_mul_commutative(dx, F::zero());
    lemma_mul_zero_left::<F>(dx);
    F::axiom_eqv_transitive(dx.mul(u), dx.mul(F::zero()), F::zero().mul(dx));
    F::axiom_eqv_transitive(dx.mul(u), F::zero().mul(dx), F::zero());
    // eq1: dx*u + dy*v ≡ 0, dx*u ≡ 0, so 0 + dy*v ≡ 0 → dy*v ≡ 0
    // dx*u ≡ 0 (already proved), dy*v ≡ dy*v (reflexive)
    F::axiom_eqv_reflexive(dy.mul(v));
    lemma_add_congruence::<F>(dx.mul(u), F::zero(), dy.mul(v), dy.mul(v));
    // dx*u + dy*v ≡ 0 + dy*v
    // 0 + dy*v ≡ dy*v
    lemma_add_zero_left::<F>(dy.mul(v));
    // Chain: dy*v ≡ 0+dy*v ≡ dx*u+dy*v ≡ 0
    F::axiom_eqv_symmetric(dx.mul(u).add(dy.mul(v)), F::zero().add(dy.mul(v)));
    F::axiom_eqv_transitive(
        F::zero().add(dy.mul(v)),
        dx.mul(u).add(dy.mul(v)),
        F::zero());
    F::axiom_eqv_symmetric(F::zero().add(dy.mul(v)), dy.mul(v));
    F::axiom_eqv_symmetric(dy.mul(v), F::zero().add(dy.mul(v)));
    F::axiom_eqv_transitive(dy.mul(v), F::zero().add(dy.mul(v)), F::zero());

    // Similarly dx*v ≡ 0 from eq2
    lemma_mul_congruence_right::<F>(dy.neg(), u, F::zero());
    lemma_mul_zero_left::<F>(dy.neg());
    F::axiom_mul_commutative(dy.neg(), F::zero());
    F::axiom_eqv_transitive(dy.neg().mul(u), dy.neg().mul(F::zero()),
        F::zero().mul(dy.neg()));
    F::axiom_eqv_transitive(dy.neg().mul(u), F::zero().mul(dy.neg()), F::zero());
    // neg_dy*u ≡ 0 (already proved on line above)
    F::axiom_eqv_reflexive(dx.mul(v));
    lemma_add_congruence::<F>(dy.neg().mul(u), F::zero(), dx.mul(v), dx.mul(v));
    // neg_dy*u + dx*v ≡ 0 + dx*v
    lemma_add_zero_left::<F>(dx.mul(v));
    // Chain: dx*v ≡ 0+dx*v ≡ neg_dy*u+dx*v ≡ 0
    F::axiom_eqv_symmetric(dy.neg().mul(u).add(dx.mul(v)), F::zero().add(dx.mul(v)));
    F::axiom_eqv_transitive(F::zero().add(dx.mul(v)),
        dy.neg().mul(u).add(dx.mul(v)), F::zero());
    F::axiom_eqv_symmetric(F::zero().add(dx.mul(v)), dx.mul(v));
    F::axiom_eqv_symmetric(dx.mul(v), F::zero().add(dx.mul(v)));
    F::axiom_eqv_transitive(dx.mul(v), F::zero().add(dx.mul(v)), F::zero());

    // Now: dy*v ≡ 0 and dx*v ≡ 0
    // dot_dd * v = (dx²+dy²)*v = dx²*v + dy²*v
    // dx²*v = dx*(dx*v) ≡ dx*0 ≡ 0
    lemma_mul_congruence_right::<F>(dx, dx.mul(v), F::zero());
    F::axiom_mul_commutative(dx, F::zero());
    lemma_mul_zero_left::<F>(dx);
    F::axiom_eqv_transitive(dx.mul(dx.mul(v)), dx.mul(F::zero()), F::zero().mul(dx));
    F::axiom_eqv_transitive(dx.mul(dx.mul(v)), F::zero().mul(dx), F::zero());
    F::axiom_mul_associative(dx, dx, v);
    F::axiom_eqv_transitive(dx.mul(dx).mul(v), dx.mul(dx.mul(v)), F::zero());

    // dy²*v = dy*(dy*v) ≡ dy*0 ≡ 0
    lemma_mul_congruence_right::<F>(dy, dy.mul(v), F::zero());
    F::axiom_mul_commutative(dy, F::zero());
    lemma_mul_zero_left::<F>(dy);
    F::axiom_eqv_transitive(dy.mul(dy.mul(v)), dy.mul(F::zero()), F::zero().mul(dy));
    F::axiom_eqv_transitive(dy.mul(dy.mul(v)), F::zero().mul(dy), F::zero());
    F::axiom_mul_associative(dy, dy, v);
    F::axiom_eqv_transitive(dy.mul(dy).mul(v), dy.mul(dy.mul(v)), F::zero());

    // dot_dd * v = dx²*v + dy²*v ≡ 0 + 0 ≡ 0
    // dx²*v ≡ 0, dy²*v ≡ 0 (already proved)
    lemma_add_congruence::<F>(
        dx.mul(dx).mul(v), F::zero(),
        dy.mul(dy).mul(v), F::zero());
    lemma_add_zero_left::<F>(F::zero());
    F::axiom_eqv_transitive(
        dx.mul(dx).mul(v).add(dy.mul(dy).mul(v)),
        F::zero().add(F::zero()),
        F::zero());
    // Factor: dx²*v + dy²*v ≡ (dx²+dy²)*v
    verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(
        dx.mul(dx), dy.mul(dy), v);
    F::axiom_eqv_transitive(dot_dd.mul(v),
        dx.mul(dx).mul(v).add(dy.mul(dy).mul(v)),
        F::zero());
    // Cancel: dot_dd * v ≡ dot_dd * 0, cancel
    lemma_mul_zero_left::<F>(dot_dd);
    F::axiom_mul_commutative(F::zero(), dot_dd);
    F::axiom_eqv_transitive(dot_dd.mul(v), F::zero(), dot_dd.mul(F::zero()));
    F::axiom_eqv_symmetric(dot_dd.mul(v), dot_dd.mul(F::zero()));
    verus_algebra::lemmas::field_lemmas::lemma_mul_cancel_left::<F>(v, F::zero(), dot_dd);
}

/// (a + c) - (b + c) ≡ a - b
proof fn lemma_add_sub_cancel_common<F: OrderedField>(a: F, b: F, c: F)
    ensures
        a.add(c).sub(b.add(c)).eqv(a.sub(b)),
{
    // (a+c) - (b+c) = (a+c) + (-(b+c)) = (a+c) + (-b + -c)
    F::axiom_sub_is_add_neg(a.add(c), b.add(c));
    // -(b+c) ≡ -b + -c by neg distributes over add
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(b, c);
    lemma_add_congruence_right::<F>(a.add(c), b.add(c).neg(), b.neg().add(c.neg()));
    F::axiom_eqv_transitive(
        a.add(c).sub(b.add(c)),
        a.add(c).add(b.add(c).neg()),
        a.add(c).add(b.neg().add(c.neg())));
    // (a+c) + (-b + -c) = a + (c + (-b + -c)) by assoc
    F::axiom_add_associative(a, c, b.neg().add(c.neg()));
    F::axiom_eqv_symmetric(a.add(c).add(b.neg().add(c.neg())),
        a.add(c.add(b.neg().add(c.neg()))));
    // c + (-b + -c) = c + (-c + -b) by inner commutativity
    F::axiom_add_commutative(b.neg(), c.neg());
    lemma_add_congruence_right::<F>(c, b.neg().add(c.neg()), c.neg().add(b.neg()));
    // c + (-c + -b) = (c + -c) + -b by assoc
    F::axiom_add_associative(c, c.neg(), b.neg());
    // c + -c ≡ 0
    F::axiom_add_inverse_right(c);
    F::axiom_add_congruence_left(c.add(c.neg()), F::zero(), b.neg());
    // 0 + -b ≡ -b
    lemma_add_zero_left::<F>(b.neg());
    F::axiom_eqv_transitive(
        c.add(c.neg()).add(b.neg()),
        F::zero().add(b.neg()),
        b.neg());
    // Chain: c + (-c + -b) ≡ (c + -c) + -b ≡ 0 + -b ≡ -b
    F::axiom_eqv_symmetric(
        c.add(c.neg()).add(b.neg()),
        c.add(c.neg().add(b.neg())));
    F::axiom_eqv_transitive(
        c.add(c.neg().add(b.neg())),
        c.add(c.neg()).add(b.neg()),
        b.neg());
    F::axiom_eqv_transitive(
        c.add(b.neg().add(c.neg())),
        c.add(c.neg().add(b.neg())),
        b.neg());
    // a + (c + (-b + -c)) ≡ a + -b
    lemma_add_congruence_right::<F>(a, c.add(b.neg().add(c.neg())), b.neg());
    // a + -b ≡ a - b
    F::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    F::axiom_sub_is_add_neg(a, b);
    // Full chain
    F::axiom_eqv_transitive(
        a.add(c).sub(b.add(c)),
        a.add(c).add(b.neg().add(c.neg())),
        a.add(c.add(b.neg().add(c.neg()))));
    F::axiom_eqv_transitive(
        a.add(c).sub(b.add(c)),
        a.add(c.add(b.neg().add(c.neg()))),
        a.add(b.neg()));
    F::axiom_eqv_transitive(
        a.add(c).sub(b.add(c)),
        a.add(b.neg()),
        a.sub(b));
}

// TODO: To complete the Symmetric decomposition proof, prove:
// 1. lemma_reflect_satisfies_perp: dot(reflect(p,a,b) - p, d) ≡ 0
// 2. lemma_reflect_midpoint_on_axis: midpoint(p, reflect(p,a,b)) on line(a,b)
// Then combine with lemma_2x2_trivial_solution to get:
//   perp(q-p, d) && midpoint_on_axis(p,q) ==> q.eqv(reflect(p,a,b))
// The algebraic expansion is very tedious (~200 lines of field axiom calls)
// due to reflect_point_across_line involving division.

/// reflect(p, a, b) satisfies perpendicularity: dot(reflect - p, d) ≡ 0.
/// INCOMPLETE: the algebraic proof requires expanding the reflect formula
/// through division and showing cancellation. The key insight is that
/// t*dot_dd ≡ dot_pad (by div_mul_cancel), which makes dot(r-p, d) = 2*(t*dot_dd - dot_pad) = 0.
pub proof fn lemma_reflect_satisfies_perp<F: OrderedField>(
    p: Point2<F>, a: Point2<F>, b: Point2<F>,
)
    requires
        !sub2(b, a).x.mul(sub2(b, a).x).add(sub2(b, a).y.mul(sub2(b, a).y)).eqv(F::zero()),
    ensures ({
        let d = sub2(b, a);
        let r = reflect_point_across_line(p, a, b);
        sub2(r, p).x.mul(d.x).add(sub2(r, p).y.mul(d.y)).eqv(F::zero())
    }),
{
    let d = sub2(b, a);
    let dx = d.x;
    let dy = d.y;
    let pa = sub2(p, a);
    let dot_dd = dx.mul(dx).add(dy.mul(dy));
    let dot_pad = pa.x.mul(dx).add(pa.y.mul(dy));
    let t = dot_pad.div(dot_dd);
    let two = F::one().add(F::one());

    // Key fact: t*dot_dd ≡ dot_pad
    verus_algebra::lemmas::field_lemmas::lemma_div_mul_cancel::<F>(dot_pad, dot_dd);
    assert(t.mul(dot_dd).eqv(dot_pad));

    // t*dx² ≡ t*dx*dx. By associativity: t*(dx*dx) = (t*dx)*dx
    F::axiom_mul_associative(t, dx, dx);
    // t*dy² similarly
    F::axiom_mul_associative(t, dy, dy);
    // t*dot_dd = t*(dx²+dy²) = t*dx² + t*dy² by distributivity
    F::axiom_mul_distributes_left(t, dx.mul(dx), dy.mul(dy));
    // So t*dx² + t*dy² ≡ dot_pad = pa.x*dx + pa.y*dy

    // The reflect formula:
    // r.x = two * (a.x + t*dx) - p.x
    // r.y = two * (a.y + t*dy) - p.y
    // (r.x - p.x) = two*(a.x + t*dx) - p.x - p.x = two*(a.x + t*dx) - two*p.x
    //             = two*(a.x + t*dx - p.x) = two*(t*dx - (p.x - a.x)) = two*(t*dx - pa.x)
    // dot(r-p, d) = (r.x-p.x)*dx + (r.y-p.y)*dy
    //             = two*(t*dx - pa.x)*dx + two*(t*dy - pa.y)*dy
    //             = two*(t*dx*dx - pa.x*dx + t*dy*dy - pa.y*dy)
    //             = two*((t*dx*dx + t*dy*dy) - (pa.x*dx + pa.y*dy))
    //             = two*(t*dot_dd - dot_pad)
    //             = two*0 = 0

    // Help Z3 along: assert the sub-result
    // t*dx*dx + t*dy*dy ≡ t*(dx²+dy²) ≡ dot_pad
    assert(t.mul(dx.mul(dx)).add(t.mul(dy.mul(dy))).eqv(dot_pad)) by {
        // t*(dx²+dy²) = t*dx² + t*dy² by distributivity
        F::axiom_mul_distributes_left(t, dx.mul(dx), dy.mul(dy));
        // Reverse: t*dx² + t*dy² ≡ t*(dx²+dy²)
        F::axiom_eqv_symmetric(
            t.mul(dx.mul(dx).add(dy.mul(dy))),
            t.mul(dx.mul(dx)).add(t.mul(dy.mul(dy))));
        // t*(dx²+dy²) = t*dot_dd (structural equality, no axiom needed)
        // Chain: t*dx²+t*dy² ≡ t*(dx²+dy²) = t*dot_dd ≡ dot_pad
        F::axiom_eqv_transitive(
            t.mul(dx.mul(dx)).add(t.mul(dy.mul(dy))),
            t.mul(dx.mul(dx).add(dy.mul(dy))),
            dot_pad);
    };

    // t*dx*dx - pa.x*dx = (t*dx - pa.x)*dx
    // This is: dx*(t*dx - pa.x) by commutativity
    // We need to show the full expression equals zero.
    // sub2(r, p).x = r.x - p.x = two*(a.x + t*dx) - p.x - p.x
    // sub2(r, p).x = two.mul(a.x.add(t.mul(dx))).sub(p.x).sub(p.x)
    // Actually sub2(r, p) = Point2 { x: r.x.sub(p.x), y: r.y.sub(p.y) }
    // r.x = two.mul(proj_x).sub(p.x) where proj_x = a.x.add(t.mul(dx))
    // so r.x.sub(p.x) = two.mul(a.x.add(t.mul(dx))).sub(p.x).sub(p.x)

    // This is getting very complex with the sub2 expansion.
    // Let me try a different approach: provide more Z3 hints.

    // Hint: proj_x = a.x + t*dx, proj_y = a.y + t*dy
    let proj_x = a.x.add(t.mul(dx));
    let proj_y = a.y.add(t.mul(dy));

    // proj is on line through a in direction d:
    // proj - a = (t*dx, t*dy), which is parallel to d
    // So dot(proj - a, d_perp) = 0 where d_perp = (-dy, dx)

    // r = 2*proj - p, so r - p = 2*proj - 2*p = 2*(proj - p)
    // dot(r-p, d) = 2*dot(proj-p, d) = 2*(dot(proj-a, d) + dot(a-p, d))
    //             = 2*(dot(proj-a, d) - dot(pa, d))
    //             = 2*(t*dot_dd - dot_pad) = 2*0 = 0
    //
    // dot(proj-a, d) = t*dx*dx + t*dy*dy = t*(dx²+dy²) = t*dot_dd ≡ dot_pad
    // So dot(proj-a, d) - dot_pad ≡ 0

    // Instead of expanding everything, let me try providing just the key assertions
    // and let Z3 connect them through the function definitions.

    // Key assertion 1: proj - a = (t*dx, t*dy)
    // proj_x = a.x + t*dx. proj_x - a.x = (a.x + t*dx) - a.x ≡ t*dx
    // Use: (a+b)-a ≡ b. Verus has (a+b)-b ≡ a, so need comm first.
    assert(proj_x.sub(a.x).eqv(t.mul(dx))) by {
        // proj_x = a.x + t*dx, need: (a.x + t*dx) - a.x ≡ t*dx
        // Commute: a.x + t*dx ≡ t*dx + a.x
        F::axiom_add_commutative(a.x, t.mul(dx));
        // (t*dx + a.x) - a.x ≡ t*dx by add_then_sub_cancel
        lemma_add_then_sub_cancel::<F>(t.mul(dx), a.x);
        // sub congruence: proj_x ≡ t*dx + a.x from commutativity
        // (a.x + t*dx) - a.x ≡ (t*dx + a.x) - a.x = t*dx
        F::axiom_eqv_reflexive(a.x);
        lemma_sub_congruence::<F>(
            a.x.add(t.mul(dx)), t.mul(dx).add(a.x), a.x, a.x);
        F::axiom_eqv_transitive(
            a.x.add(t.mul(dx)).sub(a.x),
            t.mul(dx).add(a.x).sub(a.x),
            t.mul(dx));
    };
    assert(proj_y.sub(a.y).eqv(t.mul(dy))) by {
        F::axiom_add_commutative(a.y, t.mul(dy));
        lemma_add_then_sub_cancel::<F>(t.mul(dy), a.y);
        F::axiom_eqv_reflexive(a.y);
        lemma_sub_congruence::<F>(
            a.y.add(t.mul(dy)), t.mul(dy).add(a.y), a.y, a.y);
        F::axiom_eqv_transitive(
            a.y.add(t.mul(dy)).sub(a.y),
            t.mul(dy).add(a.y).sub(a.y),
            t.mul(dy));
    };

    // Key assertion 2: dot(proj-a, d) ≡ t*dot_dd
    assert(proj_x.sub(a.x).mul(dx).add(proj_y.sub(a.y).mul(dy)).eqv(t.mul(dot_dd))) by {
        // (t*dx)*dx + (t*dy)*dy = t*dx² + t*dy² = t*(dx²+dy²) = t*dot_dd
        F::axiom_mul_congruence_left(proj_x.sub(a.x), t.mul(dx), dx);
        F::axiom_mul_congruence_left(proj_y.sub(a.y), t.mul(dy), dy);
        F::axiom_mul_associative(t, dx, dx);
        F::axiom_mul_associative(t, dy, dy);
        F::axiom_eqv_transitive(proj_x.sub(a.x).mul(dx), t.mul(dx).mul(dx), t.mul(dx.mul(dx)));
        F::axiom_eqv_transitive(proj_y.sub(a.y).mul(dy), t.mul(dy).mul(dy), t.mul(dy.mul(dy)));
        lemma_add_congruence::<F>(
            proj_x.sub(a.x).mul(dx), t.mul(dx.mul(dx)),
            proj_y.sub(a.y).mul(dy), t.mul(dy.mul(dy)));
        F::axiom_mul_distributes_left(t, dx.mul(dx), dy.mul(dy));
        F::axiom_eqv_symmetric(
            t.mul(dx.mul(dx).add(dy.mul(dy))),
            t.mul(dx.mul(dx)).add(t.mul(dy.mul(dy))));
        F::axiom_eqv_transitive(
            proj_x.sub(a.x).mul(dx).add(proj_y.sub(a.y).mul(dy)),
            t.mul(dx.mul(dx)).add(t.mul(dy.mul(dy))),
            t.mul(dot_dd));
    };

    // Key assertion 3: dot(proj-a, d) ≡ dot_pad (from t*dot_dd ≡ dot_pad)
    assert(proj_x.sub(a.x).mul(dx).add(proj_y.sub(a.y).mul(dy)).eqv(dot_pad)) by {
        F::axiom_eqv_transitive(
            proj_x.sub(a.x).mul(dx).add(proj_y.sub(a.y).mul(dy)),
            t.mul(dot_dd),
            dot_pad);
    };

    // Key assertion 4: dot(proj-a, d) - dot_pad ≡ 0
    let dot_proj_a_d = proj_x.sub(a.x).mul(dx).add(proj_y.sub(a.y).mul(dy));
    // dot_proj_a_d ≡ dot_pad (from assertion 3 above)
    // dot_proj_a_d - dot_pad ≡ dot_pad - dot_pad ≡ 0
    F::axiom_eqv_reflexive(dot_pad);
    lemma_sub_congruence::<F>(dot_proj_a_d, dot_pad, dot_pad, dot_pad);
    lemma_sub_self::<F>(dot_pad);
    F::axiom_eqv_transitive(dot_proj_a_d.sub(dot_pad), dot_pad.sub(dot_pad), F::zero());

    // Now bridge to the postcondition.
    // sub2(r, p).x = r.x - p.x = (two*proj_x - p.x) - p.x
    // We need: sub2(r,p).x ≡ two*(proj_x - p.x) = two*((proj_x-a.x) - pa.x) = two*(t*dx - pa.x)
    //
    // Step 5: (two*proj_x - p.x) - p.x ≡ two*proj_x - two*p.x
    // = two*(proj_x - p.x) by distribution (factoring two out)
    //
    // Actually, sub2(r, p).x.mul(dx) + sub2(r,p).y.mul(dy)
    // = (two*proj_x - px - px)*dx + (two*proj_y - py - py)*dy
    //
    // Let's try: prove that the result ≡ two*(dot_proj_a_d - dot_pad) ≡ two*0 ≡ 0.
    //
    // dot(r-p, d) = (r.x-p.x)*dx + (r.y-p.y)*dy
    //
    // r.x-p.x = two*proj_x - p.x - p.x
    //         ≡ two*proj_x - two*p.x  [need to prove this]
    //         = two*(proj_x - p.x)     [need distribution]
    //
    // For now, let's try asserting the key subgoal and see if Z3 connects:

    // Helper: (a - b) - b ≡ a - (b + b)
    // Proof: sub(sub(a,b), b) = add(add(a, neg(b)), neg(b))
    //      = add(a, add(neg(b), neg(b)))  [assoc]
    //      = add(a, neg(add(b, b)))       [neg distributes]
    //      = sub(a, add(b, b))
    // And: two*b ≡ b + b (by 1*b + 1*b = (1+1)*b = two*b via distribution)
    // So: (a-b)-b ≡ a - two*b ≡ two*a' - two*b when a = two*a'... no.
    //
    // Actually we need: (two*X - Y) - Y ≡ two*(X - Y)
    // two*(X - Y) = two*X - two*Y by distribution
    // (two*X - Y) - Y ≡ two*X - Y - Y ≡ two*X - 2Y
    // Need: Y + Y ≡ two*Y
    // By: (1+1)*Y = 1*Y + 1*Y = Y + Y (distribute right)
    // So Y + Y ≡ two*Y

    // Help Z3 unfold reflect:
    let r = reflect_point_across_line(p, a, b);
    assert(r.x == two.mul(proj_x).sub(p.x));
    assert(r.y == two.mul(proj_y).sub(p.y));

    // Step 5: sub2(r,p).x ≡ two.mul(proj_x.sub(p.x))
    let rx_sub_px = sub2(r, p).x;
    assert(rx_sub_px.eqv(two.mul(proj_x.sub(p.x)))) by {
        // rx_sub_px == two.mul(proj_x).sub(p.x).sub(p.x) structurally
        assert(rx_sub_px == two.mul(proj_x).sub(p.x).sub(p.x));
        // RHS: two*(proj_x - p.x) = two*(proj_x + (-p.x))
        //    = two*proj_x + two*(-p.x)  [distributes_left]
        //    = two*proj_x + (-(two*p.x))  [mul_neg_right]
        //    = two*proj_x - two*p.x   [sub_is_add_neg]
        F::axiom_sub_is_add_neg(proj_x, p.x);
        F::axiom_mul_distributes_left(two, proj_x, p.x.neg());
        verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_right::<F>(two, p.x);
        // two*(proj_x + (-p.x)) ≡ two*proj_x + two*(-p.x)
        // two*(-p.x) ≡ -(two*p.x)
        // So two*(proj_x - p.x) ≡ two*proj_x + (-(two*p.x)) = two*proj_x - two*p.x

        // LHS: rx_sub_px = (two*proj_x - p.x) - p.x
        //     = (two*proj_x + (-p.x)) + (-p.x)  [sub_is_add_neg twice]
        //     = two*proj_x + ((-p.x) + (-p.x))  [associativity]
        F::axiom_sub_is_add_neg(two.mul(proj_x).sub(p.x), p.x);
        F::axiom_sub_is_add_neg(two.mul(proj_x), p.x);
        F::axiom_add_associative(two.mul(proj_x), p.x.neg(), p.x.neg());

        // Need: (-p.x) + (-p.x) ≡ -(two*p.x)
        // (-p.x) + (-p.x) ≡ -(p.x + p.x) by neg_add
        verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(p.x, p.x);
        F::axiom_eqv_symmetric(p.x.neg().add(p.x.neg()), p.x.add(p.x).neg());
        // -(p.x + p.x): need p.x + p.x ≡ two*p.x
        // p.x + p.x = 1*p.x + 1*p.x
        verus_algebra::lemmas::ring_lemmas::lemma_mul_one_left::<F>(p.x);
        // 1*p.x ≡ p.x, so p.x ≡ 1*p.x
        F::axiom_eqv_symmetric(F::one().mul(p.x), p.x);
        F::axiom_eqv_reflexive(p.x);
        lemma_add_congruence::<F>(p.x, F::one().mul(p.x), p.x, F::one().mul(p.x));
        // p.x + p.x ≡ 1*p.x + 1*p.x
        // 1*p.x + 1*p.x ≡ (1+1)*p.x = two*p.x by distributes_right
        verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(F::one(), F::one(), p.x);
        F::axiom_eqv_symmetric(two.mul(p.x), F::one().mul(p.x).add(F::one().mul(p.x)));
        F::axiom_eqv_transitive(
            p.x.add(p.x),
            F::one().mul(p.x).add(F::one().mul(p.x)),
            two.mul(p.x));
        // -(p.x + p.x) ≡ -(two*p.x)
        F::axiom_neg_congruence(p.x.add(p.x), two.mul(p.x));
        // (-p.x)+(-p.x) ≡ -(p.x+p.x) ≡ -(two*p.x)
        F::axiom_eqv_transitive(
            p.x.neg().add(p.x.neg()),
            p.x.add(p.x).neg(),
            two.mul(p.x).neg());

        // Chain LHS: two*proj_x + ((-p.x)+(-p.x)) ≡ two*proj_x + (-(two*p.x))
        lemma_add_congruence_right::<F>(two.mul(proj_x),
            p.x.neg().add(p.x.neg()), two.mul(p.x).neg());
        // (two*proj_x + (-p.x)) + (-p.x) ≡ two*proj_x + ((-p.x)+(-p.x)) by assoc
        F::axiom_eqv_symmetric(
            two.mul(proj_x).add(p.x.neg()).add(p.x.neg()),
            two.mul(proj_x).add(p.x.neg().add(p.x.neg())));
        // Chain: LHS ≡ two*proj_x + ((-p.x)+(-p.x)) ≡ two*proj_x + (-(two*p.x))
        F::axiom_eqv_transitive(
            two.mul(proj_x).add(p.x.neg()).add(p.x.neg()),
            two.mul(proj_x).add(p.x.neg().add(p.x.neg())),
            two.mul(proj_x).add(two.mul(p.x).neg()));

        // RHS chain: two*(proj_x+(-p.x)) ≡ two*proj_x + two*(-p.x)
        //           ≡ two*proj_x + (-(two*p.x))
        lemma_add_congruence_right::<F>(two.mul(proj_x),
            two.mul(p.x.neg()), two.mul(p.x).neg());
        // Chain: two*(proj_x+(-p.x)) ≡ two*proj_x + two*(-p.x) ≡ two*proj_x + (-(two*p.x))
        F::axiom_eqv_transitive(
            two.mul(proj_x.add(p.x.neg())),
            two.mul(proj_x).add(two.mul(p.x.neg())),
            two.mul(proj_x).add(two.mul(p.x).neg()));

        // Connect: two*(proj_x - p.x) = two*(proj_x + (-p.x)) ≡ two*proj_x + (-(two*p.x))
        // LHS = (two*proj_x - p.x) - p.x ≡ two*proj_x + (-(two*p.x))
        // They're both ≡ two*proj_x + (-(two*p.x)), so they're ≡ each other.
        F::axiom_eqv_symmetric(
            two.mul(proj_x.add(p.x.neg())),
            two.mul(proj_x).add(two.mul(p.x).neg()));
        F::axiom_eqv_transitive(
            two.mul(proj_x).add(p.x.neg()).add(p.x.neg()),
            two.mul(proj_x).add(two.mul(p.x).neg()),
            two.mul(proj_x.add(p.x.neg())));
    };

    let ry_sub_py = sub2(reflect_point_across_line(p, a, b), p).y;
    assert(ry_sub_py.eqv(two.mul(proj_y.sub(p.y)))) by {
        F::axiom_sub_is_add_neg(two.mul(proj_y).sub(p.y), p.y);
        F::axiom_sub_is_add_neg(two.mul(proj_y), p.y);
        F::axiom_sub_is_add_neg(proj_y, p.y);
        F::axiom_mul_distributes_left(two, proj_y, p.y.neg());
        verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_right::<F>(two, p.y);
    };

    // Step 6: dot(r-p, d) ≡ two * dot(proj-p, d)
    // = two * ((proj_x-p.x)*dx + (proj_y-p.y)*dy)
    // proj_x - p.x = (proj_x - a.x) - (p.x - a.x) = t*dx - pa.x
    // So dot(proj-p, d) = (t*dx - pa.x)*dx + (t*dy - pa.y)*dy
    //                   = t*dx² - pa.x*dx + t*dy² - pa.y*dy
    //                   = (t*dx² + t*dy²) - (pa.x*dx + pa.y*dy)
    //                   = t*dot_dd - dot_pad ≡ 0
    // So dot(r-p, d) ≡ two * 0 ≡ 0

    // Hmm, this is still complex. Let me try providing just rx_sub_px ≡ two*(proj_x - p.x)
    // and let Z3 handle the rest through distribution.

    // Actually, let me try: assert the full dot product using the sub-results
    assert(rx_sub_px.mul(dx).add(ry_sub_py.mul(dy)).eqv(
        two.mul(proj_x.sub(p.x).mul(dx).add(proj_y.sub(p.y).mul(dy))))) by {
        // rx_sub_px ≡ two*(proj_x - p.x), so rx_sub_px * dx ≡ two*(proj_x-p.x) * dx
        F::axiom_mul_congruence_left(rx_sub_px, two.mul(proj_x.sub(p.x)), dx);
        F::axiom_mul_associative(two, proj_x.sub(p.x), dx);
        F::axiom_eqv_transitive(
            rx_sub_px.mul(dx),
            two.mul(proj_x.sub(p.x)).mul(dx),
            two.mul(proj_x.sub(p.x).mul(dx)));

        F::axiom_mul_congruence_left(ry_sub_py, two.mul(proj_y.sub(p.y)), dy);
        F::axiom_mul_associative(two, proj_y.sub(p.y), dy);
        F::axiom_eqv_transitive(
            ry_sub_py.mul(dy),
            two.mul(proj_y.sub(p.y)).mul(dy),
            two.mul(proj_y.sub(p.y).mul(dy)));

        lemma_add_congruence::<F>(
            rx_sub_px.mul(dx), two.mul(proj_x.sub(p.x).mul(dx)),
            ry_sub_py.mul(dy), two.mul(proj_y.sub(p.y).mul(dy)));

        // two*A + two*B = two*(A+B)
        F::axiom_mul_distributes_left(two, proj_x.sub(p.x).mul(dx), proj_y.sub(p.y).mul(dy));
        F::axiom_eqv_symmetric(
            two.mul(proj_x.sub(p.x).mul(dx).add(proj_y.sub(p.y).mul(dy))),
            two.mul(proj_x.sub(p.x).mul(dx)).add(two.mul(proj_y.sub(p.y).mul(dy))));
        F::axiom_eqv_transitive(
            rx_sub_px.mul(dx).add(ry_sub_py.mul(dy)),
            two.mul(proj_x.sub(p.x).mul(dx)).add(two.mul(proj_y.sub(p.y).mul(dy))),
            two.mul(proj_x.sub(p.x).mul(dx).add(proj_y.sub(p.y).mul(dy))));
    };

    // Step 7: proj_x - p.x = (proj_x - a.x) - (p.x - a.x) = (proj_x - a.x) - pa.x
    // So dot(proj-p, d) = (proj_x-p.x)*dx + (proj_y-p.y)*dy
    // proj_x - p.x = (proj_x - a.x) + (a.x - p.x) = (proj_x - a.x) - pa.x
    // Need: (proj_x-p.x)*dx ≡ (proj_x-a.x)*dx - pa.x*dx
    // i.e. proj_x.sub(p.x).mul(dx) ≡ proj_x.sub(a.x).mul(dx).sub(pa.x.mul(dx))
    // This follows from: proj_x - p.x = (proj_x - a.x) - pa.x by additive group
    //   and then distributing mul.
    //
    // Alternatively: dot(proj-p, d) = dot(proj-a, d) - dot(pa, d) = dot_proj_a_d - dot_pad
    // dot_proj_a_d - dot_pad ≡ 0 (proved above)

    // Let me try: assert dot(proj-p, d) ≡ dot_proj_a_d - dot_pad
    let dot_proj_p_d = proj_x.sub(p.x).mul(dx).add(proj_y.sub(p.y).mul(dy));
    assert(dot_proj_p_d.eqv(dot_proj_a_d.sub(dot_pad))) by {
        // proj_x - p.x = (proj_x - a.x) - (p.x - a.x)
        // (proj_x - a.x) - pa.x
        // proj_x - p.x ≡ (proj_x - a.x) + (a.x - p.x)
        // a.x - p.x = -(p.x - a.x) = -pa.x
        // So proj_x - p.x = (proj_x - a.x) - pa.x
        lemma_sub_then_add_cancel::<F>(p.x, a.x);
        // (p.x - a.x) + a.x ≡ p.x, i.e. pa.x + a.x ≡ p.x
        // proj_x - p.x = proj_x - (pa.x + a.x) = proj_x - pa.x - a.x = (proj_x - a.x) - pa.x
        // This is getting complicated. Let me just let Z3 try with the sub_is_add_neg expansions.
        F::axiom_sub_is_add_neg(proj_x, p.x);
        F::axiom_sub_is_add_neg(proj_x, a.x);
        F::axiom_sub_is_add_neg(dot_proj_a_d, dot_pad);
    };

    // Step 8: dot(r-p, d) ≡ two * (dot_proj_a_d - dot_pad) ≡ two * 0 ≡ 0
    assert(rx_sub_px.mul(dx).add(ry_sub_py.mul(dy)).eqv(F::zero())) by {
        // From step 6: dot(r-p,d) ≡ two * dot(proj-p, d)
        // From step 7: dot(proj-p, d) ≡ dot_proj_a_d - dot_pad
        // From step 4: dot_proj_a_d - dot_pad ≡ 0
        // So: two * dot(proj-p,d) ≡ two * 0 ≡ 0
        lemma_mul_congruence_right::<F>(two, dot_proj_p_d, dot_proj_a_d.sub(dot_pad));
        lemma_mul_congruence_right::<F>(two, dot_proj_a_d.sub(dot_pad), F::zero());
        F::axiom_eqv_transitive(
            two.mul(dot_proj_p_d),
            two.mul(dot_proj_a_d.sub(dot_pad)),
            two.mul(F::zero()));
        F::axiom_mul_commutative(two, F::zero());
        lemma_mul_zero_left::<F>(two);
        F::axiom_eqv_transitive(two.mul(F::zero()), F::zero().mul(two), F::zero());
        F::axiom_eqv_transitive(two.mul(dot_proj_p_d), two.mul(F::zero()), F::zero());
        F::axiom_eqv_transitive(
            rx_sub_px.mul(dx).add(ry_sub_py.mul(dy)),
            two.mul(dot_proj_p_d),
            F::zero());
    };
}

} // verus!
