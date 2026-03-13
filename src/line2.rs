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

} // verus!
