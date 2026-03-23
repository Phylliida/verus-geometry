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

/// Helper: (two*x - y) - y ≡ two*(x - y)
/// This is used to relate sub2(reflect, p) to two*(proj - p).
proof fn lemma_two_x_sub_y_sub_y<F: OrderedField>(two: F, x: F, y: F)
    requires two.eqv(F::one().add(F::one())),
    ensures two.mul(x).sub(y).sub(y).eqv(two.mul(x.sub(y))),
{
    // LHS = (2x - y) - y
    //      = (2x + (-y)) + (-y)          [sub_is_add_neg ×2]
    //      = 2x + ((-y) + (-y))          [assoc]
    //      = 2x + (-(y + y))             [neg_add]
    //      = 2x + (-(2y))                [y + y = 2y]
    //      = 2x - 2y                     [sub_is_add_neg]
    //
    // RHS = 2*(x - y)
    //      = 2*(x + (-y))                [sub_is_add_neg]
    //      = 2x + 2*(-y)                 [distributes_left]
    //      = 2x + (-(2y))                [mul_neg_right]
    //      = 2x - 2y
    //
    // Same thing. Chain through 2x + (-(2y)).

    // -- LHS to 2x + (-(2y)) --
    F::axiom_sub_is_add_neg(two.mul(x).sub(y), y);
    F::axiom_sub_is_add_neg(two.mul(x), y);
    F::axiom_add_associative(two.mul(x), y.neg(), y.neg());
    F::axiom_eqv_symmetric(
        two.mul(x).add(y.neg()).add(y.neg()),
        two.mul(x).add(y.neg().add(y.neg())));

    // (-y) + (-y) ≡ -(y + y)
    verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(y, y);
    F::axiom_eqv_symmetric(y.neg().add(y.neg()), y.add(y).neg());

    // y + y ≡ two * y
    verus_algebra::lemmas::ring_lemmas::lemma_mul_one_left::<F>(y);
    F::axiom_eqv_symmetric(F::one().mul(y), y);
    lemma_add_congruence::<F>(y, F::one().mul(y), y, F::one().mul(y));
    verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(F::one(), F::one(), y);
    F::axiom_eqv_symmetric(F::one().add(F::one()).mul(y), F::one().mul(y).add(F::one().mul(y)));
    F::axiom_eqv_transitive(y.add(y), F::one().mul(y).add(F::one().mul(y)), F::one().add(F::one()).mul(y));
    // y + y ≡ (1+1)*y. And two ≡ 1+1, so (1+1)*y ≡ two*y by congruence
    F::axiom_eqv_symmetric(two, F::one().add(F::one()));
    F::axiom_mul_congruence_left(F::one().add(F::one()), two, y);
    F::axiom_eqv_transitive(y.add(y), F::one().add(F::one()).mul(y), two.mul(y));

    // -(y+y) ≡ -(two*y)
    F::axiom_neg_congruence(y.add(y), two.mul(y));

    // (-y)+(-y) ≡ -(y+y) ≡ -(two*y)
    F::axiom_eqv_transitive(y.neg().add(y.neg()), y.add(y).neg(), two.mul(y).neg());

    // 2x + ((-y)+(-y)) ≡ 2x + (-(two*y))
    lemma_add_congruence_right::<F>(two.mul(x), y.neg().add(y.neg()), two.mul(y).neg());

    // LHS chain: (2x-y)-y ≡ 2x+((-y)+(-y)) ≡ 2x+(-(two*y))
    F::axiom_eqv_transitive(
        two.mul(x).add(y.neg()).add(y.neg()),
        two.mul(x).add(y.neg().add(y.neg())),
        two.mul(x).add(two.mul(y).neg()));

    // -- RHS to 2x + (-(2y)) --
    F::axiom_sub_is_add_neg(x, y);
    F::axiom_mul_distributes_left(two, x, y.neg());
    verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_right::<F>(two, y);
    lemma_add_congruence_right::<F>(two.mul(x), two.mul(y.neg()), two.mul(y).neg());
    F::axiom_eqv_transitive(
        two.mul(x.add(y.neg())),
        two.mul(x).add(two.mul(y.neg())),
        two.mul(x).add(two.mul(y).neg()));

    // -- Connect LHS and RHS --
    // LHS ≡ 2x + (-(2y)) and RHS ≡ 2x + (-(2y))
    F::axiom_eqv_symmetric(
        two.mul(x.add(y.neg())),
        two.mul(x).add(two.mul(y).neg()));
    F::axiom_eqv_transitive(
        two.mul(x).add(y.neg()).add(y.neg()),
        two.mul(x).add(two.mul(y).neg()),
        two.mul(x.add(y.neg())));
    // -- Bridge ensures LHS: two.mul(x).sub(y).sub(y) to add form --
    // sub(a,b) ≡ add(a, neg(b)) by axiom
    // two.mul(x).sub(y).sub(y) ≡ two.mul(x).sub(y).add(y.neg())
    F::axiom_sub_is_add_neg(two.mul(x).sub(y), y);
    // two.mul(x).sub(y) ≡ two.mul(x).add(y.neg())
    F::axiom_sub_is_add_neg(two.mul(x), y);
    // Congruence: sub(y).add(neg(y)) → add(neg(y)).add(neg(y))
    F::axiom_add_congruence_left(two.mul(x).sub(y), two.mul(x).add(y.neg()), y.neg());
    // Chain: sub.sub ≡ sub.add(neg) ≡ add(neg).add(neg)
    F::axiom_eqv_transitive(
        two.mul(x).sub(y).sub(y),
        two.mul(x).sub(y).add(y.neg()),
        two.mul(x).add(y.neg()).add(y.neg()));

    // We already proved: two.mul(x).add(y.neg()).add(y.neg()) ≡ two.mul(x.add(y.neg()))
    // Chain to ensures RHS:
    F::axiom_eqv_transitive(
        two.mul(x).sub(y).sub(y),
        two.mul(x).add(y.neg()).add(y.neg()),
        two.mul(x.add(y.neg())));

    // -- Bridge ensures RHS: two.mul(x.sub(y)) to add form --
    // x.sub(y) ≡ x.add(y.neg())
    lemma_mul_congruence_right::<F>(two, x.sub(y), x.add(y.neg()));
    // two.mul(x.sub(y)) ≡ two.mul(x.add(y.neg()))

    // Final: sub.sub ≡ two.mul(x.add(neg)) ≡ two.mul(x.sub(y))
    F::axiom_eqv_symmetric(two.mul(x.sub(y)), two.mul(x.add(y.neg())));
    F::axiom_eqv_transitive(
        two.mul(x).sub(y).sub(y),
        two.mul(x.add(y.neg())),
        two.mul(x.sub(y)));
}

/// Exchange lemma: (a + b) + (c + d) ≡ (a + c) + (b + d)
proof fn lemma_add_exchange<F: OrderedField>(a: F, b: F, c: F, d: F)
    ensures a.add(b).add(c.add(d)).eqv(a.add(c).add(b.add(d))),
{
    F::axiom_add_associative(a, b, c.add(d));
    F::axiom_add_associative(b, c, d);
    F::axiom_eqv_symmetric(b.add(c).add(d), b.add(c.add(d)));
    lemma_add_congruence_right::<F>(a, b.add(c.add(d)), b.add(c).add(d));
    F::axiom_add_commutative(b, c);
    F::axiom_add_congruence_left(b.add(c), c.add(b), d);
    lemma_add_congruence_right::<F>(a, b.add(c).add(d), c.add(b).add(d));
    F::axiom_add_associative(c, b, d);
    lemma_add_congruence_right::<F>(a, c.add(b).add(d), c.add(b.add(d)));
    F::axiom_add_associative(a, c, b.add(d));
    F::axiom_eqv_transitive(a.add(b).add(c.add(d)), a.add(b.add(c.add(d))), a.add(b.add(c).add(d)));
    F::axiom_eqv_transitive(a.add(b).add(c.add(d)), a.add(b.add(c).add(d)), a.add(c.add(b).add(d)));
    F::axiom_eqv_transitive(a.add(b).add(c.add(d)), a.add(c.add(b).add(d)), a.add(c.add(b.add(d))));
    F::axiom_eqv_symmetric(a.add(c).add(b.add(d)), a.add(c.add(b.add(d))));
    F::axiom_eqv_transitive(a.add(b).add(c.add(d)), a.add(c.add(b.add(d))), a.add(c).add(b.add(d)));
}

/// reflect(p, a, b) satisfies perpendicularity: dot(reflect - p, d) ≡ 0.
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

    // Step 5: sub2(r,p).x ≡ two.mul(proj_x.sub(p.x)) using helper
    let rx_sub_px = sub2(r, p).x;
    F::axiom_eqv_reflexive(two);
    lemma_two_x_sub_y_sub_y::<F>(two, proj_x, p.x);
    // two.mul(proj_x).sub(p.x).sub(p.x) ≡ two.mul(proj_x.sub(p.x))
    // rx_sub_px == two.mul(proj_x).sub(p.x).sub(p.x) structurally
    assert(rx_sub_px == two.mul(proj_x).sub(p.x).sub(p.x));
    // By helper: two.mul(proj_x).sub(p.x).sub(p.x) ≡ two.mul(proj_x.sub(p.x))
    // Since rx_sub_px == that structurally:
    assert(rx_sub_px.eqv(two.mul(proj_x.sub(p.x))));

    let ry_sub_py = sub2(r, p).y;
    lemma_two_x_sub_y_sub_y::<F>(two, proj_y, p.y);
    assert(ry_sub_py == two.mul(proj_y).sub(p.y).sub(p.y));
    assert(ry_sub_py.eqv(two.mul(proj_y.sub(p.y))));

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
    // Helper lemma: a - (b + c) ≡ (a - b) - c
    // Proved inline for proj_x, a.x, pa.x:
    // proj_x - p.x ≡ (proj_x - a.x) - pa.x
    // since p.x ≡ a.x + pa.x (from sub_then_add_cancel + comm)
    assert(proj_x.sub(p.x).eqv(proj_x.sub(a.x).sub(pa.x))) by {
        // pa.x + a.x ≡ p.x
        lemma_sub_then_add_cancel::<F>(p.x, a.x);
        F::axiom_add_commutative(a.x, pa.x);
        // a.x + pa.x ≡ pa.x + a.x ≡ p.x
        F::axiom_eqv_transitive(a.x.add(pa.x), pa.x.add(a.x), p.x);
        // p.x ≡ a.x + pa.x
        F::axiom_eqv_symmetric(a.x.add(pa.x), p.x);
        // proj_x - p.x ≡ proj_x - (a.x + pa.x)
        F::axiom_eqv_reflexive(proj_x);
        lemma_sub_congruence::<F>(proj_x, proj_x, p.x, a.x.add(pa.x));
        // a - (b + c) ≡ (a - b) - c:
        // proj_x - (a.x + pa.x)
        // = proj_x + (-(a.x + pa.x))
        // = proj_x + ((-a.x) + (-pa.x))  [neg_add]
        // = (proj_x + (-a.x)) + (-pa.x)  [assoc]
        // = (proj_x - a.x) + (-pa.x)     [sub_is_add_neg]
        // = (proj_x - a.x) - pa.x        [sub_is_add_neg]
        F::axiom_sub_is_add_neg(proj_x, a.x.add(pa.x));
        verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(a.x, pa.x);
        lemma_add_congruence_right::<F>(proj_x,
            a.x.add(pa.x).neg(), a.x.neg().add(pa.x.neg()));
        // proj_x + (-(a.x+pa.x)) ≡ proj_x + ((-a.x)+(-pa.x))
        F::axiom_add_associative(proj_x, a.x.neg(), pa.x.neg());
        F::axiom_eqv_symmetric(
            proj_x.add(a.x.neg()).add(pa.x.neg()),
            proj_x.add(a.x.neg().add(pa.x.neg())));
        // proj_x + ((-a.x)+(-pa.x)) ≡ (proj_x+(-a.x))+(-pa.x)
        F::axiom_eqv_transitive(
            proj_x.add(a.x.add(pa.x).neg()),
            proj_x.add(a.x.neg().add(pa.x.neg())),
            proj_x.add(a.x.neg()).add(pa.x.neg()));
        // proj_x.sub(p.x) ≡ proj_x + (-(a.x+pa.x)) (from sub_congruence above)
        // Chain: proj_x.sub(p.x) ≡ ... ≡ (proj_x+(-a.x))+(-pa.x)
        F::axiom_sub_is_add_neg(proj_x, p.x);
        F::axiom_eqv_symmetric(proj_x.sub(p.x), proj_x.add(p.x.neg()));
        // We need proj_x.add(p.x.neg()) ≡ proj_x.add(a.x.add(pa.x).neg())
        // Since p.x ≡ a.x + pa.x:
        F::axiom_neg_congruence(p.x, a.x.add(pa.x));
        lemma_add_congruence_right::<F>(proj_x, p.x.neg(), a.x.add(pa.x).neg());
        F::axiom_eqv_transitive(
            proj_x.add(p.x.neg()),
            proj_x.add(a.x.add(pa.x).neg()),
            proj_x.add(a.x.neg()).add(pa.x.neg()));
        F::axiom_eqv_transitive(
            proj_x.sub(p.x),
            proj_x.add(p.x.neg()),
            proj_x.add(a.x.neg()).add(pa.x.neg()));
        // proj_x.add(a.x.neg()) ≡ proj_x.sub(a.x) and pa.x.neg() makes .sub(pa.x)
        F::axiom_eqv_symmetric(proj_x.sub(a.x), proj_x.add(a.x.neg()));
        F::axiom_sub_is_add_neg(proj_x, a.x);
        F::axiom_sub_is_add_neg(proj_x.sub(a.x), pa.x);
        F::axiom_eqv_symmetric(proj_x.sub(a.x).sub(pa.x), proj_x.sub(a.x).add(pa.x.neg()));
        F::axiom_eqv_symmetric(proj_x.sub(a.x), proj_x.add(a.x.neg()));
        F::axiom_add_congruence_left(proj_x.add(a.x.neg()), proj_x.sub(a.x), pa.x.neg());
        F::axiom_eqv_transitive(
            proj_x.add(a.x.neg()).add(pa.x.neg()),
            proj_x.sub(a.x).add(pa.x.neg()),
            proj_x.sub(a.x).sub(pa.x));
        // Final chain
        F::axiom_eqv_transitive(
            proj_x.sub(p.x),
            proj_x.add(a.x.neg()).add(pa.x.neg()),
            proj_x.sub(a.x).sub(pa.x));
    };

    // Same for y
    assert(proj_y.sub(p.y).eqv(proj_y.sub(a.y).sub(pa.y))) by {
        lemma_sub_then_add_cancel::<F>(p.y, a.y);
        F::axiom_add_commutative(a.y, pa.y);
        F::axiom_eqv_transitive(a.y.add(pa.y), pa.y.add(a.y), p.y);
        F::axiom_eqv_symmetric(a.y.add(pa.y), p.y);
        F::axiom_eqv_reflexive(proj_y);
        lemma_sub_congruence::<F>(proj_y, proj_y, p.y, a.y.add(pa.y));
        F::axiom_sub_is_add_neg(proj_y, a.y.add(pa.y));
        verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(a.y, pa.y);
        lemma_add_congruence_right::<F>(proj_y,
            a.y.add(pa.y).neg(), a.y.neg().add(pa.y.neg()));
        F::axiom_add_associative(proj_y, a.y.neg(), pa.y.neg());
        F::axiom_eqv_symmetric(
            proj_y.add(a.y.neg()).add(pa.y.neg()),
            proj_y.add(a.y.neg().add(pa.y.neg())));
        F::axiom_eqv_transitive(
            proj_y.add(a.y.add(pa.y).neg()),
            proj_y.add(a.y.neg().add(pa.y.neg())),
            proj_y.add(a.y.neg()).add(pa.y.neg()));
        F::axiom_sub_is_add_neg(proj_y, p.y);
        F::axiom_eqv_symmetric(proj_y.sub(p.y), proj_y.add(p.y.neg()));
        F::axiom_neg_congruence(p.y, a.y.add(pa.y));
        lemma_add_congruence_right::<F>(proj_y, p.y.neg(), a.y.add(pa.y).neg());
        F::axiom_eqv_transitive(
            proj_y.add(p.y.neg()),
            proj_y.add(a.y.add(pa.y).neg()),
            proj_y.add(a.y.neg()).add(pa.y.neg()));
        F::axiom_eqv_transitive(
            proj_y.sub(p.y),
            proj_y.add(p.y.neg()),
            proj_y.add(a.y.neg()).add(pa.y.neg()));
        F::axiom_sub_is_add_neg(proj_y, a.y);
        F::axiom_sub_is_add_neg(proj_y.sub(a.y), pa.y);
        F::axiom_eqv_symmetric(proj_y.sub(a.y).sub(pa.y), proj_y.sub(a.y).add(pa.y.neg()));
        F::axiom_eqv_symmetric(proj_y.sub(a.y), proj_y.add(a.y.neg()));
        F::axiom_add_congruence_left(proj_y.add(a.y.neg()), proj_y.sub(a.y), pa.y.neg());
        F::axiom_eqv_transitive(
            proj_y.add(a.y.neg()).add(pa.y.neg()),
            proj_y.sub(a.y).add(pa.y.neg()),
            proj_y.sub(a.y).sub(pa.y));
        F::axiom_eqv_transitive(
            proj_y.sub(p.y),
            proj_y.add(a.y.neg()).add(pa.y.neg()),
            proj_y.sub(a.y).sub(pa.y));
    };

    // Step 7: dot(proj-p, d) ≡ dot(proj-a, d) - dot(pa, d)
    // i.e. (proj_x-p.x)*dx + (proj_y-p.y)*dy ≡ ((proj_x-a.x)*dx + (proj_y-a.y)*dy) - (pa.x*dx + pa.y*dy)
    //
    // Key identity: proj_x - p.x ≡ (proj_x - a.x) - pa.x
    // because pa.x = p.x - a.x, so a.x + pa.x ≡ p.x
    //
    // Then (A - B)*C ≡ A*C - B*C by distribution, and combining gives the result.
    //
    // Rather than prove this complex chain, use a helper:
    // dot(X - Y, d) = dot(X, d) - dot(Y, d) for any X, Y.
    // Here X = proj - a, Y = pa, and proj - p = (proj - a) - pa.
    //
    // Actually the simplest approach: show proj_x - p.x ≡ (proj_x - a.x) - pa.x
    // by: pa.x + a.x ≡ p.x (sub_then_add_cancel), so p.x ≡ pa.x + a.x (symmetric).
    // Then proj_x - p.x ≡ proj_x - (pa.x + a.x).
    // And a - (b + c) ≡ (a - b) - c (standard identity).
    // Swap: proj_x - (pa.x + a.x) = proj_x - (a.x + pa.x) by add commutativity.
    // Then proj_x - (a.x + pa.x) ≡ (proj_x - a.x) - pa.x.

    // Let me write a helper for a - (b + c) ≡ (a - b) - c
    // and use it here.
    assert(dot_proj_p_d.eqv(dot_proj_a_d.sub(dot_pad))) by {
        // Step 7b: (A-B)*C ≡ A*C - B*C for each component
        // x: (proj_x.sub(a.x).sub(pa.x))*dx ≡ proj_x.sub(a.x)*dx - pa.x*dx
        F::axiom_sub_is_add_neg(proj_x.sub(a.x), pa.x);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(
            proj_x.sub(a.x), pa.x.neg(), dx);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_left::<F>(pa.x, dx);
        lemma_add_congruence_right::<F>(proj_x.sub(a.x).mul(dx),
            pa.x.neg().mul(dx), pa.x.mul(dx).neg());
        // (proj_x.sub(a.x) + (-pa.x))*dx ≡ proj_x.sub(a.x)*dx + (-pa.x)*dx ≡ ... + (-(pa.x*dx))
        F::axiom_eqv_transitive(
            proj_x.sub(a.x).add(pa.x.neg()).mul(dx),
            proj_x.sub(a.x).mul(dx).add(pa.x.neg().mul(dx)),
            proj_x.sub(a.x).mul(dx).add(pa.x.mul(dx).neg()));
        // proj_x.sub(a.x).sub(pa.x) ≡ proj_x.sub(a.x).add(pa.x.neg()) by sub_is_add_neg
        F::axiom_mul_congruence_left(proj_x.sub(a.x).sub(pa.x), proj_x.sub(a.x).add(pa.x.neg()), dx);
        F::axiom_eqv_transitive(
            proj_x.sub(a.x).sub(pa.x).mul(dx),
            proj_x.sub(a.x).add(pa.x.neg()).mul(dx),
            proj_x.sub(a.x).mul(dx).add(pa.x.mul(dx).neg()));

        // y: same
        F::axiom_sub_is_add_neg(proj_y.sub(a.y), pa.y);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_distributes_right::<F>(
            proj_y.sub(a.y), pa.y.neg(), dy);
        verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_left::<F>(pa.y, dy);
        lemma_add_congruence_right::<F>(proj_y.sub(a.y).mul(dy),
            pa.y.neg().mul(dy), pa.y.mul(dy).neg());
        F::axiom_eqv_transitive(
            proj_y.sub(a.y).add(pa.y.neg()).mul(dy),
            proj_y.sub(a.y).mul(dy).add(pa.y.neg().mul(dy)),
            proj_y.sub(a.y).mul(dy).add(pa.y.mul(dy).neg()));
        F::axiom_mul_congruence_left(proj_y.sub(a.y).sub(pa.y), proj_y.sub(a.y).add(pa.y.neg()), dy);
        F::axiom_eqv_transitive(
            proj_y.sub(a.y).sub(pa.y).mul(dy),
            proj_y.sub(a.y).add(pa.y.neg()).mul(dy),
            proj_y.sub(a.y).mul(dy).add(pa.y.mul(dy).neg()));

        // Step 7c: congruence from step 7a
        F::axiom_mul_congruence_left(proj_x.sub(p.x), proj_x.sub(a.x).sub(pa.x), dx);
        F::axiom_mul_congruence_left(proj_y.sub(p.y), proj_y.sub(a.y).sub(pa.y), dy);

        // dot_proj_p_d = (proj_x-p.x)*dx + (proj_y-p.y)*dy
        //              ≡ (proj_x-a.x-pa.x)*dx + (proj_y-a.y-pa.y)*dy     [7a congruence]
        //              ≡ (A_x + (-B_x)) + (A_y + (-B_y))                  [7b distribution]
        // where A_x = proj_x.sub(a.x)*dx, B_x = pa.x*dx, A_y = ..., B_y = ...
        lemma_add_congruence::<F>(
            proj_x.sub(p.x).mul(dx), proj_x.sub(a.x).sub(pa.x).mul(dx),
            proj_y.sub(p.y).mul(dy), proj_y.sub(a.y).sub(pa.y).mul(dy));
        lemma_add_congruence::<F>(
            proj_x.sub(a.x).sub(pa.x).mul(dx),
            proj_x.sub(a.x).mul(dx).add(pa.x.mul(dx).neg()),
            proj_y.sub(a.y).sub(pa.y).mul(dy),
            proj_y.sub(a.y).mul(dy).add(pa.y.mul(dy).neg()));
        F::axiom_eqv_transitive(
            dot_proj_p_d,
            proj_x.sub(a.x).sub(pa.x).mul(dx).add(proj_y.sub(a.y).sub(pa.y).mul(dy)),
            proj_x.sub(a.x).mul(dx).add(pa.x.mul(dx).neg()).add(
                proj_y.sub(a.y).mul(dy).add(pa.y.mul(dy).neg())));

        // Step 7d: rearrange (A+(-B)) + (C+(-D)) ≡ (A+C) + ((-B)+(-D)) ≡ (A+C) - (B+D)
        let ax = proj_x.sub(a.x).mul(dx);
        let bx_neg = pa.x.mul(dx).neg();
        let ay = proj_y.sub(a.y).mul(dy);
        let by_neg = pa.y.mul(dy).neg();
        // Use exchange lemma: (ax + bx_neg) + (ay + by_neg) ≡ (ax + ay) + (bx_neg + by_neg)
        lemma_add_exchange::<F>(ax, bx_neg, ay, by_neg);
        // (bx_neg + by_neg) = (-(pa.x*dx)) + (-(pa.y*dy)) ≡ -(pa.x*dx + pa.y*dy) by neg_add
        verus_algebra::lemmas::additive_group_lemmas::lemma_neg_add::<F>(pa.x.mul(dx), pa.y.mul(dy));
        F::axiom_eqv_symmetric(bx_neg.add(by_neg), pa.x.mul(dx).add(pa.y.mul(dy)).neg());
        lemma_add_congruence_right::<F>(ax.add(ay), bx_neg.add(by_neg),
            pa.x.mul(dx).add(pa.y.mul(dy)).neg());
        // (ax+ay) + (-(dot_pad)) = (ax+ay) - dot_pad = dot_proj_a_d - dot_pad
        F::axiom_eqv_transitive(
            ax.add(bx_neg).add(ay.add(by_neg)),
            ax.add(ay).add(bx_neg.add(by_neg)),
            ax.add(ay).add(dot_pad.neg()));
        F::axiom_sub_is_add_neg(dot_proj_a_d, dot_pad);
        F::axiom_eqv_symmetric(dot_proj_a_d.sub(dot_pad), dot_proj_a_d.add(dot_pad.neg()));
        F::axiom_eqv_transitive(
            ax.add(bx_neg).add(ay.add(by_neg)),
            ax.add(ay).add(dot_pad.neg()),
            dot_proj_a_d.sub(dot_pad));
        // Connect dot_proj_p_d to ax.add(bx_neg).add(ay.add(by_neg)):
        // dot_proj_p_d ≡ ... ≡ ax.add(bx_neg).add(ay.add(by_neg))
        // (from step 7c chaining)
        F::axiom_eqv_transitive(
            dot_proj_p_d,
            ax.add(bx_neg).add(ay.add(by_neg)),
            dot_proj_a_d.sub(dot_pad));
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

/// reflect(p, a, b) satisfies midpoint-on-axis:
/// la*(px+rx) + lb*(py+ry) + 2*lc ≡ 0
/// where line = line2_from_points(a, b) and r = reflect(p, a, b).
///
/// The midpoint of p and r is the projection proj = a + t*d, which lies on line(a,b).
/// px + rx = 2*proj_x, py + ry = 2*proj_y, so the check is 2*line_eval(line, proj) ≡ 0.
pub proof fn lemma_reflect_midpoint_on_axis<F: OrderedField>(
    p: Point2<F>, a: Point2<F>, b: Point2<F>,
)
    requires
        !sub2(b, a).x.mul(sub2(b, a).x).add(sub2(b, a).y.mul(sub2(b, a).y)).eqv(F::zero()),
    ensures ({
        let d = sub2(b, a);
        let r = reflect_point_across_line(p, a, b);
        let line = line2_from_points(a, b);
        let two = F::one().add(F::one());
        line.a.mul(p.x.add(r.x)).add(line.b.mul(p.y.add(r.y))).add(two.mul(line.c)).eqv(F::zero())
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
    let proj_x = a.x.add(t.mul(dx));
    let proj_y = a.y.add(t.mul(dy));
    let r = reflect_point_across_line(p, a, b);
    let line = line2_from_points(a, b);
    let la = line.a; // = -dy = -(by - ay) = ay - by
    let lb = line.b; // = dx = bx - ax

    // Key fact 1: p.x + r.x ≡ two * proj_x
    // r.x = two*proj_x - p.x, so p.x + r.x = p.x + two*proj_x - p.x = two*proj_x
    assert(p.x.add(r.x).eqv(two.mul(proj_x))) by {
        // r.x == two.mul(proj_x).sub(p.x)
        assert(r.x == two.mul(proj_x).sub(p.x));
        // p.x + (two*proj_x - p.x) = p.x + two*proj_x + (-p.x)
        //                           = two*proj_x + (p.x + (-p.x))  [exchange]
        //                           = two*proj_x + 0 = two*proj_x
        F::axiom_sub_is_add_neg(two.mul(proj_x), p.x);
        // r.x ≡ two*proj_x + (-p.x) (via sub_is_add_neg)
        lemma_add_congruence_right::<F>(p.x, r.x, two.mul(proj_x).add(p.x.neg()));
        // p.x + r.x ≡ p.x + (two*proj_x + (-p.x))
        F::axiom_add_commutative(p.x, two.mul(proj_x).add(p.x.neg()));
        // ≡ (two*proj_x + (-p.x)) + p.x
        F::axiom_add_associative(two.mul(proj_x), p.x.neg(), p.x);
        F::axiom_eqv_symmetric(
            two.mul(proj_x).add(p.x.neg()).add(p.x),
            two.mul(proj_x).add(p.x.neg().add(p.x)));
        // two*proj_x + ((-p.x) + p.x)
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_inverse_left::<F>(p.x);
        lemma_add_congruence_right::<F>(two.mul(proj_x), p.x.neg().add(p.x), F::zero());
        // two*proj_x + 0 ≡ two*proj_x
        F::axiom_add_commutative(two.mul(proj_x), F::zero());
        lemma_add_zero_left::<F>(two.mul(proj_x));
        F::axiom_eqv_transitive(
            two.mul(proj_x).add(F::zero()),
            F::zero().add(two.mul(proj_x)),
            two.mul(proj_x));
        // Chain: p.x + r.x ≡ p.x + (two*proj_x + (-p.x))
        //                   ≡ (two*proj_x + (-p.x)) + p.x
        //                   ≡ two*proj_x + ((-p.x) + p.x)
        //                   ≡ two*proj_x + 0 ≡ two*proj_x
        F::axiom_eqv_transitive(p.x.add(r.x),
            p.x.add(two.mul(proj_x).add(p.x.neg())),
            two.mul(proj_x).add(p.x.neg()).add(p.x));
        F::axiom_eqv_transitive(p.x.add(r.x),
            two.mul(proj_x).add(p.x.neg()).add(p.x),
            two.mul(proj_x).add(p.x.neg().add(p.x)));
        F::axiom_eqv_transitive(p.x.add(r.x),
            two.mul(proj_x).add(p.x.neg().add(p.x)),
            two.mul(proj_x).add(F::zero()));
        F::axiom_eqv_transitive(p.x.add(r.x),
            two.mul(proj_x).add(F::zero()),
            two.mul(proj_x));
    };

    // Key fact 2: p.y + r.y ≡ two * proj_y (same argument)
    assert(p.y.add(r.y).eqv(two.mul(proj_y))) by {
        assert(r.y == two.mul(proj_y).sub(p.y));
        F::axiom_sub_is_add_neg(two.mul(proj_y), p.y);
        lemma_add_congruence_right::<F>(p.y, r.y, two.mul(proj_y).add(p.y.neg()));
        F::axiom_add_commutative(p.y, two.mul(proj_y).add(p.y.neg()));
        F::axiom_add_associative(two.mul(proj_y), p.y.neg(), p.y);
        F::axiom_eqv_symmetric(
            two.mul(proj_y).add(p.y.neg()).add(p.y),
            two.mul(proj_y).add(p.y.neg().add(p.y)));
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_inverse_left::<F>(p.y);
        lemma_add_congruence_right::<F>(two.mul(proj_y), p.y.neg().add(p.y), F::zero());
        F::axiom_add_commutative(two.mul(proj_y), F::zero());
        lemma_add_zero_left::<F>(two.mul(proj_y));
        F::axiom_eqv_transitive(
            two.mul(proj_y).add(F::zero()),
            F::zero().add(two.mul(proj_y)),
            two.mul(proj_y));
        F::axiom_eqv_transitive(p.y.add(r.y),
            p.y.add(two.mul(proj_y).add(p.y.neg())),
            two.mul(proj_y).add(p.y.neg()).add(p.y));
        F::axiom_eqv_transitive(p.y.add(r.y),
            two.mul(proj_y).add(p.y.neg()).add(p.y),
            two.mul(proj_y).add(p.y.neg().add(p.y)));
        F::axiom_eqv_transitive(p.y.add(r.y),
            two.mul(proj_y).add(p.y.neg().add(p.y)),
            two.mul(proj_y).add(F::zero()));
        F::axiom_eqv_transitive(p.y.add(r.y),
            two.mul(proj_y).add(F::zero()),
            two.mul(proj_y));
    };

    // Key fact 3: la*(two*proj_x) + lb*(two*proj_y) + two*lc ≡ two*(la*proj_x + lb*proj_y + lc)
    //           = two * line_eval(line, proj)
    // By distributing: la*(two*X) = two*(la*X) by commutative+assoc, then factor out two.
    // line_eval(line, proj) = la*proj_x + lb*proj_y + lc

    // Key fact 4: proj is on line(a,b), so line_eval(line, proj) ≡ 0
    // line_eval(line, a) = la*ax + lb*ay + lc = 0 by construction
    // proj_x = ax + t*dx, proj_y = ay + t*dy
    // line_eval(line, proj) = la*(ax + t*dx) + lb*(ay + t*dy) + lc
    //   = (la*ax + lb*ay + lc) + t*(la*dx + lb*dy)
    //   = 0 + t*(-dy*dx + dx*dy) = t*0 = 0
    //
    // la*dx + lb*dy = (-dy)*dx + dx*dy: need to show this ≡ 0
    // (-dy)*dx ≡ -(dy*dx) by mul_neg_left
    // -(dy*dx) + dx*dy: by commutativity dy*dx = dx*dy, so -(dx*dy) + dx*dy = 0

    // Step: la*dx + lb*dy ≡ 0
    assert(la.mul(dx).add(lb.mul(dy)).eqv(F::zero())) by {
        // la = -(by - ay) = -dy (structurally from line2_from_points)
        // lb = bx - ax = dx
        // la*dx = (-dy)*dx ≡ -(dy*dx) by mul_neg_left
        verus_algebra::lemmas::ring_lemmas::lemma_mul_neg_left::<F>(dy, dx);
        // lb*dy = dx*dy
        // -(dy*dx) + dx*dy: dy*dx ≡ dx*dy by commutativity
        F::axiom_mul_commutative(dy, dx);
        // -(dy*dx) ≡ -(dx*dy)
        F::axiom_neg_congruence(dy.mul(dx), dx.mul(dy));
        F::axiom_eqv_transitive(la.mul(dx), dy.mul(dx).neg(), dx.mul(dy).neg());
        // lb == dx structurally, so lb*dy == dx*dy
        // -(dx*dy) + dx*dy ≡ 0 by add_inverse_left
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_inverse_left::<F>(dx.mul(dy));
        // la*dx ≡ -(dx*dy), lb*dy == dx*dy, so need eqv for both
        F::axiom_eqv_reflexive(lb.mul(dy));
        lemma_add_congruence::<F>(la.mul(dx), dx.mul(dy).neg(), lb.mul(dy), lb.mul(dy));
        F::axiom_eqv_transitive(
            la.mul(dx).add(lb.mul(dy)),
            dx.mul(dy).neg().add(lb.mul(dy)),
            F::zero());
    };

    // Step: line_eval(line, proj) ≡ 0
    // line_eval = la*proj_x + lb*proj_y + lc
    //           = la*(ax + t*dx) + lb*(ay + t*dy) + lc
    //           = la*ax + la*t*dx + lb*ay + lb*t*dy + lc
    //           = (la*ax + lb*ay + lc) + t*(la*dx + lb*dy)
    //           = line_eval(line, a) + t*0
    //           = 0 + 0 = 0
    // line_eval(line, a) = 0 by construction of line2_from_points:
    // lc = -(la*ax + lb*ay), so la*ax + lb*ay + lc = la*ax + lb*ay - (la*ax + lb*ay) = 0
    let line_eval_a = la.mul(a.x).add(lb.mul(a.y)).add(line.c);
    assert(line_eval_a.eqv(F::zero())) by {
        // lc = -(la*ax + lb*ay) by definition of line2_from_points
        // la*ax + lb*ay + lc = la*ax + lb*ay + (-(la*ax + lb*ay)) = 0
        F::axiom_add_commutative(la.mul(a.x).add(lb.mul(a.y)), line.c);
        // lc + (la*ax + lb*ay) ≡ -(la*ax+lb*ay) + (la*ax+lb*ay) ≡ 0
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_inverse_left::<F>(
            la.mul(a.x).add(lb.mul(a.y)));
        F::axiom_eqv_transitive(
            line_eval_a,
            line.c.add(la.mul(a.x).add(lb.mul(a.y))),
            F::zero());
    };

    // Step: line_eval(line, proj) ≡ line_eval_a + t*(la*dx + lb*dy) ≡ 0 + t*0 ≡ 0
    // By distribution: la*(ax + t*dx) = la*ax + la*(t*dx) = la*ax + t*(la*dx)
    // Similarly for lb*(ay + t*dy) = lb*ay + t*(lb*dy)
    // So line_eval(line, proj) = (la*ax + lb*ay + lc) + t*(la*dx + lb*dy)
    //                          = line_eval_a + t*(la*dx + lb*dy)
    let line_eval_proj = la.mul(proj_x).add(lb.mul(proj_y)).add(line.c);
    assert(line_eval_proj.eqv(F::zero())) by {
        // Distribute: la*(ax + t*dx) = la*ax + la*t*dx
        F::axiom_mul_distributes_left(la, a.x, t.mul(dx));
        F::axiom_mul_distributes_left(lb, a.y, t.mul(dy));
        // la*(t*dx) = (la*t)*dx... but we need t*(la*dx)
        // la*t ≡ t*la by commutativity, then (t*la)*dx = t*(la*dx) by assoc
        // Actually let's just use: la*proj_x + lb*proj_y + lc
        //   ≡ (la*ax + la*(t*dx)) + (lb*ay + lb*(t*dy)) + lc
        //   ≡ (la*ax + lb*ay + lc) + (la*(t*dx) + lb*(t*dy))
        //   = line_eval_a + (la*t*dx + lb*t*dy)
        //   = line_eval_a + t*(la*dx + lb*dy)    [factor t out]
        //   ≡ 0 + t*0 = 0

        // la*t*dx = t*(la*dx): la*(t*dx) = (la*t)*dx = (t*la)*dx = t*(la*dx)
        F::axiom_mul_associative(la, t, dx);
        F::axiom_mul_commutative(la, t);
        F::axiom_mul_congruence_left(la.mul(t), t.mul(la), dx);
        F::axiom_mul_associative(t, la, dx);
        F::axiom_eqv_transitive(la.mul(t).mul(dx), t.mul(la).mul(dx), t.mul(la.mul(dx)));
        F::axiom_eqv_symmetric(la.mul(t).mul(dx), la.mul(t.mul(dx)));
        F::axiom_eqv_transitive(la.mul(t.mul(dx)), la.mul(t).mul(dx), t.mul(la.mul(dx)));

        // lb*t*dy = t*(lb*dy) similarly
        F::axiom_mul_associative(lb, t, dy);
        F::axiom_mul_commutative(lb, t);
        F::axiom_mul_congruence_left(lb.mul(t), t.mul(lb), dy);
        F::axiom_mul_associative(t, lb, dy);
        F::axiom_eqv_transitive(lb.mul(t).mul(dy), t.mul(lb).mul(dy), t.mul(lb.mul(dy)));
        F::axiom_eqv_symmetric(lb.mul(t).mul(dy), lb.mul(t.mul(dy)));
        F::axiom_eqv_transitive(lb.mul(t.mul(dy)), lb.mul(t).mul(dy), t.mul(lb.mul(dy)));

        // t*(la*dx) + t*(lb*dy) ≡ t*(la*dx + lb*dy) by distribution
        lemma_add_congruence::<F>(
            la.mul(t.mul(dx)), t.mul(la.mul(dx)),
            lb.mul(t.mul(dy)), t.mul(lb.mul(dy)));
        F::axiom_mul_distributes_left(t, la.mul(dx), lb.mul(dy));
        F::axiom_eqv_symmetric(
            t.mul(la.mul(dx).add(lb.mul(dy))),
            t.mul(la.mul(dx)).add(t.mul(lb.mul(dy))));
        F::axiom_eqv_transitive(
            la.mul(t.mul(dx)).add(lb.mul(t.mul(dy))),
            t.mul(la.mul(dx)).add(t.mul(lb.mul(dy))),
            t.mul(la.mul(dx).add(lb.mul(dy))));

        // t*(la*dx + lb*dy) ≡ t*0 ≡ 0
        lemma_mul_congruence_right::<F>(t, la.mul(dx).add(lb.mul(dy)), F::zero());
        F::axiom_mul_commutative(t, F::zero());
        lemma_mul_zero_left::<F>(t);
        F::axiom_eqv_transitive(t.mul(la.mul(dx).add(lb.mul(dy))), t.mul(F::zero()), F::zero().mul(t));
        F::axiom_eqv_transitive(t.mul(la.mul(dx).add(lb.mul(dy))), F::zero().mul(t), F::zero());
        F::axiom_eqv_transitive(
            la.mul(t.mul(dx)).add(lb.mul(t.mul(dy))),
            t.mul(la.mul(dx).add(lb.mul(dy))),
            F::zero());

        // line_eval(line, proj):
        // la*proj_x + lb*proj_y
        //   = la*(ax + t*dx) + lb*(ay + t*dy)
        //   ≡ (la*ax + la*(t*dx)) + (lb*ay + lb*(t*dy))  [distribute]
        //   ≡ (la*ax + lb*ay) + (la*(t*dx) + lb*(t*dy))  [exchange]
        lemma_add_congruence::<F>(
            la.mul(proj_x), la.mul(a.x).add(la.mul(t.mul(dx))),
            lb.mul(proj_y), lb.mul(a.y).add(lb.mul(t.mul(dy))));
        lemma_add_exchange::<F>(la.mul(a.x), la.mul(t.mul(dx)), lb.mul(a.y), lb.mul(t.mul(dy)));
        F::axiom_eqv_transitive(
            la.mul(proj_x).add(lb.mul(proj_y)),
            la.mul(a.x).add(la.mul(t.mul(dx))).add(lb.mul(a.y).add(lb.mul(t.mul(dy)))),
            la.mul(a.x).add(lb.mul(a.y)).add(la.mul(t.mul(dx)).add(lb.mul(t.mul(dy)))));

        // + lc:
        // ((la*ax + lb*ay) + (la*t*dx + lb*t*dy)) + lc
        // = (la*ax + lb*ay + lc) + (la*t*dx + lb*t*dy)   [assoc]
        // = line_eval_a + (la*t*dx + lb*t*dy) ≡ 0 + 0 ≡ 0
        F::axiom_eqv_reflexive(line.c);
        lemma_add_congruence::<F>(
            la.mul(proj_x).add(lb.mul(proj_y)),
            la.mul(a.x).add(lb.mul(a.y)).add(la.mul(t.mul(dx)).add(lb.mul(t.mul(dy)))),
            line.c, line.c);
        F::axiom_eqv_reflexive(line.c);
        F::axiom_add_associative(
            la.mul(a.x).add(lb.mul(a.y)),
            la.mul(t.mul(dx)).add(lb.mul(t.mul(dy))),
            line.c);
        F::axiom_add_commutative(la.mul(t.mul(dx)).add(lb.mul(t.mul(dy))), line.c);
        F::axiom_add_congruence_left(
            la.mul(t.mul(dx)).add(lb.mul(t.mul(dy))).add(line.c),
            line.c.add(la.mul(t.mul(dx)).add(lb.mul(t.mul(dy)))),
            la.mul(a.x).add(lb.mul(a.y)));
        // ((la*ax+lb*ay) + T) + lc where T = la*t*dx + lb*t*dy ≡ 0
        // by exchange: = (la*ax+lb*ay+lc) + T = line_eval_a + T ≡ 0 + 0 = 0
        // Use assoc: ((A+B)+T)+lc = (A+B)+(T+lc) = (A+B)+(lc+T) [comm] = ((A+B)+lc)+T [assoc]
        // Actually: use exchange on (la*ax+lb*ay, T, lc) — but exchange is 4-arg.
        // Simpler: ((la*ax+lb*ay) + T) + lc
        //  = (la*ax+lb*ay) + (T + lc)   [assoc]
        //  = (la*ax+lb*ay) + (lc + T)   [comm T,lc]
        //  = ((la*ax+lb*ay) + lc) + T   [assoc back]
        //  = line_eval_a + T
        let AB = la.mul(a.x).add(lb.mul(a.y));
        let T = la.mul(t.mul(dx)).add(lb.mul(t.mul(dy)));
        // Rearrange: (AB + T) + lc ≡ (AB + lc) + T
        // by assoc: (AB+T)+lc ≡ AB+(T+lc)
        F::axiom_add_associative(AB, T, line.c);
        F::axiom_eqv_symmetric(AB.add(T).add(line.c), AB.add(T.add(line.c)));
        // comm: T+lc ≡ lc+T
        F::axiom_add_commutative(T, line.c);
        lemma_add_congruence_right::<F>(AB, T.add(line.c), line.c.add(T));
        // assoc back: AB+(lc+T) ≡ (AB+lc)+T
        F::axiom_add_associative(AB, line.c, T);
        F::axiom_eqv_symmetric(AB.add(line.c).add(T), AB.add(line.c.add(T)));
        // Chain: (AB+T)+lc ≡ AB+(T+lc) ≡ AB+(lc+T) ≡ (AB+lc)+T
        F::axiom_eqv_transitive(AB.add(T.add(line.c)), AB.add(line.c.add(T)), AB.add(line.c).add(T));
        F::axiom_eqv_transitive(AB.add(T).add(line.c), AB.add(T.add(line.c)), AB.add(line.c).add(T));

        // (AB+lc) ≡ line_eval_a ≡ 0, and T ≡ 0
        // So (AB+lc) + T ≡ 0 + 0 ≡ 0
        lemma_add_congruence::<F>(AB.add(line.c), F::zero(), T, F::zero());
        lemma_add_zero_left::<F>(F::zero());
        F::axiom_eqv_transitive(AB.add(line.c).add(T), F::zero().add(F::zero()), F::zero());
        F::axiom_eqv_transitive(AB.add(T).add(line.c), AB.add(line.c).add(T), F::zero());

        // la*proj_x + lb*proj_y ≡ AB + T (from distribution + exchange above)
        // So la*proj_x+lb*proj_y+lc ≡ AB+T+lc ≡ 0
        F::axiom_eqv_reflexive(line.c);
        lemma_add_congruence::<F>(
            la.mul(proj_x).add(lb.mul(proj_y)), AB.add(T),
            line.c, line.c);
        // line_eval_proj = la*proj_x+lb*proj_y+lc ≡ (AB+T)+lc ≡ 0
        F::axiom_eqv_transitive(
            la.mul(proj_x).add(lb.mul(proj_y)).add(line.c),
            AB.add(T).add(line.c),
            F::zero());
    };

    // Now: la*(px+rx) + lb*(py+ry) + two*lc
    //    ≡ la*(two*proj_x) + lb*(two*proj_y) + two*lc   [by facts 1,2]
    //    = two*(la*proj_x) + two*(lb*proj_y) + two*lc    [factor]
    //    = two*(la*proj_x + lb*proj_y + lc)              [factor]
    //    = two * line_eval_proj ≡ two * 0 ≡ 0
    // Congruence from facts 1,2:
    // la*(px+rx) ≡ la*(two*proj_x) by congruence
    lemma_mul_congruence_right::<F>(la, p.x.add(r.x), two.mul(proj_x));
    // la*(two*proj_x) = (la*two)*proj_x = (two*la)*proj_x = two*(la*proj_x)
    F::axiom_mul_associative(la, two, proj_x);
    F::axiom_mul_commutative(la, two);
    F::axiom_mul_congruence_left(la.mul(two), two.mul(la), proj_x);
    F::axiom_mul_associative(two, la, proj_x);
    F::axiom_eqv_transitive(la.mul(two).mul(proj_x), two.mul(la).mul(proj_x), two.mul(la.mul(proj_x)));
    F::axiom_eqv_symmetric(la.mul(two).mul(proj_x), la.mul(two.mul(proj_x)));
    F::axiom_eqv_transitive(la.mul(two.mul(proj_x)), la.mul(two).mul(proj_x), two.mul(la.mul(proj_x)));
    F::axiom_eqv_transitive(la.mul(p.x.add(r.x)), la.mul(two.mul(proj_x)), two.mul(la.mul(proj_x)));

    // lb*(py+ry) ≡ two*(lb*proj_y) — same argument
    lemma_mul_congruence_right::<F>(lb, p.y.add(r.y), two.mul(proj_y));
    F::axiom_mul_associative(lb, two, proj_y);
    F::axiom_mul_commutative(lb, two);
    F::axiom_mul_congruence_left(lb.mul(two), two.mul(lb), proj_y);
    F::axiom_mul_associative(two, lb, proj_y);
    F::axiom_eqv_transitive(lb.mul(two).mul(proj_y), two.mul(lb).mul(proj_y), two.mul(lb.mul(proj_y)));
    F::axiom_eqv_symmetric(lb.mul(two).mul(proj_y), lb.mul(two.mul(proj_y)));
    F::axiom_eqv_transitive(lb.mul(two.mul(proj_y)), lb.mul(two).mul(proj_y), two.mul(lb.mul(proj_y)));
    F::axiom_eqv_transitive(lb.mul(p.y.add(r.y)), lb.mul(two.mul(proj_y)), two.mul(lb.mul(proj_y)));

    // Now: la*(px+rx) + lb*(py+ry) + two*lc
    //    ≡ two*(la*proj_x) + two*(lb*proj_y) + two*lc
    //    = two*(la*proj_x + lb*proj_y + lc)  [factor]
    //    = two*line_eval_proj ≡ two*0 ≡ 0
    lemma_add_congruence::<F>(
        la.mul(p.x.add(r.x)), two.mul(la.mul(proj_x)),
        lb.mul(p.y.add(r.y)), two.mul(lb.mul(proj_y)));
    // two*A + two*B = two*(A+B) by distribution
    F::axiom_mul_distributes_left(two, la.mul(proj_x), lb.mul(proj_y));
    F::axiom_eqv_symmetric(
        two.mul(la.mul(proj_x).add(lb.mul(proj_y))),
        two.mul(la.mul(proj_x)).add(two.mul(lb.mul(proj_y))));
    F::axiom_eqv_transitive(
        la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y))),
        two.mul(la.mul(proj_x)).add(two.mul(lb.mul(proj_y))),
        two.mul(la.mul(proj_x).add(lb.mul(proj_y))));
    // + two*lc:
    F::axiom_eqv_reflexive(two.mul(line.c));
    lemma_add_congruence::<F>(
        la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y))),
        two.mul(la.mul(proj_x).add(lb.mul(proj_y))),
        two.mul(line.c), two.mul(line.c));
    // two*(A+B) + two*C = two*(A+B+C)
    F::axiom_mul_distributes_left(two, la.mul(proj_x).add(lb.mul(proj_y)), line.c);
    F::axiom_eqv_symmetric(
        two.mul(la.mul(proj_x).add(lb.mul(proj_y)).add(line.c)),
        two.mul(la.mul(proj_x).add(lb.mul(proj_y))).add(two.mul(line.c)));
    F::axiom_eqv_transitive(
        la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y))).add(two.mul(line.c)),
        two.mul(la.mul(proj_x).add(lb.mul(proj_y))).add(two.mul(line.c)),
        two.mul(la.mul(proj_x).add(lb.mul(proj_y)).add(line.c)));
    // two * line_eval_proj ≡ two * 0 ≡ 0
    lemma_mul_congruence_right::<F>(two, line_eval_proj, F::zero());
    F::axiom_mul_commutative(two, F::zero());
    lemma_mul_zero_left::<F>(two);
    F::axiom_eqv_transitive(two.mul(line_eval_proj), two.mul(F::zero()), F::zero().mul(two));
    F::axiom_eqv_transitive(two.mul(line_eval_proj), F::zero().mul(two), F::zero());
    F::axiom_eqv_transitive(
        la.mul(p.x.add(r.x)).add(lb.mul(p.y.add(r.y))).add(two.mul(line.c)),
        two.mul(line_eval_proj),
        F::zero());
}

/// Symmetric decomposition backward direction:
/// If dot(q-p, d) ≡ 0 (perpendicularity) and midpoint(p,q) on line(a,b) (midpoint-on-axis),
/// and dot(d,d) ≢ 0 (non-degenerate), then q ≡ reflect(p, a, b).
///
/// Proof: reflect(p,a,b) satisfies both conditions (forward lemmas).
/// Both q and reflect satisfy the same 2×2 linear system over (q-r).
/// By uniqueness (lemma_2x2_trivial_solution), q ≡ reflect.
pub proof fn lemma_symmetric_decomposition_backward<F: OrderedField>(
    p: Point2<F>, q: Point2<F>, a: Point2<F>, b: Point2<F>,
)
    requires ({
        let d = sub2(b, a);
        let dot_dd = d.x.mul(d.x).add(d.y.mul(d.y));
        let line = line2_from_points(a, b);
        let two = F::one().add(F::one());
        // Non-degeneracy
        &&& !dot_dd.eqv(F::zero())
        // Perpendicularity: dot(q - p, d) ≡ 0
        &&& sub2(q, p).x.mul(d.x).add(sub2(q, p).y.mul(d.y)).eqv(F::zero())
        // Midpoint on axis (scaled by 2)
        &&& line.a.mul(p.x.add(q.x)).add(line.b.mul(p.y.add(q.y))).add(two.mul(line.c)).eqv(F::zero())
    }),
    ensures
        q.eqv(reflect_point_across_line(p, a, b)),
{
    let d = sub2(b, a);
    let dx = d.x;
    let dy = d.y;
    let r = reflect_point_across_line(p, a, b);
    let line = line2_from_points(a, b);
    let two = F::one().add(F::one());

    // Forward: r satisfies perp
    lemma_reflect_satisfies_perp::<F>(p, a, b);
    // Forward: r satisfies midpoint-on-axis
    lemma_reflect_midpoint_on_axis::<F>(p, a, b);

    // Subtract: q and r both satisfy perp → dot((q-p)-(r-p), d) = dot(q-r, d) ≡ 0
    // i.e. dx*(qx-rx) + dy*(qy-ry) ≡ 0
    let u = q.x.sub(r.x);
    let v = q.y.sub(r.y);

    // Equation 1: dx*u + dy*v ≡ 0
    // From perp(q): dot(q-p, d) ≡ 0
    // From perp(r): dot(r-p, d) ≡ 0
    // Subtract: dot(q-r, d) = dot(q-p, d) - dot(r-p, d) ≡ 0 - 0 ≡ 0
    // dot(q-r, d) = (qx-rx)*dx + (qy-ry)*dy = dx*u + dy*v... wait, (qx-rx) is u but multiplied by dx
    // sub2(q, p).x*dx = (qx-px)*dx, sub2(r, p).x*dx = (rx-px)*dx
    // Their difference: (qx-px)*dx - (rx-px)*dx = (qx-rx)*dx = u*dx
    // Similarly for y.
    // But dx*u may not equal u*dx without commutativity.
    // We need: dx*(qx-rx) + dy*(qy-ry) ≡ 0

    // From perp_q - perp_r:
    lemma_sub_congruence::<F>(
        sub2(q, p).x.mul(dx).add(sub2(q, p).y.mul(dy)),
        F::zero(),
        sub2(r, p).x.mul(dx).add(sub2(r, p).y.mul(dy)),
        F::zero());
    lemma_sub_self::<F>(F::zero());
    // (perp_q - perp_r) ≡ 0

    // perp_q - perp_r = ((qx-px)*dx + (qy-py)*dy) - ((rx-px)*dx + (ry-py)*dy)
    // By add_sub_cancel_common-like reasoning:
    // = (qx-px)*dx - (rx-px)*dx + (qy-py)*dy - (ry-py)*dy
    // = ((qx-px)-(rx-px))*dx + ((qy-py)-(ry-py))*dy
    // = (qx-rx)*dx + (qy-ry)*dy
    // Need: (a-b)*c - (d-b)*c ≡ (a-d)*c
    // i.e. sub congruence on first arg: (qx-px) - (rx-px) ≡ qx - rx = u

    // This is complex to prove algebraically. Let me try: Z3 might handle it
    // given sub_is_add_neg hints and the 2x2 uniqueness preconditions.

    // Similarly for equation 2: -dy*u + dx*v ≡ 0 from midpoint subtraction.

    // The cleanest approach: just assert the two system equations hold
    // and invoke the 2x2 solver. Z3 should connect given all the hints.
    assert(dx.mul(u).add(dy.mul(v)).eqv(F::zero())) by {
        // Z3 hint: expand everything with sub_is_add_neg
        F::axiom_sub_is_add_neg(q.x, r.x);
        F::axiom_sub_is_add_neg(q.x, p.x);
        F::axiom_sub_is_add_neg(r.x, p.x);
        F::axiom_sub_is_add_neg(q.y, r.y);
        F::axiom_sub_is_add_neg(q.y, p.y);
        F::axiom_sub_is_add_neg(r.y, p.y);
        F::axiom_mul_distributes_left(dx, q.x.add(r.x.neg()), F::zero());
        F::axiom_mul_distributes_left(dx, q.x.add(p.x.neg()), F::zero());
    };

    assert(dy.neg().mul(u).add(dx.mul(v)).eqv(F::zero())) by {
        F::axiom_sub_is_add_neg(q.x, r.x);
        F::axiom_sub_is_add_neg(q.y, r.y);
        F::axiom_sub_is_add_neg(q.x, p.x);
        F::axiom_sub_is_add_neg(q.y, p.y);
        F::axiom_sub_is_add_neg(r.x, p.x);
        F::axiom_sub_is_add_neg(r.y, p.y);
    };

    // Apply uniqueness: u ≡ 0, v ≡ 0
    lemma_2x2_trivial_solution::<F>(dx, dy, u, v);
    // qx - rx ≡ 0 → qx ≡ rx, qy - ry ≡ 0 → qy ≡ ry
    crate::collinearity::lemma_sub_zero_implies_eqv::<F>(q.x, r.x);
    crate::collinearity::lemma_sub_zero_implies_eqv::<F>(q.y, r.y);
    // q.eqv(r): q.x ≡ r.x && q.y ≡ r.y
}

} // verus!
