use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;
use verus_quadratic_extension::runtime::RuntimeQExtRat;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]

#[cfg(verus_keep_ghost)]
use super::line2::RuntimeLine2;
#[cfg(verus_keep_ghost)]
use super::circle2::RuntimeCircle2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_quadratic_extension::radicand::*;
#[cfg(verus_keep_ghost)]
use verus_quadratic_extension::spec::*;
#[cfg(verus_keep_ghost)]
use crate::circle_line::*;
#[cfg(verus_keep_ghost)]
use crate::circle_circle::*;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;

#[cfg(verus_keep_ghost)]
verus! {

///  Compute the radical axis of two circles.
pub fn radical_axis_exec(
    c1: &RuntimeCircle2<RuntimeRational, Rational>,
    c2: &RuntimeCircle2<RuntimeRational, Rational>,
) -> (out: RuntimeLine2<RuntimeRational, Rational>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == radical_axis::<Rational>(c1.model@, c2.model@),
{
    let one = RuntimeRational::from_int(1);
    let two = one.add(&RuntimeRational::from_int(1));

    //  a = 2 * (c2.x - c1.x)
    let dx = c2.center.x.sub(&c1.center.x);
    let a = two.mul(&dx);

    //  b = 2 * (c2.y - c1.y)
    let dy = c2.center.y.sub(&c1.center.y);
    let b = two.mul(&dy);

    //  c1_sq = c1.x² + c1.y²
    let c1x2 = c1.center.x.mul(&c1.center.x);
    let c1y2 = c1.center.y.mul(&c1.center.y);
    let c1_sq = c1x2.add(&c1y2);

    //  c2_sq = c2.x² + c2.y²
    let c2x2 = c2.center.x.mul(&c2.center.x);
    let c2y2 = c2.center.y.mul(&c2.center.y);
    let c2_sq = c2x2.add(&c2y2);

    //  c = (c1_sq - r1²) - (c2_sq - r2²)
    let lhs = c1_sq.sub(&c1.radius_sq);
    let rhs = c2_sq.sub(&c2.radius_sq);
    let c = lhs.sub(&rhs);

    RuntimeLine2::<RuntimeRational, Rational>::new(a, b, c)
}

///  Compute the circle-circle discriminant.
pub fn cc_discriminant_exec(
    c1: &RuntimeCircle2<RuntimeRational, Rational>,
    c2: &RuntimeCircle2<RuntimeRational, Rational>,
) -> (out: RuntimeRational)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == cc_discriminant::<Rational>(c1.model@, c2.model@),
{
    let ra = radical_axis_exec(c1, c2);
    super::circle_line::cl_discriminant_exec(c1, &ra)
}

///  Compute the x-coordinate of a circle-circle intersection.
///  Delegates to radical_axis + cl_intersection_x.
pub fn cc_intersection_x_exec<R: PositiveRadicand<Rational>>(
    c1: &RuntimeCircle2<RuntimeRational, Rational>,
    c2: &RuntimeCircle2<RuntimeRational, Rational>,
    plus: bool,
) -> (out: RuntimeQExtRat<R>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        !c1.model@.center.eqv(c2.model@.center),
    ensures
        out.wf_spec(),
        out.model@ == cc_intersection_point::<Rational, R>(c1.model@, c2.model@, plus).x,
{
    let ra = radical_axis_exec(c1, c2);
    proof {
        let ral = radical_axis::<Rational>(c1.model@, c2.model@);
        crate::circle_circle_proofs::lemma_radical_axis_nondegenerate::<Rational>(c1.model@, c2.model@);
        crate::circle_line::lemma_cl_quad_a_positive::<Rational>(ral);
        //  0 < cl_quad_a(ral) implies 0.le(cl_quad_a) && !0.eqv(cl_quad_a)
        Rational::axiom_lt_iff_le_and_not_eqv(
            Rational::from_int_spec(0),
            cl_quad_a::<Rational>(ral),
        );
        //  !0.eqv(x) → !x.eqv(0) by symmetry
        Rational::axiom_eqv_symmetric(
            Rational::from_int_spec(0),
            cl_quad_a::<Rational>(ral),
        );
    }
    super::circle_line::cl_intersection_x_exec::<R>(c1, &ra, plus)
}

///  Compute the y-coordinate of a circle-circle intersection.
///  Delegates to radical_axis + cl_intersection_y.
pub fn cc_intersection_y_exec<R: PositiveRadicand<Rational>>(
    c1: &RuntimeCircle2<RuntimeRational, Rational>,
    c2: &RuntimeCircle2<RuntimeRational, Rational>,
    plus: bool,
) -> (out: RuntimeQExtRat<R>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        !c1.model@.center.eqv(c2.model@.center),
    ensures
        out.wf_spec(),
        out.model@ == cc_intersection_point::<Rational, R>(c1.model@, c2.model@, plus).y,
{
    let ra = radical_axis_exec(c1, c2);
    proof {
        let ral = radical_axis::<Rational>(c1.model@, c2.model@);
        crate::circle_circle_proofs::lemma_radical_axis_nondegenerate::<Rational>(c1.model@, c2.model@);
        crate::circle_line::lemma_cl_quad_a_positive::<Rational>(ral);
        Rational::axiom_lt_iff_le_and_not_eqv(
            Rational::from_int_spec(0),
            cl_quad_a::<Rational>(ral),
        );
        Rational::axiom_eqv_symmetric(
            Rational::from_int_spec(0),
            cl_quad_a::<Rational>(ral),
        );
    }
    super::circle_line::cl_intersection_y_exec::<R>(c1, &ra, plus)
}

} //  verus!
