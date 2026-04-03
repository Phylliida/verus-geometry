#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::line2::RuntimeLine2;
#[cfg(verus_keep_ghost)]
use super::circle2::RuntimeCircle2;
#[cfg(verus_keep_ghost)]
use verus_quadratic_extension::radicand::*;
#[cfg(verus_keep_ghost)]
use verus_quadratic_extension::spec::*;
#[cfg(verus_keep_ghost)]
use verus_quadratic_extension::runtime_qext::RuntimeQExt;
#[cfg(verus_keep_ghost)]
use crate::circle_line::*;
#[cfg(verus_keep_ghost)]
use crate::circle_circle::*;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;

#[cfg(verus_keep_ghost)]
verus! {

///  Compute the radical axis of two circles.
pub fn radical_axis_exec<F: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    c1: &RuntimeCircle2<F, V>,
    c2: &RuntimeCircle2<F, V>,
) -> (out: RuntimeLine2<F, V>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == radical_axis::<V>(c1.model@, c2.model@),
{
    let one = c1.center.x.one_like();
    let one2 = c1.center.x.one_like();
    let two = one.add(&one2);

    //  a = 2 * (c2.x - c1.x)
    let dx = c2.center.x.sub(&c1.center.x);
    let a = two.mul(&dx);

    //  b = 2 * (c2.y - c1.y)
    let dy = c2.center.y.sub(&c1.center.y);
    let two2 = c1.center.x.one_like().add(&c1.center.x.one_like());
    let b = two2.mul(&dy);

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

    RuntimeLine2::<F, V>::new(a, b, c)
}

///  Compute the circle-circle discriminant.
pub fn cc_discriminant_exec<F: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    c1: &RuntimeCircle2<F, V>,
    c2: &RuntimeCircle2<F, V>,
) -> (out: F)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cc_discriminant::<V>(c1.model@, c2.model@),
{
    let ra = radical_axis_exec(c1, c2);
    super::circle_line::cl_discriminant_exec(c1, &ra)
}

///  Compute the x-coordinate of a circle-circle intersection.
///  Delegates to radical_axis + cl_intersection_x.
pub fn cc_intersection_x_exec<V: OrderedField, R: PositiveRadicand<V>, F: RuntimeOrderedFieldOps<V>>(
    c1: &RuntimeCircle2<F, V>,
    c2: &RuntimeCircle2<F, V>,
    radicand_rt: &F,
    plus: bool,
) -> (out: RuntimeQExt<V, R, F>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt@ == R::value(),
        !c1.model@.center.eqv(c2.model@.center),
    ensures
        out.wf_spec(),
        out@ == cc_intersection_point::<V, R>(c1.model@, c2.model@, plus).x,
{
    let ra = radical_axis_exec(c1, c2);
    proof {
        let ral = radical_axis::<V>(c1.model@, c2.model@);
        crate::circle_circle_proofs::lemma_radical_axis_nondegenerate::<V>(c1.model@, c2.model@);
        crate::circle_line::lemma_cl_quad_a_positive::<V>(ral);
        V::axiom_lt_iff_le_and_not_eqv(
            V::zero(),
            cl_quad_a::<V>(ral),
        );
        V::axiom_eqv_symmetric(
            V::zero(),
            cl_quad_a::<V>(ral),
        );
    }
    super::circle_line::cl_intersection_x_exec::<V, R, F>(c1, &ra, radicand_rt, plus)
}

///  Compute the y-coordinate of a circle-circle intersection.
///  Delegates to radical_axis + cl_intersection_y.
pub fn cc_intersection_y_exec<V: OrderedField, R: PositiveRadicand<V>, F: RuntimeOrderedFieldOps<V>>(
    c1: &RuntimeCircle2<F, V>,
    c2: &RuntimeCircle2<F, V>,
    radicand_rt: &F,
    plus: bool,
) -> (out: RuntimeQExt<V, R, F>)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt@ == R::value(),
        !c1.model@.center.eqv(c2.model@.center),
    ensures
        out.wf_spec(),
        out@ == cc_intersection_point::<V, R>(c1.model@, c2.model@, plus).y,
{
    let ra = radical_axis_exec(c1, c2);
    proof {
        let ral = radical_axis::<V>(c1.model@, c2.model@);
        crate::circle_circle_proofs::lemma_radical_axis_nondegenerate::<V>(c1.model@, c2.model@);
        crate::circle_line::lemma_cl_quad_a_positive::<V>(ral);
        V::axiom_lt_iff_le_and_not_eqv(
            V::zero(),
            cl_quad_a::<V>(ral),
        );
        V::axiom_eqv_symmetric(
            V::zero(),
            cl_quad_a::<V>(ral),
        );
    }
    super::circle_line::cl_intersection_y_exec::<V, R, F>(c1, &ra, radicand_rt, plus)
}

} //  verus!
