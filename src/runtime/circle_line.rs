#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
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
verus! {

///  Compute the quadratic coefficient A = a² + b².
pub fn cl_quad_a_exec<F: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    line: &RuntimeLine2<F, V>,
) -> (out: F)
    requires
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_quad_a::<V>(line.model@),
{
    let a2 = line.a.mul(&line.a);
    let b2 = line.b.mul(&line.b);
    a2.add(&b2)
}

///  Compute the signed distance numerator: a*cx + b*cy + c.
pub fn cl_signed_dist_num_exec<F: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    circle: &RuntimeCircle2<F, V>,
    line: &RuntimeLine2<F, V>,
) -> (out: F)
    requires
        circle.wf_spec(),
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_signed_dist_num::<V>(circle.model@, line.model@),
{
    let acx = line.a.mul(&circle.center.x);
    let bcy = line.b.mul(&circle.center.y);
    let s = acx.add(&bcy);
    s.add(&line.c)
}

///  Compute the circle-line discriminant: A * r² - h².
pub fn cl_discriminant_exec<F: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    circle: &RuntimeCircle2<F, V>,
    line: &RuntimeLine2<F, V>,
) -> (out: F)
    requires
        circle.wf_spec(),
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_discriminant::<V>(circle.model@, line.model@),
{
    let a_coef = cl_quad_a_exec(line);
    let h = cl_signed_dist_num_exec(circle, line);
    let ar2 = a_coef.mul(&circle.radius_sq);
    let h2 = h.mul(&h);
    ar2.sub(&h2)
}

///  Compute the x-coordinate of a circle-line intersection.
pub fn cl_intersection_x_exec<V: OrderedField, R: PositiveRadicand<V>, F: RuntimeOrderedFieldOps<V>>(
    circle: &RuntimeCircle2<F, V>,
    line: &RuntimeLine2<F, V>,
    radicand_rt: &F,
    plus: bool,
) -> (out: RuntimeQExt<V, R, F>)
    requires
        circle.wf_spec(),
        line.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt@ == R::value(),
        !cl_quad_a::<V>(line.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_x::<V, R>(circle.model@, line.model@, plus),
{
    let a_coef = cl_quad_a_exec(line);
    let h = cl_signed_dist_num_exec(circle, line);

    //  re = cx - a*h / A
    let ah = line.a.mul(&h);
    let ah_div_a = ah.div(&a_coef);
    let re = circle.center.x.sub(&ah_div_a);

    //  im = ∓ b / A
    let im = if plus {
        let nb = line.b.neg();
        nb.div(&a_coef)
    } else {
        line.b.div(&a_coef)
    };

    let rad = radicand_rt.copy();
    RuntimeQExt::new(re, im, rad)
}

///  Compute the y-coordinate of a circle-line intersection.
pub fn cl_intersection_y_exec<V: OrderedField, R: PositiveRadicand<V>, F: RuntimeOrderedFieldOps<V>>(
    circle: &RuntimeCircle2<F, V>,
    line: &RuntimeLine2<F, V>,
    radicand_rt: &F,
    plus: bool,
) -> (out: RuntimeQExt<V, R, F>)
    requires
        circle.wf_spec(),
        line.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt@ == R::value(),
        !cl_quad_a::<V>(line.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_y::<V, R>(circle.model@, line.model@, plus),
{
    let a_coef = cl_quad_a_exec(line);
    let h = cl_signed_dist_num_exec(circle, line);

    //  re = cy - b*h / A
    let bh = line.b.mul(&h);
    let bh_div_a = bh.div(&a_coef);
    let re = circle.center.y.sub(&bh_div_a);

    //  im = ± a / A
    let im = if plus {
        line.a.div(&a_coef)
    } else {
        let na = line.a.neg();
        na.div(&a_coef)
    };

    let rad = radicand_rt.copy();
    RuntimeQExt::new(re, im, rad)
}

} //  verus!
