use verus_rational::RuntimeRational;
use verus_quadratic_extension::runtime::RuntimeQExtRat;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
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
use crate::line2::Line2;
#[cfg(verus_keep_ghost)]
use crate::circle2::Circle2;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;

#[cfg(verus_keep_ghost)]
verus! {

///  Compute the quadratic coefficient A = a² + b².
pub fn cl_quad_a_exec(line: &RuntimeLine2) -> (out: RuntimeRational)
    requires
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_quad_a::<RationalModel>(line@),
{
    let a2 = line.a.mul(&line.a);
    let b2 = line.b.mul(&line.b);
    a2.add(&b2)
}

///  Compute the signed distance numerator: a*cx + b*cy + c.
pub fn cl_signed_dist_num_exec(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
) -> (out: RuntimeRational)
    requires
        circle.wf_spec(),
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_signed_dist_num::<RationalModel>(circle@, line@),
{
    let acx = line.a.mul(&circle.center.x);
    let bcy = line.b.mul(&circle.center.y);
    let s = acx.add(&bcy);
    s.add(&line.c)
}

///  Compute the circle-line discriminant: A * r² - h².
pub fn cl_discriminant_exec(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
) -> (out: RuntimeRational)
    requires
        circle.wf_spec(),
        line.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cl_discriminant::<RationalModel>(circle@, line@),
{
    let a_coef = cl_quad_a_exec(line);
    let h = cl_signed_dist_num_exec(circle, line);
    let ar2 = a_coef.mul(&circle.radius_sq);
    let h2 = h.mul(&h);
    ar2.sub(&h2)
}

///  Compute the x-coordinate of a circle-line intersection.
pub fn cl_intersection_x_exec<R: PositiveRadicand<RationalModel>>(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
    plus: bool,
) -> (out: RuntimeQExtRat<R>)
    requires
        circle.wf_spec(),
        line.wf_spec(),
        !cl_quad_a::<RationalModel>(line@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_x::<RationalModel, R>(circle@, line@, plus),
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

    RuntimeQExtRat::new(re, im)
}

///  Compute the y-coordinate of a circle-line intersection.
pub fn cl_intersection_y_exec<R: PositiveRadicand<RationalModel>>(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
    plus: bool,
) -> (out: RuntimeQExtRat<R>)
    requires
        circle.wf_spec(),
        line.wf_spec(),
        !cl_quad_a::<RationalModel>(line@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_y::<RationalModel, R>(circle@, line@, plus),
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

    RuntimeQExtRat::new(re, im)
}

} //  verus!
