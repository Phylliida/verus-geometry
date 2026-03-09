use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::line2::RuntimeLine2;
#[cfg(verus_keep_ghost)]
use crate::line_intersection::*;
#[cfg(verus_keep_ghost)]
use crate::line2::Line2;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

/// Compute the determinant of two lines' normals.
pub fn line_det_exec(l1: &RuntimeLine2, l2: &RuntimeLine2) -> (out: RuntimeRational)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == line_det::<RationalModel>(l1@, l2@),
{
    let a1b2 = l1.a.mul(&l2.b);
    let b1a2 = l1.b.mul(&l2.a);
    a1b2.sub(&b1a2)
}

/// Compute the intersection point of two non-parallel lines.
pub fn line_line_intersection_2d_exec(
    l1: &RuntimeLine2,
    l2: &RuntimeLine2,
) -> (out: RuntimePoint2)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
        !line_det::<RationalModel>(l1@, l2@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == line_line_intersection_2d::<RationalModel>(l1@, l2@),
{
    let det = line_det_exec(l1, l2);
    // x = (b1*c2 - b2*c1) / det
    let b1c2 = l1.b.mul(&l2.c);
    let b2c1 = l2.b.mul(&l1.c);
    let x_num = b1c2.sub(&b2c1);
    let x = x_num.div(&det);
    // y = (a2*c1 - a1*c2) / det
    let a2c1 = l2.a.mul(&l1.c);
    let a1c2 = l1.a.mul(&l2.c);
    let y_num = a2c1.sub(&a1c2);
    let y = y_num.div(&det);

    RuntimePoint2::new(x, y)
}

} // verus!
