#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::line2::RuntimeLine2;
#[cfg(verus_keep_ghost)]
use crate::line_intersection::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
verus! {

pub fn line_det_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    l1: &RuntimeLine2<R, V>, l2: &RuntimeLine2<R, V>,
) -> (out: R)
    requires l1.wf_spec(), l2.wf_spec(),
    ensures out.wf_spec(), out@ == line_det::<V>(l1.model@, l2.model@),
{
    let a1b2 = l1.a.mul(&l2.b);
    let b1a2 = l1.b.mul(&l2.a);
    a1b2.sub(&b1a2)
}

pub fn line_line_intersection_2d_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    l1: &RuntimeLine2<R, V>,
    l2: &RuntimeLine2<R, V>,
) -> (out: RuntimePoint2<R, V>)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
        !line_det::<V>(l1.model@, l2.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model@ == line_line_intersection_2d::<V>(l1.model@, l2.model@),
{
    let det = line_det_exec(l1, l2);
    let b1c2 = l1.b.mul(&l2.c);
    let b2c1 = l2.b.mul(&l1.c);
    let x_num = b1c2.sub(&b2c1);
    let x = x_num.div(&det);
    let a2c1 = l2.a.mul(&l1.c);
    let a1c2 = l1.a.mul(&l2.c);
    let y_num = a2c1.sub(&a1c2);
    let y = y_num.div(&det);
    RuntimePoint2::new(x, y)
}

} //  verus!
