#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::line2::*;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 2D line (ax + by + c = 0), generic over any runtime field.
pub struct RuntimeLine2<R, V: OrderedField> where R: RuntimeRingOps<V> {
    pub a: R,
    pub b: R,
    pub c: R,
    pub model: Ghost<Line2<V>>,
}

impl<R: RuntimeRingOps<V>, V: OrderedField> RuntimeLine2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.a.wf_spec()
        &&& self.b.wf_spec()
        &&& self.c.wf_spec()
        &&& self.a.rf_view() == self.model@.a
        &&& self.b.rf_view() == self.model@.b
        &&& self.c.rf_view() == self.model@.c
    }

    pub fn new(a: R, b: R, c: R) -> (out: Self)
        requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.a == a.rf_view(),
            out.model@.b == b.rf_view(),
            out.model@.c == c.rf_view(),
    {
        let ghost model = Line2 { a: a.rf_view(), b: b.rf_view(), c: c.rf_view() };
        RuntimeLine2 { a, b, c, model: Ghost(model) }
    }
}

///  Construct a line through two points.
pub fn line2_from_points_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    q: &RuntimePoint2<R, V>,
) -> (out: RuntimeLine2<R, V>)
    requires p.wf_spec(), q.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@ == line2_from_points::<V>(p.model@, q.model@),
{
    let dy = q.y.rf_sub(&p.y);
    let a = dy.rf_neg();
    let b = q.x.rf_sub(&p.x);
    let apx = a.rf_mul(&p.x);
    let bpy = b.rf_mul(&p.y);
    let s = apx.rf_add(&bpy);
    let c = s.rf_neg();
    let ghost model = line2_from_points::<V>(p.model@, q.model@);
    RuntimeLine2 { a, b, c, model: Ghost(model) }
}

///  Evaluate the line equation at a point: a*px + b*py + c.
pub fn line2_eval_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    line: &RuntimeLine2<R, V>,
    p: &RuntimePoint2<R, V>,
) -> (out: R)
    requires line.wf_spec(), p.wf_spec(),
    ensures
        out.wf_spec(),
        out.rf_view() == line2_eval::<V>(line.model@, p.model@),
{
    let apx = line.a.rf_mul(&p.x);
    let bpy = line.b.rf_mul(&p.y);
    let s = apx.rf_add(&bpy);
    s.rf_add(&line.c)
}

} //  verus!
