#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 2D point, generic over any runtime field.
pub struct RuntimePoint2<R, V: OrderedField> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub model: Ghost<Point2<V>>,
}

impl<R: RuntimeRingOps<V>, V: OrderedField> RuntimePoint2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x.rf_view() == self.model@.x
        &&& self.y.rf_view() == self.model@.y
    }

    pub fn new(x: R, y: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.rf_view(),
            out.model@.y == y.rf_view(),
    {
        let ghost model = Point2 { x: x.rf_view(), y: y.rf_view() };
        RuntimePoint2 { x, y, model: Ghost(model) }
    }

    pub fn copy_point(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@,
    {
        let x = self.x.rf_copy();
        let y = self.y.rf_copy();
        RuntimePoint2 { x, y, model: Ghost(self.model@) }
    }
}

///  Point subtraction: a - b = (dx, dy).
pub fn sub2_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    a: &RuntimePoint2<R, V>,
    b: &RuntimePoint2<R, V>,
) -> (out: (R, R))
    requires a.wf_spec(), b.wf_spec(),
    ensures
        out.0.wf_spec(), out.1.wf_spec(),
        out.0.rf_view() == a.model@.x.sub(b.model@.x),
        out.1.rf_view() == a.model@.y.sub(b.model@.y),
{
    (a.x.rf_sub(&b.x), a.y.rf_sub(&b.y))
}

///  Point + (dx, dy) = point.
pub fn add_vec2_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>,
    dx: &R,
    dy: &R,
) -> (out: RuntimePoint2<R, V>)
    requires p.wf_spec(), dx.wf_spec(), dy.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@.x == p.model@.x.add(dx.rf_view()),
        out.model@.y == p.model@.y.add(dy.rf_view()),
{
    let rx = p.x.rf_add(dx);
    let ry = p.y.rf_add(dy);
    let ghost model = Point2 { x: p.model@.x.add(dx.rf_view()), y: p.model@.y.add(dy.rf_view()) };
    RuntimePoint2 { x: rx, y: ry, model: Ghost(model) }
}

} //  verus!
