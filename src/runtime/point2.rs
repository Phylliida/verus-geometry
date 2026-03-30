#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ring::Ring;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use verus_linalg::runtime::vec2::RuntimeVec2;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 2D point, generic over any runtime field. Models Point2<V>.
pub struct RuntimePoint2<R, V: OrderedField> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub model: Ghost<Point2<V>>,
}

impl<R: RuntimeRingOps<V>, V: OrderedField> RuntimePoint2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
    }

    pub fn new(x: R, y: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.model(),
            out.model@.y == y.model(),
    {
        let ghost model = Point2 { x: x.model(), y: y.model() };
        RuntimePoint2 { x, y, model: Ghost(model) }
    }

    pub fn copy_point(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@,
    {
        RuntimePoint2::new(self.x.copy(), self.y.copy())
    }

    ///  Point - Point = Vec2.
    pub fn sub(&self, other: &Self) -> (out: RuntimeVec2<R, V>)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.sub(other.model@.x),
            out.model@.y == self.model@.y.sub(other.model@.y),
    {
        RuntimeVec2::new(
            self.x.sub(&other.x),
            self.y.sub(&other.y),
        )
    }

    ///  Point + Vec2 = Point.
    pub fn add(&self, v: &RuntimeVec2<R, V>) -> (out: Self)
        requires self.wf_spec(), v.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.add(v.model@.x),
            out.model@.y == self.model@.y.add(v.model@.y),
    {
        RuntimePoint2::new(
            self.x.add(&v.x),
            self.y.add(&v.y),
        )
    }
}

} //  verus!
