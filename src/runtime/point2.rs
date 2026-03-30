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

///  A runtime 2D point/vector, generic over any runtime field.
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
        let x = self.x.copy();
        let y = self.y.copy();
        RuntimePoint2 { x, y, model: Ghost(self.model@) }
    }

    ///  Component-wise subtraction: self - other.
    pub fn sub(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.sub(other.model@.x),
            out.model@.y == self.model@.y.sub(other.model@.y),
    {
        RuntimePoint2::new(
            self.x.sub(&other.x),
            self.y.sub(&other.y),
        )
    }

    ///  Component-wise addition: self + other.
    pub fn add(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.add(other.model@.x),
            out.model@.y == self.model@.y.add(other.model@.y),
    {
        RuntimePoint2::new(
            self.x.add(&other.x),
            self.y.add(&other.y),
        )
    }

    ///  Scalar multiply: t * self.
    pub fn scale(&self, t: &R) -> (out: Self)
        requires self.wf_spec(), t.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == t.model().mul(self.model@.x),
            out.model@.y == t.model().mul(self.model@.y),
    {
        RuntimePoint2::new(
            t.mul(&self.x),
            t.mul(&self.y),
        )
    }

    ///  Dot product: self · other.
    pub fn dot(&self, other: &Self) -> (out: R)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model() == self.model@.x.mul(other.model@.x)
                .add(self.model@.y.mul(other.model@.y)),
    {
        self.x.mul(&other.x).add(&self.y.mul(&other.y))
    }

    ///  Squared norm: self · self.
    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out.model() == self.model@.x.mul(self.model@.x)
                .add(self.model@.y.mul(self.model@.y)),
    {
        self.dot(self)
    }
}

} //  verus!
