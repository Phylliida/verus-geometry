#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::point3::Point3;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{cross, dot};

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 3D point/vector, generic over any runtime field.
pub struct RuntimePoint3<R, V: OrderedField> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub z: R,
    pub model: Ghost<Point3<V>>,
}

impl<R: RuntimeRingOps<V>, V: OrderedField> RuntimePoint3<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.z.model() == self.model@.z
    }

    pub fn new(x: R, y: R, z: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.model(),
            out.model@.y == y.model(),
            out.model@.z == z.model(),
    {
        let ghost model = Point3 { x: x.model(), y: y.model(), z: z.model() };
        RuntimePoint3 { x, y, z, model: Ghost(model) }
    }

    pub fn copy_point(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@,
    {
        let x = self.x.copy();
        let y = self.y.copy();
        let z = self.z.copy();
        RuntimePoint3 { x, y, z, model: Ghost(self.model@) }
    }

    ///  Component-wise subtraction: self - other.
    pub fn sub(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.sub(other.model@.x),
            out.model@.y == self.model@.y.sub(other.model@.y),
            out.model@.z == self.model@.z.sub(other.model@.z),
    {
        RuntimePoint3::new(
            self.x.sub(&other.x),
            self.y.sub(&other.y),
            self.z.sub(&other.z),
        )
    }

    ///  Component-wise addition: self + other.
    pub fn add(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.add(other.model@.x),
            out.model@.y == self.model@.y.add(other.model@.y),
            out.model@.z == self.model@.z.add(other.model@.z),
    {
        RuntimePoint3::new(
            self.x.add(&other.x),
            self.y.add(&other.y),
            self.z.add(&other.z),
        )
    }

    ///  Scalar multiply: t * self.
    pub fn scale(&self, t: &R) -> (out: Self)
        requires self.wf_spec(), t.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == t.model().mul(self.model@.x),
            out.model@.y == t.model().mul(self.model@.y),
            out.model@.z == t.model().mul(self.model@.z),
    {
        RuntimePoint3::new(
            t.mul(&self.x),
            t.mul(&self.y),
            t.mul(&self.z),
        )
    }

    ///  Cross product: self × other.
    pub fn cross(&self, other: &Self) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.y.mul(other.model@.z).sub(self.model@.z.mul(other.model@.y)),
            out.model@.y == self.model@.z.mul(other.model@.x).sub(self.model@.x.mul(other.model@.z)),
            out.model@.z == self.model@.x.mul(other.model@.y).sub(self.model@.y.mul(other.model@.x)),
    {
        RuntimePoint3::new(
            self.y.mul(&other.z).sub(&self.z.mul(&other.y)),
            self.z.mul(&other.x).sub(&self.x.mul(&other.z)),
            self.x.mul(&other.y).sub(&self.y.mul(&other.x)),
        )
    }

    ///  Dot product: self · other.
    pub fn dot(&self, other: &Self) -> (out: R)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model() == self.model@.x.mul(other.model@.x)
                .add(self.model@.y.mul(other.model@.y))
                .add(self.model@.z.mul(other.model@.z)),
    {
        self.x.mul(&other.x)
            .add(&self.y.mul(&other.y))
            .add(&self.z.mul(&other.z))
    }

    ///  Squared norm: self · self.
    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out.model() == self.model@.x.mul(self.model@.x)
                .add(self.model@.y.mul(self.model@.y))
                .add(self.model@.z.mul(self.model@.z)),
    {
        self.dot(self)
    }
}

} //  verus!
