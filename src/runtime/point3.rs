#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::point3::Point3;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::ring::Ring;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_linalg::runtime::vec3::RuntimeVec3;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 3D point, generic over any runtime field. Models Point3<V>.
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
        RuntimePoint3::new(self.x.copy(), self.y.copy(), self.z.copy())
    }

    ///  Point - Point = Vec3.
    pub fn sub(&self, other: &Self) -> (out: RuntimeVec3<R, V>)
        requires self.wf_spec(), other.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.sub(other.model@.x),
            out.model@.y == self.model@.y.sub(other.model@.y),
            out.model@.z == self.model@.z.sub(other.model@.z),
    {
        RuntimeVec3::new(
            self.x.sub(&other.x),
            self.y.sub(&other.y),
            self.z.sub(&other.z),
        )
    }

    ///  Point + Vec3 = Point.
    pub fn add(&self, v: &RuntimeVec3<R, V>) -> (out: Self)
        requires self.wf_spec(), v.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == self.model@.x.add(v.model@.x),
            out.model@.y == self.model@.y.add(v.model@.y),
            out.model@.z == self.model@.z.add(v.model@.z),
    {
        RuntimePoint3::new(
            self.x.add(&v.x),
            self.y.add(&v.y),
            self.z.add(&v.z),
        )
    }
}

} //  verus!
