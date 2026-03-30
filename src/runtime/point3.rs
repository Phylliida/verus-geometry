#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::point3::Point3;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 3D point, generic over any runtime field.
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
}

///  Point subtraction: a - b = (dx, dy, dz).
pub fn sub3_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
) -> (out: (R, R, R))
    requires a.wf_spec(), b.wf_spec(),
    ensures
        out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
        out.0.model() == a.model@.x.sub(b.model@.x),
        out.1.model() == a.model@.y.sub(b.model@.y),
        out.2.model() == a.model@.z.sub(b.model@.z),
{
    (a.x.sub(&b.x), a.y.sub(&b.y), a.z.sub(&b.z))
}

///  Point + (dx, dy, dz) = point.
pub fn add_vec3_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    dx: &R, dy: &R, dz: &R,
) -> (out: RuntimePoint3<R, V>)
    requires p.wf_spec(), dx.wf_spec(), dy.wf_spec(), dz.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@.x == p.model@.x.add(dx.model()),
        out.model@.y == p.model@.y.add(dy.model()),
        out.model@.z == p.model@.z.add(dz.model()),
{
    let rx = p.x.add(dx);
    let ry = p.y.add(dy);
    let rz = p.z.add(dz);
    let ghost model = Point3 {
        x: p.model@.x.add(dx.model()),
        y: p.model@.y.add(dy.model()),
        z: p.model@.z.add(dz.model()),
    };
    RuntimePoint3 { x: rx, y: ry, z: rz, model: Ghost(model) }
}

///  Cross product: (u × v) = (uy*vz - uz*vy, uz*vx - ux*vz, ux*vy - uy*vx).
pub fn cross_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    ux: &R, uy: &R, uz: &R,
    vx: &R, vy: &R, vz: &R,
) -> (out: (R, R, R))
    requires
        ux.wf_spec(), uy.wf_spec(), uz.wf_spec(),
        vx.wf_spec(), vy.wf_spec(), vz.wf_spec(),
    ensures
        out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
        out.0.model() == uy.model().mul(vz.model()).sub(uz.model().mul(vy.model())),
        out.1.model() == uz.model().mul(vx.model()).sub(ux.model().mul(vz.model())),
        out.2.model() == ux.model().mul(vy.model()).sub(uy.model().mul(vx.model())),
{
    let a = uy.mul(vz).sub(&uz.mul(vy));
    let b = uz.mul(vx).sub(&ux.mul(vz));
    let c = ux.mul(vy).sub(&uy.mul(vx));
    (a, b, c)
}

///  Dot product: u · v = ux*vx + uy*vy + uz*vz.
pub fn dot3_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    ux: &R, uy: &R, uz: &R,
    vx: &R, vy: &R, vz: &R,
) -> (out: R)
    requires
        ux.wf_spec(), uy.wf_spec(), uz.wf_spec(),
        vx.wf_spec(), vy.wf_spec(), vz.wf_spec(),
    ensures
        out.wf_spec(),
        out.model() == ux.model().mul(vx.model())
            .add(uy.model().mul(vy.model()))
            .add(uz.model().mul(vz.model())),
{
    let a = ux.mul(vx);
    let b = uy.mul(vy);
    let c = uz.mul(vz);
    a.add(&b).add(&c)
}

} //  verus!
