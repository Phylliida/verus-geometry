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
        &&& self.x.rf_view() == self.model@.x
        &&& self.y.rf_view() == self.model@.y
        &&& self.z.rf_view() == self.model@.z
    }

    pub fn new(x: R, y: R, z: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.rf_view(),
            out.model@.y == y.rf_view(),
            out.model@.z == z.rf_view(),
    {
        let ghost model = Point3 { x: x.rf_view(), y: y.rf_view(), z: z.rf_view() };
        RuntimePoint3 { x, y, z, model: Ghost(model) }
    }

    pub fn copy_point(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@,
    {
        let x = self.x.rf_copy();
        let y = self.y.rf_copy();
        let z = self.z.rf_copy();
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
        out.0.rf_view() == a.model@.x.sub(b.model@.x),
        out.1.rf_view() == a.model@.y.sub(b.model@.y),
        out.2.rf_view() == a.model@.z.sub(b.model@.z),
{
    (a.x.rf_sub(&b.x), a.y.rf_sub(&b.y), a.z.rf_sub(&b.z))
}

///  Point + (dx, dy, dz) = point.
pub fn add_vec3_exec<R: RuntimeRingOps<V>, V: OrderedField>(
    p: &RuntimePoint3<R, V>,
    dx: &R, dy: &R, dz: &R,
) -> (out: RuntimePoint3<R, V>)
    requires p.wf_spec(), dx.wf_spec(), dy.wf_spec(), dz.wf_spec(),
    ensures
        out.wf_spec(),
        out.model@.x == p.model@.x.add(dx.rf_view()),
        out.model@.y == p.model@.y.add(dy.rf_view()),
        out.model@.z == p.model@.z.add(dz.rf_view()),
{
    let rx = p.x.rf_add(dx);
    let ry = p.y.rf_add(dy);
    let rz = p.z.rf_add(dz);
    let ghost model = Point3 {
        x: p.model@.x.add(dx.rf_view()),
        y: p.model@.y.add(dy.rf_view()),
        z: p.model@.z.add(dz.rf_view()),
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
        out.0.rf_view() == uy.rf_view().mul(vz.rf_view()).sub(uz.rf_view().mul(vy.rf_view())),
        out.1.rf_view() == uz.rf_view().mul(vx.rf_view()).sub(ux.rf_view().mul(vz.rf_view())),
        out.2.rf_view() == ux.rf_view().mul(vy.rf_view()).sub(uy.rf_view().mul(vx.rf_view())),
{
    let a = uy.rf_mul(vz).rf_sub(&uz.rf_mul(vy));
    let b = uz.rf_mul(vx).rf_sub(&ux.rf_mul(vz));
    let c = ux.rf_mul(vy).rf_sub(&uy.rf_mul(vx));
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
        out.rf_view() == ux.rf_view().mul(vx.rf_view())
            .add(uy.rf_view().mul(vy.rf_view()))
            .add(uz.rf_view().mul(vz.rf_view())),
{
    let a = ux.rf_mul(vx);
    let b = uy.rf_mul(vy);
    let c = uz.rf_mul(vz);
    a.rf_add(&b).rf_add(&c)
}

} //  verus!
