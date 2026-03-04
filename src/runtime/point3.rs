use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::point3::{Point3, sub3, add_vec3};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{cross, dot};

pub use verus_linalg::runtime::vec3::RuntimeVec3;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimePoint3
// ---------------------------------------------------------------------------

pub struct RuntimePoint3 {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub z: RuntimeRational,
    pub model: Ghost<Point3<RationalModel>>,
}

impl View for RuntimePoint3 {
    type V = Point3<RationalModel>;

    open spec fn view(&self) -> Point3<RationalModel> {
        self.model@
    }
}

impl RuntimePoint3 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.z@ == self@.z
    }

    pub fn new(x: RuntimeRational, y: RuntimeRational, z: RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
            z.wf_spec(),
        ensures
            out.wf_spec(),
            out@.x == x@,
            out@.y == y@,
            out@.z == z@,
    {
        let ghost model = Point3 { x: x@, y: y@, z: z@ };
        RuntimePoint3 { x, y, z, model: Ghost(model) }
    }

    pub fn from_ints(x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        let rz = RuntimeRational::from_int(z);
        Self::new(rx, ry, rz)
    }
}

// ---------------------------------------------------------------------------
// Exec operations
// ---------------------------------------------------------------------------

/// Point subtraction: a - b = vector
pub fn sub3_exec(a: &RuntimePoint3, b: &RuntimePoint3) -> (out: RuntimeVec3)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == sub3::<RationalModel>(a@, b@),
{
    let dx = a.x.sub(&b.x);
    let dy = a.y.sub(&b.y);
    let dz = a.z.sub(&b.z);
    let ghost model = sub3::<RationalModel>(a@, b@);
    RuntimeVec3 { x: dx, y: dy, z: dz, model: Ghost(model) }
}

/// Point + vector = point
pub fn add_vec3_exec(p: &RuntimePoint3, v: &RuntimeVec3) -> (out: RuntimePoint3)
    requires
        p.wf_spec(),
        v.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == add_vec3::<RationalModel>(p@, v@),
{
    let rx = p.x.add(&v.x);
    let ry = p.y.add(&v.y);
    let rz = p.z.add(&v.z);
    let ghost model = add_vec3::<RationalModel>(p@, v@);
    RuntimePoint3 { x: rx, y: ry, z: rz, model: Ghost(model) }
}

/// Cross product: a × b (delegates to verus-linalg)
pub fn cross_exec(a: &RuntimeVec3, b: &RuntimeVec3) -> (out: RuntimeVec3)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == cross::<RationalModel>(a@, b@),
{
    a.cross_exec(b)
}

/// Dot product: a · b (delegates to verus-linalg)
pub fn dot3_exec(a: &RuntimeVec3, b: &RuntimeVec3) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == dot::<RationalModel>(a@, b@),
{
    a.dot_exec(b)
}

} // verus!
