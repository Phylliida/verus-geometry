use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::point2::{Point2, sub2, add_vec2};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec2::Vec2;

pub use verus_linalg::runtime::vec2::RuntimeVec2;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimePoint2
//  ---------------------------------------------------------------------------

pub struct RuntimePoint2 {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub model: Ghost<Point2<RationalModel>>,
}

impl View for RuntimePoint2 {
    type V = Point2<RationalModel>;

    open spec fn view(&self) -> Point2<RationalModel> {
        self.model@
    }
}

impl RuntimePoint2 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
    }

    pub fn new(x: RuntimeRational, y: RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
        ensures
            out.wf_spec(),
            out@.x == x@,
            out@.y == y@,
    {
        let ghost model = Point2 { x: x@, y: y@ };
        RuntimePoint2 { x, y, model: Ghost(model) }
    }

    pub fn from_ints(x: i64, y: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        Self::new(rx, ry)
    }
}

//  ---------------------------------------------------------------------------
//  Exec operations
//  ---------------------------------------------------------------------------

///  Point subtraction: a - b = vector
pub fn sub2_exec(a: &RuntimePoint2, b: &RuntimePoint2) -> (out: RuntimeVec2)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == sub2::<RationalModel>(a@, b@),
{
    let dx = a.x.sub(&b.x);
    let dy = a.y.sub(&b.y);
    let ghost model = sub2::<RationalModel>(a@, b@);
    RuntimeVec2 { x: dx, y: dy, model: Ghost(model) }
}

///  Point + vector = point
pub fn add_vec2_exec(p: &RuntimePoint2, v: &RuntimeVec2) -> (out: RuntimePoint2)
    requires
        p.wf_spec(),
        v.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == add_vec2::<RationalModel>(p@, v@),
{
    let rx = p.x.add(&v.x);
    let ry = p.y.add(&v.y);
    let ghost model = add_vec2::<RationalModel>(p@, v@);
    RuntimePoint2 { x: rx, y: ry, model: Ghost(model) }
}

} //  verus!
