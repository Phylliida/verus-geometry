use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::line2::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeLine2
//  ---------------------------------------------------------------------------

pub struct RuntimeLine2 {
    pub a: RuntimeRational,
    pub b: RuntimeRational,
    pub c: RuntimeRational,
    pub model: Ghost<Line2<RationalModel>>,
}

impl View for RuntimeLine2 {
    type V = Line2<RationalModel>;

    open spec fn view(&self) -> Line2<RationalModel> {
        self.model@
    }
}

impl RuntimeLine2 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.a.wf_spec()
        &&& self.b.wf_spec()
        &&& self.c.wf_spec()
        &&& self.a@ == self@.a
        &&& self.b@ == self@.b
        &&& self.c@ == self@.c
    }

    pub fn new(a: RuntimeRational, b: RuntimeRational, c: RuntimeRational) -> (out: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            out.wf_spec(),
            out@.a == a@,
            out@.b == b@,
            out@.c == c@,
    {
        let ghost model = Line2 { a: a@, b: b@, c: c@ };
        RuntimeLine2 { a, b, c, model: Ghost(model) }
    }
}

//  ---------------------------------------------------------------------------
//  Exec constructors
//  ---------------------------------------------------------------------------

///  Construct a line through two points.
pub fn line2_from_points_exec(
    p: &super::point2::RuntimePoint2,
    q: &super::point2::RuntimePoint2,
) -> (out: RuntimeLine2)
    requires
        p.wf_spec(),
        q.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == line2_from_points::<RationalModel>(p@, q@),
{
    //  a = -(q.y - p.y)
    let dy = q.y.sub(&p.y);
    let a = dy.neg();
    //  b = q.x - p.x
    let b = q.x.sub(&p.x);
    //  c = -(a*p.x + b*p.y)
    let apx = a.mul(&p.x);
    let bpy = b.mul(&p.y);
    let s = apx.add(&bpy);
    let c = s.neg();

    let ghost model = line2_from_points::<RationalModel>(p@, q@);
    RuntimeLine2 { a, b, c, model: Ghost(model) }
}

///  Evaluate the line equation at a point.
pub fn line2_eval_exec(
    line: &RuntimeLine2,
    p: &super::point2::RuntimePoint2,
) -> (out: RuntimeRational)
    requires
        line.wf_spec(),
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == line2_eval::<RationalModel>(line@, p@),
{
    let apx = line.a.mul(&p.x);
    let bpy = line.b.mul(&p.y);
    let s = apx.add(&bpy);
    s.add(&line.c)
}

} //  verus!
