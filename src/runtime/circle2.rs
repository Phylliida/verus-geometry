use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use crate::circle2::*;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeCircle2
// ---------------------------------------------------------------------------

pub struct RuntimeCircle2 {
    pub center: RuntimePoint2,
    pub radius_sq: RuntimeRational,
    pub model: Ghost<Circle2<RationalModel>>,
}

impl View for RuntimeCircle2 {
    type V = Circle2<RationalModel>;

    open spec fn view(&self) -> Circle2<RationalModel> {
        self.model@
    }
}

impl RuntimeCircle2 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.center.wf_spec()
        &&& self.radius_sq.wf_spec()
        &&& self.center@ == self@.center
        &&& self.radius_sq@ == self@.radius_sq
    }

    pub fn from_center_radius_sq(
        center: RuntimePoint2,
        radius_sq: RuntimeRational,
    ) -> (out: Self)
        requires
            center.wf_spec(),
            radius_sq.wf_spec(),
        ensures
            out.wf_spec(),
            out@.center == center@,
            out@.radius_sq == radius_sq@,
    {
        let ghost model = Circle2 { center: center@, radius_sq: radius_sq@ };
        RuntimeCircle2 { center, radius_sq, model: Ghost(model) }
    }
}

} // verus!
