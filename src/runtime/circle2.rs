#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use crate::circle2::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::RuntimeRingOps;

#[cfg(verus_keep_ghost)]
verus! {

///  A runtime 2D circle (center + radius_sq), generic over any runtime field.
pub struct RuntimeCircle2<R, V: OrderedField> where R: RuntimeRingOps<V> {
    pub center: RuntimePoint2<R, V>,
    pub radius_sq: R,
    pub model: Ghost<Circle2<V>>,
}

impl<R: RuntimeRingOps<V>, V: OrderedField> View for RuntimeCircle2<R, V> {
    type V = Circle2<V>;

    open spec fn view(&self) -> Circle2<V> {
        self.model@
    }
}

impl<R: RuntimeRingOps<V>, V: OrderedField> RuntimeCircle2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.center.wf_spec()
        &&& self.radius_sq.wf_spec()
        &&& self.center.model@ == self.model@.center
        &&& self.radius_sq@ == self.model@.radius_sq
    }

    pub fn from_center_radius_sq(
        center: RuntimePoint2<R, V>,
        radius_sq: R,
    ) -> (out: Self)
        requires center.wf_spec(), radius_sq.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.center == center.model@,
            out.model@.radius_sq == radius_sq@,
    {
        let ghost model = Circle2 { center: center.model@, radius_sq: radius_sq@ };
        RuntimeCircle2 { center, radius_sq, model: Ghost(model) }
    }
}

} //  verus!
