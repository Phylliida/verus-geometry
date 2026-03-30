#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use crate::segment_distance::*;

#[cfg(verus_keep_ghost)]
verus! {

pub fn gram_entries_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: (R, R, R, R, R))
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures ({
        let (uu, vv, uv, uw, vw) = out;
        let (suu, svv, suv, suw, svw) = gram_entries::<V>(a.model@, b.model@, c.model@, d.model@);
        &&& uu.wf_spec() && uu.model() == suu
        &&& vv.wf_spec() && vv.model() == svv
        &&& uv.wf_spec() && uv.model() == suv
        &&& uw.wf_spec() && uw.model() == suw
        &&& vw.wf_spec() && vw.model() == svw
    }),
{
    let u = b.sub(a);
    let v = d.sub(c);
    let w = a.sub(c);
    (u.dot(&u), v.dot(&v), u.dot(&v), u.dot(&w), v.dot(&w))
}

pub fn gram_determinant_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: R)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
    ensures out.wf_spec(), out.model() == gram_determinant::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let (uu, vv, uv, _, _) = gram_entries_exec(a, b, c, d);
    uu.mul(&vv).sub(&uv.mul(&uv))
}

pub fn closest_parameter_s_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        !gram_determinant::<V>(a.model@, b.model@, c.model@, d.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model() == closest_parameter_s::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let (uu, vv, uv, uw, vw) = gram_entries_exec(a, b, c, d);
    let denom = uu.mul(&vv).sub(&uv.mul(&uv));
    let numer = uv.mul(&vw).sub(&vv.mul(&uw));
    numer.div(&denom)
}

pub fn closest_parameter_t_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        !gram_determinant::<V>(a.model@, b.model@, c.model@, d.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model() == closest_parameter_t::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let (uu, vv, uv, uw, vw) = gram_entries_exec(a, b, c, d);
    let denom = uu.mul(&vv).sub(&uv.mul(&uv));
    let numer = uu.mul(&vw).sub(&uv.mul(&uw));
    numer.div(&denom)
}

pub fn line_line_squared_distance_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>, b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>, d: &RuntimePoint3<R, V>,
) -> (out: R)
    requires
        a.wf_spec(), b.wf_spec(), c.wf_spec(), d.wf_spec(),
        !gram_determinant::<V>(a.model@, b.model@, c.model@, d.model@).eqv(V::zero()),
    ensures
        out.wf_spec(),
        out.model() == line_line_squared_distance::<V>(a.model@, b.model@, c.model@, d.model@),
{
    let s = closest_parameter_s_exec(a, b, c, d);
    let t = closest_parameter_t_exec(a, b, c, d);
    let p1 = a.add(&b.sub(a).scale(&s));
    let p2 = c.add(&d.sub(c).scale(&t));
    p1.sub(&p2).norm_sq()
}

} //  verus!
