use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::point3::{RuntimePoint3, RuntimeVec3, sub3_exec, add_vec3_exec};
#[cfg(verus_keep_ghost)]
use crate::segment_distance::*;
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::ops::{dot, scale, norm_sq};

#[cfg(verus_keep_ghost)]
verus! {

///  Compute the 5 Gram matrix entries for lines (a,b) and (c,d).
pub fn gram_entries_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: (RuntimeRational, RuntimeRational, RuntimeRational, RuntimeRational, RuntimeRational))
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures ({
        let (uu, vv, uv, uw, vw) = out;
        let (suu, svv, suv, suw, svw) = gram_entries::<RationalModel>(a@, b@, c@, d@);
        &&& uu.wf_spec() && uu@ == suu
        &&& vv.wf_spec() && vv@ == svv
        &&& uv.wf_spec() && uv@ == suv
        &&& uw.wf_spec() && uw@ == suw
        &&& vw.wf_spec() && vw@ == svw
    }),
{
    let u = sub3_exec(b, a);
    let v = sub3_exec(d, c);
    let w = sub3_exec(a, c);
    let uu = u.dot_exec(&u);
    let vv = v.dot_exec(&v);
    let uv = u.dot_exec(&v);
    let uw = u.dot_exec(&w);
    let vw = v.dot_exec(&w);
    (uu, vv, uv, uw, vw)
}

///  Compute the Gram determinant: uu*vv - uv^2.
pub fn gram_determinant_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == gram_determinant::<RationalModel>(a@, b@, c@, d@),
{
    let (uu, vv, uv, _, _) = gram_entries_exec(a, b, c, d);
    uu.mul(&vv).sub(&uv.mul(&uv))
}

///  Closest-approach parameter s on line (a,b).
pub fn closest_parameter_s_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
        !gram_determinant::<RationalModel>(a@, b@, c@, d@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_s::<RationalModel>(a@, b@, c@, d@),
{
    let (uu, vv, uv, uw, vw) = gram_entries_exec(a, b, c, d);
    let denom = uu.mul(&vv).sub(&uv.mul(&uv));
    let numer = uv.mul(&vw).sub(&vv.mul(&uw));
    numer.div(&denom)
}

///  Closest-approach parameter t on line (c,d).
pub fn closest_parameter_t_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
        !gram_determinant::<RationalModel>(a@, b@, c@, d@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == closest_parameter_t::<RationalModel>(a@, b@, c@, d@),
{
    let (uu, vv, uv, uw, vw) = gram_entries_exec(a, b, c, d);
    let denom = uu.mul(&vv).sub(&uv.mul(&uv));
    let numer = uu.mul(&vw).sub(&uv.mul(&uw));
    numer.div(&denom)
}

///  Squared distance between closest approach points on two lines.
pub fn line_line_squared_distance_exec(
    a: &RuntimePoint3, b: &RuntimePoint3,
    c: &RuntimePoint3, d: &RuntimePoint3,
) -> (out: RuntimeRational)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        d.wf_spec(),
        !gram_determinant::<RationalModel>(a@, b@, c@, d@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == line_line_squared_distance::<RationalModel>(a@, b@, c@, d@),
{
    let s = closest_parameter_s_exec(a, b, c, d);
    let t = closest_parameter_t_exec(a, b, c, d);
    //  p1 = a + s*(b-a)
    let u = sub3_exec(b, a);
    let su = RuntimeVec3::scale_exec(&s, &u);
    let p1 = add_vec3_exec(a, &su);
    //  p2 = c + t*(d-c)
    let v = sub3_exec(d, c);
    let tv = RuntimeVec3::scale_exec(&t, &v);
    let p2 = add_vec3_exec(c, &tv);
    //  ||p1 - p2||^2
    let diff = sub3_exec(&p1, &p2);
    diff.norm_sq_exec()
}

} //  verus!
