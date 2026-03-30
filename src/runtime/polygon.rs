#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::field::OrderedField;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;
#[cfg(verus_keep_ghost)]
use super::point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use super::classification::orient2d_sign_exec;
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use crate::orientation_sign::*;
#[cfg(verus_keep_ghost)]
use crate::convex_polygon::*;
#[cfg(verus_keep_ghost)]
use crate::convexity::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimePolygon2<R, V: OrderedField> where R: RuntimeOrderedFieldOps<V> {
    pub vertices: Vec<RuntimePoint2<R, V>>,
}

impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> RuntimePolygon2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        forall|i: int| 0 <= i < self.vertices@.len() ==>
            (#[trigger] self.vertices@[i]).wf_spec()
    }

    pub open spec fn model(&self) -> Seq<Point2<V>> {
        Seq::new(self.vertices@.len(), |i: int| self.vertices@[i].model@)
    }

    pub fn len(&self) -> (out: usize)
        ensures out == self.vertices@.len(),
    {
        self.vertices.len()
    }

    pub fn get(&self, i: usize) -> (out: &RuntimePoint2<R, V>)
        requires i < self.vertices@.len(),
        ensures
            out.wf_spec() == self.vertices@[i as int].wf_spec(),
            out.model@ == self.vertices@[i as int].model@,
    {
        &self.vertices[i]
    }
}

pub fn is_positive(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Positive),
{
    match s { OrientationSign::Positive => true, _ => false }
}

pub fn is_negative(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Negative),
{
    match s { OrientationSign::Negative => true, _ => false }
}

pub fn is_zero(s: &OrientationSign) -> (out: bool)
    ensures out == (*s == OrientationSign::Zero),
{
    match s { OrientationSign::Zero => true, _ => false }
}

pub fn point_in_convex_polygon_boundary_inclusive_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        p.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == point_in_convex_polygon_boundary_inclusive::<V>(
            p.model@, polygon.model(),
        ),
{
    let n = polygon.len();
    let mut has_positive = false;
    let mut has_negative = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            p.wf_spec(),
            polygon.wf_spec(),
            has_positive == polygon_prefix_has_positive_sign::<V>(
                p.model@, polygon.model(), i as int,
            ),
            has_negative == polygon_prefix_has_negative_sign::<V>(
                p.model@, polygon.model(), i as int,
            ),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let sign = orient2d_sign_exec(vi, vj, p);

        let sp = is_positive(&sign);
        let sn = is_negative(&sign);

        if sp { has_positive = true; }
        if sn { has_negative = true; }

        proof {
            if has_positive {
                if sp {
                    assert(polygon_edge_orient_sign::<V>(
                        p.model@, polygon.model(), i as int,
                    ) == OrientationSign::Positive);
                }
                assert(polygon_prefix_has_positive_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if has_negative {
                if sn {
                    assert(polygon_edge_orient_sign::<V>(
                        p.model@, polygon.model(), i as int,
                    ) == OrientationSign::Negative);
                }
                assert(polygon_prefix_has_negative_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_positive {
                assert(!polygon_prefix_has_positive_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_negative {
                assert(!polygon_prefix_has_negative_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
        }

        i = i + 1;
    }

    !(has_positive && has_negative)
}

pub fn point_strictly_in_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    p: &RuntimePoint2<R, V>, polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        p.wf_spec(),
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == point_strictly_in_convex_polygon::<V>(
            p.model@, polygon.model(),
        ),
{
    let n = polygon.len();
    let mut has_positive = false;
    let mut has_negative = false;
    let mut has_zero = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            p.wf_spec(),
            polygon.wf_spec(),
            has_positive == polygon_prefix_has_positive_sign::<V>(
                p.model@, polygon.model(), i as int,
            ),
            has_negative == polygon_prefix_has_negative_sign::<V>(
                p.model@, polygon.model(), i as int,
            ),
            has_zero == polygon_prefix_has_zero_sign::<V>(
                p.model@, polygon.model(), i as int,
            ),
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let sign = orient2d_sign_exec(vi, vj, p);

        let sp = is_positive(&sign);
        let sn = is_negative(&sign);
        let sz = is_zero(&sign);

        if sp { has_positive = true; }
        if sn { has_negative = true; }
        if sz { has_zero = true; }

        proof {
            if has_positive {
                if sp {
                    assert(polygon_edge_orient_sign::<V>(
                        p.model@, polygon.model(), i as int,
                    ) == OrientationSign::Positive);
                }
                assert(polygon_prefix_has_positive_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if has_negative {
                if sn {
                    assert(polygon_edge_orient_sign::<V>(
                        p.model@, polygon.model(), i as int,
                    ) == OrientationSign::Negative);
                }
                assert(polygon_prefix_has_negative_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if has_zero {
                if sz {
                    assert(polygon_edge_orient_sign::<V>(
                        p.model@, polygon.model(), i as int,
                    ) == OrientationSign::Zero);
                }
                assert(polygon_prefix_has_zero_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_positive {
                assert(!polygon_prefix_has_positive_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_negative {
                assert(!polygon_prefix_has_negative_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
            if !has_zero {
                assert(!polygon_prefix_has_zero_sign::<V>(
                    p.model@, polygon.model(), (i + 1) as int,
                ));
            }
        }

        i = i + 1;
    }

    !(has_positive && has_negative) && !has_zero
}

pub fn is_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == is_convex_polygon::<V>(polygon.model()),
{
    let n = polygon.len();
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            polygon.wf_spec(),
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < n as int ==> {
                let next_ii = polygon_next_index(n as int, ii);
                !orient2d_negative::<V>(
                    #[trigger] polygon.model()[ii], polygon.model()[next_ii],
                    #[trigger] polygon.model()[jj],
                )
            },
        decreases n - i,
    {
        let next_i: usize = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vnext = polygon.get(next_i);

        let mut j: usize = 0;

        while j < n
            invariant
                n == polygon.vertices@.len(),
                n >= 3,
                0 <= i < n,
                0 <= j <= n,
                polygon.wf_spec(),
                next_i < n,
                next_i as int == polygon_next_index(n as int, i as int),
                vi.wf_spec(),
                vnext.wf_spec(),
                vi.model@ == polygon.model()[i as int],
                vnext.model@ == polygon.model()[next_i as int],
                forall|jj: int| 0 <= jj < j ==> {
                    let next_ii = polygon_next_index(n as int, i as int);
                    !orient2d_negative::<V>(
                        polygon.model()[i as int], polygon.model()[next_ii],
                        #[trigger] polygon.model()[jj],
                    )
                },
            decreases n - j,
        {
            let vj = polygon.get(j);
            let sign = orient2d_sign_exec(vi, vnext, vj);

            proof {
                lemma_orient2d_sign_matches::<V>(vi.model@, vnext.model@, vj.model@);
            }

            if is_negative(&sign) {
                proof {
                    assert(orient2d_negative::<V>(
                        polygon.model()[i as int],
                        polygon.model()[polygon_next_index(n as int, i as int)],
                        polygon.model()[j as int],
                    ));
                }
                return false;
            }

            j = j + 1;
        }

        proof {
            assert forall|jj: int| 0 <= jj < n as int implies {
                let next_ii = polygon_next_index(n as int, i as int);
                !orient2d_negative::<V>(
                    #[trigger] polygon.model()[i as int], polygon.model()[next_ii],
                    #[trigger] polygon.model()[jj],
                )
            } by {}
        }

        i = i + 1;
    }

    true
}

pub fn is_strictly_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == is_strictly_convex_polygon::<V>(polygon.model()),
{
    let n = polygon.len();
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            polygon.wf_spec(),
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < n as int ==> {
                let next_ii = polygon_next_index(n as int, ii);
                !orient2d_negative::<V>(
                    #[trigger] polygon.model()[ii], polygon.model()[next_ii],
                    #[trigger] polygon.model()[jj],
                )
            },
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < n as int
                && jj != ii && jj != polygon_next_index(n as int, ii)
                ==> {
                let next_ii = polygon_next_index(n as int, ii);
                orient2d_positive::<V>(
                    #[trigger] polygon.model()[ii], polygon.model()[next_ii],
                    #[trigger] polygon.model()[jj],
                )
            },
        decreases n - i,
    {
        let next_i: usize = if i + 1 < n { i + 1 } else { 0 };
        let vi = polygon.get(i);
        let vnext = polygon.get(next_i);

        let mut j: usize = 0;

        while j < n
            invariant
                n == polygon.vertices@.len(),
                n >= 3,
                0 <= i < n,
                0 <= j <= n,
                polygon.wf_spec(),
                next_i < n,
                next_i as int == polygon_next_index(n as int, i as int),
                vi.wf_spec(),
                vnext.wf_spec(),
                vi.model@ == polygon.model()[i as int],
                vnext.model@ == polygon.model()[next_i as int],
                forall|jj: int| 0 <= jj < j ==> {
                    !orient2d_negative::<V>(
                        polygon.model()[i as int],
                        polygon.model()[polygon_next_index(n as int, i as int)],
                        #[trigger] polygon.model()[jj],
                    )
                },
                forall|jj: int| 0 <= jj < j
                    && jj != i as int
                    && jj != polygon_next_index(n as int, i as int)
                    ==> {
                    orient2d_positive::<V>(
                        polygon.model()[i as int],
                        polygon.model()[polygon_next_index(n as int, i as int)],
                        #[trigger] polygon.model()[jj],
                    )
                },
            decreases n - j,
        {
            let vj = polygon.get(j);

            proof {
                assert(polygon.model()[i as int] == polygon.vertices@[i as int].model@);
                assert(polygon.model()[next_i as int] == polygon.vertices@[next_i as int].model@);
                assert(polygon.model()[j as int] == polygon.vertices@[j as int].model@);
            }

            let sign = orient2d_sign_exec(vi, vnext, vj);

            proof {
                lemma_orient2d_sign_matches::<V>(vi.model@, vnext.model@, vj.model@);
            }

            if is_negative(&sign) {
                return false;
            }

            if j != i && j != next_i && !is_positive(&sign) {
                proof {
                    assert(!orient2d_positive::<V>(
                        polygon.model()[i as int],
                        polygon.model()[polygon_next_index(n as int, i as int)],
                        polygon.model()[j as int],
                    ));
                }
                return false;
            }

            j = j + 1;
        }

        i = i + 1;
    }

    true
}

pub fn is_locally_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == is_locally_convex_polygon::<V>(polygon.model()),
{
    let n = polygon.len();
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            polygon.wf_spec(),
            forall|k: int| 0 <= k < i ==> {
                let j = polygon_next_index(n as int, k);
                let m = polygon_next_index(n as int, j);
                !orient2d_negative::<V>(
                    #[trigger] polygon.model()[k], polygon.model()[j], polygon.model()[m],
                )
            },
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let k = if j + 1 < n { j + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let vk = polygon.get(k);
        let sign = orient2d_sign_exec(vi, vj, vk);

        proof {
            assert(polygon.model()[i as int] == polygon.vertices@[i as int].model@);
            assert(polygon.model()[j as int] == polygon.vertices@[j as int].model@);
            assert(polygon.model()[k as int] == polygon.vertices@[k as int].model@);
            lemma_orient2d_sign_matches::<V>(vi.model@, vj.model@, vk.model@);
        }

        if is_negative(&sign) {
            return false;
        }

        i = i + 1;
    }

    true
}

pub fn is_locally_strictly_convex_polygon_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    polygon: &RuntimePolygon2<R, V>,
) -> (out: bool)
    requires
        polygon.wf_spec(),
        polygon.vertices@.len() >= 3,
    ensures
        out == is_locally_strictly_convex_polygon::<V>(polygon.model()),
{
    let n = polygon.len();
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.vertices@.len(),
            n >= 3,
            0 <= i <= n,
            polygon.wf_spec(),
            forall|k: int| 0 <= k < i ==> {
                let j = polygon_next_index(n as int, k);
                let m = polygon_next_index(n as int, j);
                orient2d_positive::<V>(
                    #[trigger] polygon.model()[k], polygon.model()[j], polygon.model()[m],
                )
            },
        decreases n - i,
    {
        let j = if i + 1 < n { i + 1 } else { 0 };
        let k = if j + 1 < n { j + 1 } else { 0 };
        let vi = polygon.get(i);
        let vj = polygon.get(j);
        let vk = polygon.get(k);
        let sign = orient2d_sign_exec(vi, vj, vk);

        proof {
            assert(polygon.model()[i as int] == polygon.vertices@[i as int].model@);
            assert(polygon.model()[j as int] == polygon.vertices@[j as int].model@);
            assert(polygon.model()[k as int] == polygon.vertices@[k as int].model@);
            lemma_orient2d_sign_matches::<V>(vi.model@, vj.model@, vk.model@);
        }

        if !is_positive(&sign) {
            return false;
        }

        i = i + 1;
    }

    true
}

} //  verus!
