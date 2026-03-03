use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ordered_field_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::point2::*;
use crate::point3::*;
use crate::orient2d::*;
use crate::orient3d::*;

verus! {

// ---------------------------------------------------------------------------
// OrientationSign enum
// ---------------------------------------------------------------------------

/// Classification of an orientation determinant's sign.
#[derive(PartialEq, Eq)]
pub enum OrientationSign {
    Positive,
    Zero,
    Negative,
}

// ---------------------------------------------------------------------------
// Sign extraction spec functions (require OrderedRing)
// ---------------------------------------------------------------------------

/// Classify the sign of orient2d(a, b, c).
pub open spec fn orient2d_sign<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> OrientationSign {
    let val = orient2d(a, b, c);
    if T::zero().lt(val) {
        OrientationSign::Positive
    } else if val.lt(T::zero()) {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

/// Classify the sign of orient3d(a, b, c, d).
pub open spec fn orient3d_sign<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> OrientationSign {
    let val = orient3d(a, b, c, d);
    if T::zero().lt(val) {
        OrientationSign::Positive
    } else if val.lt(T::zero()) {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

// ---------------------------------------------------------------------------
// Strict positivity / negativity / zero predicates
// ---------------------------------------------------------------------------

/// orient2d(a, b, c) > 0
pub open spec fn orient2d_positive<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    T::zero().lt(orient2d(a, b, c))
}

/// orient2d(a, b, c) < 0
pub open spec fn orient2d_negative<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    orient2d(a, b, c).lt(T::zero())
}

/// orient2d(a, b, c) ≡ 0
pub open spec fn orient2d_zero<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
) -> bool {
    orient2d(a, b, c).eqv(T::zero())
}

/// orient3d(a, b, c, d) > 0
pub open spec fn orient3d_positive<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> bool {
    T::zero().lt(orient3d(a, b, c, d))
}

/// orient3d(a, b, c, d) < 0
pub open spec fn orient3d_negative<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> bool {
    orient3d(a, b, c, d).lt(T::zero())
}

/// orient3d(a, b, c, d) ≡ 0
pub open spec fn orient3d_zero<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
) -> bool {
    orient3d(a, b, c, d).eqv(T::zero())
}

// ---------------------------------------------------------------------------
// Trichotomy lemmas — exactly one of {positive, negative, zero} holds
// ---------------------------------------------------------------------------

/// Exactly one of orient2d_positive, orient2d_negative, orient2d_zero holds.
pub proof fn lemma_orient2d_trichotomy<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        // At least one holds
        orient2d_positive(a, b, c) || orient2d_negative(a, b, c) || orient2d_zero(a, b, c),
        // Mutual exclusion
        !(orient2d_positive(a, b, c) && orient2d_negative(a, b, c)),
        !(orient2d_positive(a, b, c) && orient2d_zero(a, b, c)),
        !(orient2d_negative(a, b, c) && orient2d_zero(a, b, c)),
{
    let val = orient2d(a, b, c);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    // trichotomy gives: 0 < val || 0 ≡ val || val < 0
    // and mutual exclusion of all three

    // If 0 ≡ val, then val ≡ 0 (symmetric)
    if T::zero().eqv(val) {
        T::axiom_eqv_symmetric(T::zero(), val);
    }

    // Mutual exclusion: positive && zero impossible
    if orient2d_positive(a, b, c) && orient2d_zero(a, b, c) {
        // 0 < val and val ≡ 0
        // val ≡ 0 implies 0 ≡ val (symmetric)
        T::axiom_eqv_symmetric(val, T::zero());
        // But trichotomy says !(0 < val && 0 ≡ val)
    }

    // Mutual exclusion: negative && zero impossible
    if orient2d_negative(a, b, c) && orient2d_zero(a, b, c) {
        // val < 0 and val ≡ 0
        // val ≡ 0 implies val < 0 contradicts trichotomy(val, 0)
        ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());
    }
}

/// Exactly one of orient3d_positive, orient3d_negative, orient3d_zero holds.
pub proof fn lemma_orient3d_trichotomy<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d_positive(a, b, c, d) || orient3d_negative(a, b, c, d) || orient3d_zero(a, b, c, d),
        !(orient3d_positive(a, b, c, d) && orient3d_negative(a, b, c, d)),
        !(orient3d_positive(a, b, c, d) && orient3d_zero(a, b, c, d)),
        !(orient3d_negative(a, b, c, d) && orient3d_zero(a, b, c, d)),
{
    let val = orient3d(a, b, c, d);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);

    if T::zero().eqv(val) {
        T::axiom_eqv_symmetric(T::zero(), val);
    }

    if orient3d_positive(a, b, c, d) && orient3d_zero(a, b, c, d) {
        T::axiom_eqv_symmetric(val, T::zero());
    }

    if orient3d_negative(a, b, c, d) && orient3d_zero(a, b, c, d) {
        ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());
    }
}

// ---------------------------------------------------------------------------
// Sign matches predicates
// ---------------------------------------------------------------------------

/// orient2d_sign classifies correctly w.r.t. the predicates.
pub proof fn lemma_orient2d_sign_matches<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        (orient2d_sign(a, b, c) == OrientationSign::Positive) == orient2d_positive(a, b, c),
        (orient2d_sign(a, b, c) == OrientationSign::Negative) == orient2d_negative(a, b, c),
        (orient2d_sign(a, b, c) == OrientationSign::Zero) == orient2d_zero(a, b, c),
{
    let val = orient2d(a, b, c);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());

    // Zero case: sign is Zero iff val ≡ 0
    // sign == Zero means !0.lt(val) && !val.lt(0)
    // By trichotomy(0, val): 0 < val || 0 ≡ val || val < 0
    // If !0.lt(val) && !val.lt(0), then 0 ≡ val, so val ≡ 0

    if T::zero().eqv(val) {
        T::axiom_eqv_symmetric(T::zero(), val);
    }
    if val.eqv(T::zero()) {
        T::axiom_eqv_symmetric(val, T::zero());
    }
}

/// orient3d_sign classifies correctly w.r.t. the predicates.
pub proof fn lemma_orient3d_sign_matches<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        (orient3d_sign(a, b, c, d) == OrientationSign::Positive) == orient3d_positive(a, b, c, d),
        (orient3d_sign(a, b, c, d) == OrientationSign::Negative) == orient3d_negative(a, b, c, d),
        (orient3d_sign(a, b, c, d) == OrientationSign::Zero) == orient3d_zero(a, b, c, d),
{
    let val = orient3d(a, b, c, d);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());

    if T::zero().eqv(val) {
        T::axiom_eqv_symmetric(T::zero(), val);
    }
    if val.eqv(T::zero()) {
        T::axiom_eqv_symmetric(val, T::zero());
    }
}

// ---------------------------------------------------------------------------
// Degenerate cases give Zero
// ---------------------------------------------------------------------------

/// orient2d_sign(a, a, c) == Zero
pub proof fn lemma_orient2d_sign_degenerate_ab<T: OrderedRing>(
    a: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d_sign(a, a, c) == OrientationSign::Zero,
{
    lemma_orient2d_degenerate_ab::<T>(a, c);
    // orient2d(a, a, c) ≡ 0
    // So orient2d_zero(a, a, c) holds
    // By sign_matches, sign == Zero
    lemma_orient2d_sign_matches::<T>(a, a, c);
}

/// orient2d_sign(a, b, b) == Zero
pub proof fn lemma_orient2d_sign_degenerate_bc<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>,
)
    ensures
        orient2d_sign(a, b, b) == OrientationSign::Zero,
{
    lemma_orient2d_degenerate_bc::<T>(a, b);
    lemma_orient2d_sign_matches::<T>(a, b, b);
}

/// orient3d_sign(a, a, c, d) == Zero
pub proof fn lemma_orient3d_sign_degenerate_ab<T: OrderedRing>(
    a: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d_sign(a, a, c, d) == OrientationSign::Zero,
{
    lemma_orient3d_degenerate_ab::<T>(a, c, d);
    lemma_orient3d_sign_matches::<T>(a, a, c, d);
}

/// orient3d_sign(a, b, c, c) == Zero
pub proof fn lemma_orient3d_sign_degenerate_cd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>,
)
    ensures
        orient3d_sign(a, b, c, c) == OrientationSign::Zero,
{
    lemma_orient3d_degenerate_cd::<T>(a, b, c);
    lemma_orient3d_sign_matches::<T>(a, b, c, c);
}

// ---------------------------------------------------------------------------
// Swap reverses sign
// ---------------------------------------------------------------------------

/// If val ≡ -val2, then sign(val) is the reverse of sign(val2).
pub proof fn lemma_neg_flips_sign<T: OrderedRing>(val: T, val2: T)
    requires
        val.eqv(val2.neg()),
    ensures
        // positive <-> negative
        T::zero().lt(val) <==> val2.lt(T::zero()),
        val.lt(T::zero()) <==> T::zero().lt(val2),
        // zero <-> zero
        val.eqv(T::zero()) <==> val2.eqv(T::zero()),
{
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val2);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());
    ordered_ring_lemmas::lemma_trichotomy::<T>(val2, T::zero());

    // If val ≡ -val2:

    // zero <-> zero: val ≡ 0 iff val2 ≡ 0
    // val ≡ 0 and val ≡ -val2 means -val2 ≡ 0 means val2 ≡ -0 ≡ 0
    if val.eqv(T::zero()) {
        // -val2 ≡ val ≡ 0
        T::axiom_eqv_symmetric(val, val2.neg());
        T::axiom_eqv_transitive(val2.neg(), val, T::zero());
        // -val2 ≡ 0, so val2 ≡ -(-val2)... use neg_zero
        // -val2 ≡ 0 means val2 + (-val2) ≡ val2 + 0 ≡ val2
        // But val2 + (-val2) ≡ 0, so val2 ≡ 0? No...
        // Actually: -val2 ≡ 0, neg both sides: -(-val2) ≡ -0 ≡ 0
        // -(-val2) ≡ val2, so val2 ≡ 0
        additive_group_lemmas::lemma_neg_involution::<T>(val2);
        // neg_involution gives val2.neg().neg().eqv(val2), swap to get val2.eqv(val2.neg().neg())
        T::axiom_eqv_symmetric(val2.neg().neg(), val2);
        T::axiom_neg_congruence(val2.neg(), T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val2.neg().neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(val2, val2.neg().neg(), T::zero());
    }
    if val2.eqv(T::zero()) {
        // val ≡ -val2 ≡ -0 ≡ 0
        T::axiom_neg_congruence(val2, T::zero());
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_transitive(val2.neg(), T::zero().neg(), T::zero());
        T::axiom_eqv_transitive(val, val2.neg(), T::zero());
    }

    // positive -> negative: 0 < val implies val2 < 0
    // 0 < val and val ≡ -val2
    // 0 < -val2, i.e. val2 must be negative
    // By le_neg_flip: a ≤ b implies -b ≤ -a
    // 0 ≤ val (from 0 < val) and val ≡ -val2
    // We need: val2 < 0
    if T::zero().lt(val) {
        // 0 < val and val ≡ -val2
        // By congruence: 0 < -val2
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), val);
        // 0 ≤ val
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), val, val2.neg());
        // 0 ≤ -val2
        // le_neg_flip: 0 ≤ -val2 implies --val2 ≤ -0, i.e. val2 ≤ 0
        ordered_ring_lemmas::lemma_le_neg_flip::<T>(T::zero(), val2.neg());
        // -(-val2) ≤ -0
        additive_group_lemmas::lemma_neg_involution::<T>(val2);
        additive_group_lemmas::lemma_neg_zero::<T>();
        // val2 ≡ --val2
        T::axiom_eqv_symmetric(val2, val2.neg().neg());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(val2.neg().neg(), val2, T::zero().neg());
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(val2, T::zero().neg(), T::zero());
        // val2 ≤ 0
        // Also !val2 ≡ 0 (since if val2 ≡ 0 then val ≡ 0, contradicting 0 < val)
        T::axiom_lt_iff_le_and_not_eqv(val2, T::zero());
    }

    // negative -> positive: val < 0 implies 0 < val2
    if val.lt(T::zero()) {
        // val < 0 and val ≡ -val2
        T::axiom_lt_iff_le_and_not_eqv(val, T::zero());
        // val ≤ 0
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(val, val2.neg(), T::zero());
        // -val2 ≤ 0
        // le_neg_flip: -val2 ≤ 0 implies -0 ≤ --val2, i.e. 0 ≤ val2
        ordered_ring_lemmas::lemma_le_neg_flip::<T>(val2.neg(), T::zero());
        additive_group_lemmas::lemma_neg_involution::<T>(val2);
        additive_group_lemmas::lemma_neg_zero::<T>();
        T::axiom_eqv_symmetric(val2, val2.neg().neg());
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero().neg(), val2.neg().neg(), val2);
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(T::zero().neg(), T::zero(), val2);
        // 0 ≤ val2
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), val2);
    }

    // val2 < 0 -> 0 < val
    if val2.lt(T::zero()) {
        // -val2 > 0, and val ≡ -val2
        T::axiom_lt_iff_le_and_not_eqv(val2, T::zero());
        // val2 ≤ 0
        ordered_ring_lemmas::lemma_le_neg_flip::<T>(val2, T::zero());
        // -0 ≤ -val2, i.e. 0 ≤ -val2
        additive_group_lemmas::lemma_neg_zero::<T>();
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(T::zero().neg(), T::zero(), val2.neg());
        // 0 ≤ -val2
        // 0 ≤ val via congruence (val ≡ -val2)
        T::axiom_eqv_symmetric(val, val2.neg());
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(T::zero(), val2.neg(), val);
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), val);
    }

    // 0 < val2 -> val < 0
    if T::zero().lt(val2) {
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), val2);
        // 0 ≤ val2
        ordered_ring_lemmas::lemma_le_neg_flip::<T>(T::zero(), val2);
        // -val2 ≤ -0 ≡ 0
        additive_group_lemmas::lemma_neg_zero::<T>();
        ordered_ring_lemmas::lemma_le_congruence_right::<T>(val2.neg(), T::zero().neg(), T::zero());
        // -val2 ≤ 0, and val ≡ -val2
        T::axiom_eqv_symmetric(val, val2.neg());
        ordered_ring_lemmas::lemma_le_congruence_left::<T>(val2.neg(), val, T::zero());
        // val ≤ 0
        T::axiom_lt_iff_le_and_not_eqv(val, T::zero());
    }
}

/// Swapping b, c reverses the 2D orientation sign.
pub proof fn lemma_orient2d_sign_swap_bc<T: OrderedRing>(
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    ensures
        orient2d_sign(a, c, b) == match orient2d_sign(a, b, c) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    // orient2d(a, c, b) ≡ -orient2d(a, b, c)
    lemma_orient2d_swap_bc::<T>(a, b, c);
    let val = orient2d(a, b, c);
    let swapped = orient2d(a, c, b);
    // swapped ≡ val.neg()
    lemma_neg_flips_sign::<T>(swapped, val);
    lemma_orient2d_sign_matches::<T>(a, b, c);
    lemma_orient2d_sign_matches::<T>(a, c, b);
}

/// Swapping c, d reverses the 3D orientation sign.
pub proof fn lemma_orient3d_sign_swap_cd<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d_sign(a, b, d, c) == match orient3d_sign(a, b, c, d) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_orient3d_swap_cd::<T>(a, b, c, d);
    let val = orient3d(a, b, c, d);
    let swapped = orient3d(a, b, d, c);
    lemma_neg_flips_sign::<T>(swapped, val);
    lemma_orient3d_sign_matches::<T>(a, b, c, d);
    lemma_orient3d_sign_matches::<T>(a, b, d, c);
}

/// Swapping b, c reverses the 3D orientation sign.
pub proof fn lemma_orient3d_sign_swap_bc<T: OrderedRing>(
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    ensures
        orient3d_sign(a, c, b, d) == match orient3d_sign(a, b, c, d) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    lemma_orient3d_swap_bc::<T>(a, b, c, d);
    let val = orient3d(a, b, c, d);
    let swapped = orient3d(a, c, b, d);
    lemma_neg_flips_sign::<T>(swapped, val);
    lemma_orient3d_sign_matches::<T>(a, b, c, d);
    lemma_orient3d_sign_matches::<T>(a, c, b, d);
}

// ---------------------------------------------------------------------------
// Sign classification for arbitrary scalars
// ---------------------------------------------------------------------------

/// Classify the sign of an arbitrary scalar.
pub open spec fn scalar_sign<T: OrderedRing>(val: T) -> OrientationSign {
    if T::zero().lt(val) {
        OrientationSign::Positive
    } else if val.lt(T::zero()) {
        OrientationSign::Negative
    } else {
        OrientationSign::Zero
    }
}

// ---------------------------------------------------------------------------
// Sign invariant under positive scaling (requires OrderedField)
// ---------------------------------------------------------------------------

/// Multiplying by a positive scalar preserves sign.
pub proof fn lemma_scalar_sign_pos_scale<T: OrderedField>(s: T, val: T)
    requires
        T::zero().lt(s),
    ensures
        scalar_sign(s.mul(val)) == scalar_sign(val),
{
    ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), val);
    ordered_ring_lemmas::lemma_trichotomy::<T>(val, T::zero());

    if T::zero().lt(val) {
        // 0 < s, 0 < val → 0 < s*val
        ordered_field_lemmas::lemma_mul_pos_pos::<T>(s, val);
        ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), s.mul(val));
        ordered_ring_lemmas::lemma_trichotomy::<T>(s.mul(val), T::zero());
    } else if val.lt(T::zero()) {
        // 0 < s, val < 0 → s*val < 0
        ordered_field_lemmas::lemma_mul_pos_neg::<T>(s, val);
        ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), s.mul(val));
        ordered_ring_lemmas::lemma_trichotomy::<T>(s.mul(val), T::zero());
    } else {
        // val ≡ 0 (from trichotomy: ¬(0 < val) ∧ ¬(val < 0) → 0 ≡ val)
        if T::zero().eqv(val) {
            T::axiom_eqv_symmetric(T::zero(), val);
        }
        // s*val ≡ s*0 ≡ 0
        ring_lemmas::lemma_mul_congruence_right::<T>(s, val, T::zero());
        T::axiom_mul_zero_right(s);
        T::axiom_eqv_transitive(s.mul(val), s.mul(T::zero()), T::zero());
        // s*val ≡ 0, so ¬(0 < s*val) and ¬(s*val < 0)
        ordered_ring_lemmas::lemma_trichotomy::<T>(T::zero(), s.mul(val));
        ordered_ring_lemmas::lemma_trichotomy::<T>(s.mul(val), T::zero());
        T::axiom_eqv_symmetric(s.mul(val), T::zero());
    }
}

/// orient2d_sign is invariant under positive scaling of the determinant.
pub proof fn lemma_orient2d_sign_pos_scale<T: OrderedField>(
    s: T,
    a: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        T::zero().lt(s),
    ensures
        scalar_sign(s.mul(orient2d(a, b, c))) == orient2d_sign(a, b, c),
{
    lemma_scalar_sign_pos_scale::<T>(s, orient2d(a, b, c));
}

/// orient3d_sign is invariant under positive scaling of the determinant.
pub proof fn lemma_orient3d_sign_pos_scale<T: OrderedField>(
    s: T,
    a: Point3<T>, b: Point3<T>, c: Point3<T>, d: Point3<T>,
)
    requires
        T::zero().lt(s),
    ensures
        scalar_sign(s.mul(orient3d(a, b, c, d))) == orient3d_sign(a, b, c, d),
{
    lemma_scalar_sign_pos_scale::<T>(s, orient3d(a, b, c, d));
}

} // verus!
