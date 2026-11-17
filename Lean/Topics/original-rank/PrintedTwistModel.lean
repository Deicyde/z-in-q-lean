import PrintedTwists

namespace ZInQBlueprint.OriginalRank

open ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b

/-- The homogeneous isomorphism between Tian–Yuan–Zhang's cubic and
the short cubic used by the Lean L-function. The identity is over any
field, including residue fields where the twist parameter is a unit. -/
theorem twist_cubic_identity {K : Type*} [Field K] (d x y z : K) :
    (d ^ 2 * y) ^ 2 * z - ((d * x) ^ 3 - d ^ 2 * (d * x) * z ^ 2) =
      d ^ 3 * (d * y ^ 2 * z - (x ^ 3 - x * z ^ 2)) := by ring

/-- The diagonal map and its inverse preserve the homogeneous equations
without dividing by any of the three projective coordinates. -/
theorem twist_cubics_iff {K : Type*} [Field K] {d : K} (hd : d ≠ 0) (x y z : K) :
    d * y ^ 2 * z = x ^ 3 - x * z ^ 2 ↔
      (d ^ 2 * y) ^ 2 * z = (d * x) ^ 3 - d ^ 2 * (d * x) * z ^ 2 := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [twist_cubic_identity, sub_eq_zero.mpr h, mul_zero]
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [twist_cubic_identity] at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 hd))

/-- The inverse coordinate change exists on every chart for nonzero twist. -/
theorem twist_coordinates_inverse {K : Type*} [Field K] {d : K} (hd : d ≠ 0) (x y z : K) :
    ((d * x) / d, (d ^ 2 * y) / d ^ 2, z) = (x, y, z) ∧
    (d * (x / d), d ^ 2 * (y / d ^ 2), z) = (x, y, z) := by
  simp [hd, mul_div_cancel₀, mul_div_cancel_left₀]

/-- Once the analytic order exceeds one, the paper defines its normalized
invariant to be zero (p. 722). The second coefficient in the proof of
Theorem 3.5(2) on p. 760 is then even. -/
def HigherOrderGenusCoefficient : Prop :=
  ∀ (d : ℕ) (hd : d % 8 = 5), Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → 2 ≤ analyticOrderAt F 1 →
      Even (TYZ.printedCoefficient d hd)

theorem higher_order_iff_printed_derivative :
    HigherOrderGenusCoefficient ↔ SelectedTwists.PrintedBracketDerivative := by
  constructor
  · intro h d hd hs F hF hv
    exact h d hd hs F hF ((SelectedTwists.higherOrder_iff_derivative_zero hd hs hF).2 hv)
  · intro h d hd hs F hF hv
    exact h d hd hs F hF ((SelectedTwists.higherOrder_iff_derivative_zero hd hs hF).1 hv)

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.twist_cubic_identity
#print axioms ZInQBlueprint.OriginalRank.twist_cubics_iff
#print axioms ZInQBlueprint.OriginalRank.twist_coordinates_inverse
#print axioms ZInQBlueprint.OriginalRank.higher_order_iff_printed_derivative
