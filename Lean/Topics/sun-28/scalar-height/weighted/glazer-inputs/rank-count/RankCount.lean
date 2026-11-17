import RankWeights
import TwistPoints
import SignedOrbitBudget

/-! The published fixed-curve count and full two-descent imply the polylogarithmic bound. -/
namespace ZInQBlueprint.RankCount
open Finset Sun28.FiveDescent ZInQBlueprint.TwistCount ZInQBlueprint.OriginalHeightCount
noncomputable section

theorem prime_cost (d e : ℤ) :
    primeCost d e=7^(∑ p∈parameterPrimes d e,localCost d e p) := by
  rw [primeCost,←prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro p hp
  obtain h|h:=mem_union.mp hp
  · by_cases he:p∈e.natAbs.primeFactors <;> simp [position,choiceWeight,localCost,h,he]
  · by_cases hd:p∈d.natAbs.primeFactors <;> simp [position,choiceWeight,localCost,h,hd]

theorem sextic_point_count {γ : ℝ} (positive : 0≤γ) (silverman : FixedCurveCount γ)
    (descent : DescentRankBounds) : PointCount (γ*7^16) := by
  intro d e sd se Y points
  have bound:=(silverman d e sd se Y points).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤7) (total_rank descent sd se)) positive)
  rw [pow_add] at bound
  rw [prime_cost,Nat.cast_pow,Nat.cast_ofNat]
  simpa only [mul_assoc] using bound

theorem count_from_ranks {γ : ℝ} (positive : 0≤γ) (silverman : FixedCurveCount γ)
    (descent : DescentRankBounds) {X K : ℕ} (window : Real.log (X:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    ((exceptions X).card:ℝ) ≤ 4*(γ*7^16)*(K:ℝ)*(1+Real.log (K:ℝ))^2498 :=
  ZInQBlueprint.TwistCount.exceptional_count (mul_nonneg positive (by positivity))
    (sextic_point_count positive silverman descent) window

/-- All four signs lift, so their multiplicity cancels the four choices of twist signs. -/
theorem count_from_four_lifts {γ : ℝ} (positive : 0≤γ) (silverman : FixedCurveCount γ)
    (descent : DescentRankBounds) {X K : ℕ} (window : Real.log (X:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    ((exceptions X).card:ℝ) ≤ (γ*7^16)*(K:ℝ)*(1+Real.log (K:ℝ))^2498 :=
  ZInQBlueprint.TwistCount.four_lift_count (mul_nonneg positive (by positivity))
    (sextic_point_count positive silverman descent) window

end
end ZInQBlueprint.RankCount
#print axioms ZInQBlueprint.RankCount.prime_cost
#print axioms ZInQBlueprint.RankCount.sextic_point_count
#print axioms ZInQBlueprint.RankCount.count_from_ranks
#print axioms ZInQBlueprint.RankCount.count_from_four_lifts
