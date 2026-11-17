import Mathlib.NumberTheory.Height.NumberField
import ThetaQuotient

/-! A common denominator at every finite place bounds the finite part of a projective height. -/
namespace ZInQBlueprint.BranchDepth
open NumberField Height
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [Nonempty ι]

/-- For a positive rational integer the finite denominator product is the integer to
the power of the absolute degree of the field. -/
theorem finite_denominator_product (K : Type*) [Field K] [NumberField K] {D : ℕ} (hD : 0 < D) :
    (∏ᶠ w : FinitePlace K, (w (D:K))⁻¹) = (D:ℝ) ^ Module.finrank ℚ K := by
  have h := prod_abs_eq_one (K := K) (show (D:K) ≠ 0 by exact_mod_cast hD.ne')
  simp only [InfinitePlace.map_natCast, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq] at h
  rw [finprod_inv_distrib]
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- Allows zero coordinates. Finite support follows by restricting the supremum to
the nonzero coordinates before taking the union of their finite supports. -/
theorem finite_part_le {x : ι → K} (hx : x ≠ 0) {D : ℕ} (hD : 0 < D)
    (h : ∀ (w : FinitePlace K) i, w (x i) ≤ (w (D:K))⁻¹) :
    (∏ᶠ w : FinitePlace K, ⨆ i, w (x i)) ≤ (D:ℝ) ^ Module.finrank ℚ K := by
  rw [← finite_denominator_product K hD]
  have hs : (fun w : FinitePlace K => ⨆ i, w (x i)).HasFiniteMulSupport := by
    change (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) => ⨆ i, v.val (x i)).HasFiniteMulSupport
    fun_prop (disch := assumption)
  have ht := FinitePlace.hasFiniteMulSupport (K := K) (show (D:K) ≠ 0 by exact_mod_cast hD.ne')
  apply finprod_le_finprod₀ hs (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _) ht.inv
  intro v
  exact ciSup_le (h v)

/-- The denominator contributes at most log D to the absolute logarithmic height. -/
theorem height_le_of_arch_finite {x : ι → K} (hx : x ≠ 0) {D : ℕ} (hD : 0 < D)
    (h : ∀ (w : FinitePlace K) i, w (x i) ≤ (w (D:K))⁻¹) {B : ℝ} (hB : 0 < B)
    (harch : (∏ w : InfinitePlace K, (⨆ i, w (x i))^w.mult) ≤ B ^ Module.finrank ℚ K) :
    ThetaQuotient.normalizedHeight x ≤ Real.log B + Real.log D := by
  let d := Module.finrank ℚ K
  have hf := finite_part_le hx hD h
  have hfp : 0 ≤ ∏ᶠ w : FinitePlace K, ⨆ i, w (x i) :=
    finprod_nonneg (fun w => Real.iSup_nonneg_of_nonnegHomClass w.val _)
  have hm : mulHeight x ≤ (B*(D:ℝ))^d := by
    rw [NumberField.mulHeight_eq hx,mul_pow]
    exact mul_le_mul harch hf hfp (pow_nonneg hB.le _)
  have hl := Real.log_le_log (mulHeight_pos x) hm
  rw [Real.log_pow, Real.log_mul hB.ne' (by exact_mod_cast hD.ne')] at hl
  unfold ThetaQuotient.normalizedHeight
  rw [logHeight_eq_log_mulHeight]
  apply (div_le_iff₀ (by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K))).mpr
  simpa only [d,mul_comm] using hl

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.finite_denominator_product
#print axioms ZInQBlueprint.BranchDepth.finite_part_le
#print axioms ZInQBlueprint.BranchDepth.height_le_of_arch_finite
