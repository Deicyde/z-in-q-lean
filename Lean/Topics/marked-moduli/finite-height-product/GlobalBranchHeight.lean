import FiniteDenominator
import IntrinsicArch
import PoleHeight

/-! Global projective height of the ten branch weights over their own coordinate field. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial NumberField BranchHeight ContactInvariant SexticThetaHeight ThetaQuotient Height
noncomputable section

/-- The height of the intrinsic pivot chart equals that of the sum-normalized chart. -/
theorem sumWeights_height {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    letI := weight_numberField hu hδ hz
    normalizedHeight (sumWeights r) = normalizedHeight (weights r) := by
  let := weight_numberField hu hδ hz
  let s := ∑ j, weights r j
  have hs : s ≠ 0 := (paper_pair hu hδ hr hz).1
  have he : sumWeights r = s⁻¹ • weights r := by
    funext j
    change weights r j / s = s⁻¹ * weights r j
    rw [div_eq_inv_mul]
  unfold normalizedHeight
  rw [he,logHeight_eq_log_mulHeight,logHeight_eq_log_mulHeight,mulHeight_smul_eq_mulHeight _ (inv_ne_zero hs)]

/-- Only the pointwise finite-place estimate remains as an arithmetic input. The curve,
its intrinsic number field, the nonzero sum and all infinite places are handled here. -/
theorem paper_height_of_denominator {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0)
    {D : ℕ} (hD : 0 < D) :
    letI := weight_numberField hu hδ hz
    (∀ (w : FinitePlace (weightField r)) i, w (sumWeights r i) ≤ (w (D:weightField r))⁻¹) →
    normalizedHeight (weights r) < 49 + Real.log D := by
  let := weight_numberField hu hδ hz
  intro hf
  obtain ⟨hs,_⟩ := sumWeights_equations hu hδ hr hz
  have hx : sumWeights r ≠ 0 := by
    intro eq
    rw [eq] at hs
    simp at hs
  have H := height_le_of_arch_finite hx hD hf (by norm_num [archBound] : 0 < archBound)
    (intrinsic_infinite_factor hu hδ hr hz)
  rw [sumWeights_height hu hδ hr hz] at H
  linarith [log_archBound_lt]

private theorem pos_poleNorm (u : ℚ) : 0 < poleNorm u := by
  change 0 < (ResidualFactors.poleForm u.num (u.den:ℤ)).natAbs
  apply Int.natAbs_pos.mpr
  have h := (CurveChart.rational_parameters u).1
  unfold CurveChart.homogeneousG at h
  unfold ResidualFactors.poleForm at h ⊢
  exact_mod_cast h

/-- For the explicit pole denominator the only local assumption is the corresponding
one-coordinate inequality at each finite place. -/
theorem paper_height_of_pole_denominator {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    let D : ℕ := 144*3^4*27^2*(poleNorm u)^6
    letI := weight_numberField hu hδ hz
    (∀ (w : FinitePlace (weightField r)) i, w (sumWeights r i) ≤ (w (D:weightField r))⁻¹) →
    normalizedHeight (weights r) < 49 + Real.log 8503056 + 6*Real.log (poleNorm u) := by
  let := weight_numberField hu hδ hz
  intro D hf
  have hg := pos_poleNorm u
  have hD : 0 < D := by dsimp [D]; positivity
  have H := paper_height_of_denominator hu hδ hr hz hD hf
  have he : (D:ℝ) = 8503056*(poleNorm u:ℝ)^6 := by
    dsimp [D]
    push_cast
    ring
  rw [he,Real.log_mul (by norm_num) (pow_ne_zero _ (by exact_mod_cast hg.ne')),Real.log_pow] at H
  exact lt_of_lt_of_eq H (by norm_num only [Nat.cast_ofNat]; ac_rfl)

/-- The pole-form estimate expresses the preceding uniform bound entirely in the input height. -/
theorem paper_height_of_input_denominator {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ j, aeval (r j) (sextic u δ)=0) :
    let D : ℕ := 144*3^4*27^2*(poleNorm u)^6
    letI := weight_numberField hu hδ hz
    (∀ (w : FinitePlace (weightField r)) i, w (sumWeights r i) ≤ (w (D:weightField r))⁻¹) →
    normalizedHeight (weights r) < 49 + Real.log 8503056 + 6*Real.log 3907 + 12*ZInQ.ratHeight u := by
  let := weight_numberField hu hδ hz
  intro D hf
  have H := paper_height_of_pole_denominator hu hδ hr hz hf
  linarith [pole_form_height u]

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.sumWeights_height
#print axioms ZInQBlueprint.BranchDepth.paper_height_of_denominator
#print axioms ZInQBlueprint.BranchDepth.paper_height_of_pole_denominator
#print axioms ZInQBlueprint.BranchDepth.paper_height_of_input_denominator
