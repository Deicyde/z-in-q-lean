import PaperHeight
import ParameterReturn
import PrintedRankEndpoint

/-! Recover the projective branch height from the rational modular invariant. -/
namespace ZInQBlueprint.JacobianHeight
open Polynomial ZInQ BranchHeight ThetaQuotient SexticThetaHeight
noncomputable section

private theorem six_log_14400 : 6 * Real.log 14400 < 60 := by
  have h : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h10 : (14400 : ℝ) < Real.exp 10 := calc
    _ < (2.7 : ℝ)^10 := by norm_num
    _ < (Real.exp 1)^10 := pow_lt_pow_left₀ h (by norm_num) (by decide)
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  linarith only [(Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 14400)).mpr h10]

/-- Height comparison in both directions on the same fibre, for every ordering and twist. -/
theorem branch_and_modular_height {u δ : ℚ} (hu : u ∉ contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0) :
    letI := weight_numberField hu hδ hz
    normalizedHeight (weights r) < ratHeight (SixContact.J u) + 175 ∧
      ratHeight (SixContact.J u) ≤ 5 * normalizedHeight (weights r) + Real.log 3779136 := by
  let := weight_numberField hu hδ hz
  have h0 : u ≠ 0 := fun h => hu (h ▸ (by decide : (0 : ℚ) ∈ contactSet))
  have hp := PoleNorm.sharp_parameter_height u h0
  change 12 * ratHeight u ≤ ratHeight (SixContact.J u) + 6 * Real.log 14400 at hp
  exact ⟨by linarith only [BranchDepth.paper_branch_height_input hu hδ hr hz, hp, six_log_14400],
    paper_J_height hu hδ hr hz⟩

/-- An upper bound on the rational invariant suffices for the intrinsic six-contact estimate. -/
theorem canonical_of_modular_height
    (hJ : ∀ u : ℚ, u ∉ contactSet → ratHeight (SixContact.J u) ≤ 30 * HeightBudget.vonKaenelBudget u + 150) :
    CanonicalBranchBound := by
  intro u hu
  obtain ⟨r,hr,hz⟩ := ThetaPeriod.six_roots hu (one_ne_zero : (1 : ℚ) ≠ 0)
  refine ⟨r,hr,hz,?_⟩
  let := weight_numberField hu one_ne_zero hz
  have hh := (branch_and_modular_height hu one_ne_zero hr hz).1
  have hb := le_max_right (1 : ℝ) (HeightBudget.vonKaenelBudget u)
  have hm := le_max_left (1 : ℝ) (HeightBudget.vonKaenelBudget u)
  linarith only [hh, hJ u hu, hb, hm]

/-- The constant in this implication allows the genus-two discriminant comparison and
von Känel's theorem to be applied with the same stable height. -/
theorem original_of_modular_height
    (hJ : ∀ u : ℚ, u ∉ contactSet → ratHeight (SixContact.J u) ≤ 30 * HeightBudget.vonKaenelBudget u + 150)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := OriginalRank.frozen_from_height_and_printed_rank (canonical_of_modular_height hJ) genus rank

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.branch_and_modular_height
#print axioms ZInQBlueprint.JacobianHeight.canonical_of_modular_height
#print axioms ZInQBlueprint.JacobianHeight.original_of_modular_height
