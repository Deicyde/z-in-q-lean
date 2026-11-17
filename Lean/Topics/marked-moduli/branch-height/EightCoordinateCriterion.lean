import EightBranchHeight
import QuadraticDiscriminants
import CanonicalBranch

namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod SexticThetaHeight
noncomputable section
attribute [local instance] Classical.decEq

/-- Roots of the three displayed quadratics give the intrinsic coordinates in degree at most eight. -/
theorem canonical_bound_iff_degree_eight : CanonicalBranchBound ↔
    ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), ∃ r : Fin 6 → ℂ, Function.Injective r ∧
      ∃ hz : ∀ i, aeval (r i) (sextic u 1) = 0,
        letI := weight_numberField hu one_ne_zero hz
        Module.finrank ℚ (weightField r) ≤ 8 ∧
        ThetaQuotient.normalizedHeight (weights r) ≤ 2^26 * max 1 (HeightBudget.vonKaenelBudget u) := by
  constructor
  · intro h u hu
    obtain ⟨r,hr,hz,hb⟩ := h u hu
    exact ⟨r,hr,hz,paper_weightField_le_eight hu one_ne_zero hz,hb⟩
  · intro h u hu
    obtain ⟨r,hr,hz,_,hb⟩ := h u hu
    exact ⟨r,hr,hz,hb⟩

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.canonical_bound_iff_degree_eight
