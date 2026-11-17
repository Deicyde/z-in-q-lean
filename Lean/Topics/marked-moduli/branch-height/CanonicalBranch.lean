import BranchTrace

namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod SexticThetaHeight
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- An arithmetic sufficient condition with coefficients in the intrinsic ratio field.
This version involves neither a period chart nor an auxiliary number-field witness. -/
def CanonicalBranchBound : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), ∃ r : Fin 6 → ℂ, Function.Injective r ∧
    ∃ hz : ∀ i, aeval (r i) (sextic u 1) = 0,
      letI := weight_numberField hu one_ne_zero hz
      ThetaQuotient.normalizedHeight (weights r) ≤ 2^26 * max 1 (HeightBudget.vonKaenelBudget u)

theorem untwisted_of_canonical (h : CanonicalBranchBound) : UntwistedBranchHeight := by
  intro u hu
  obtain ⟨r,hr,hz,hb⟩ := h u hu
  let := weight_numberField hu one_ne_zero hz
  exact ⟨r,hr,hz,weightField r,inferInstance,inferInstance,(weightField r).val.toRingHom,weights r,
    fun _ => rfl,hb⟩

theorem frozen_of_canonical_height_and_odd_rows
    (height : CanonicalBranchBound) (D : RecursionData) (base : D.L 1 = 1)
    (periods : ClassThreePeriods D.L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 → OddRowTraces D n) :
    ZInQ.FrozenTarget :=
  frozen_of_untwisted_height_and_odd_rows (untwisted_of_canonical height) D base periods rows

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.untwisted_of_canonical
#print axioms ZInQBlueprint.BranchHeight.frozen_of_canonical_height_and_odd_rows
