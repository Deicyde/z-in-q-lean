import QuadraticFactors
import ThreeQuadraticFields

/-! Degree eight for the number field used in the paper's branch-height estimate. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial SexticThetaHeight SexticIgusaChart ThetaPeriod
noncomputable section

theorem paper_weightField_le_eight {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hz : ∀ i, aeval (r i) (sextic u δ) = 0) :
    Module.finrank ℚ (weightField r) ≤ 8 := by
  apply weightField_degree_three_quadratics (firstFactor u) (secondFactor u) (thirdFactor u) (unmarked hu hδ).2.1
  · exact (quad_degree _ _).2.le
  · exact (quad_degree _ _).2.le
  · exact (quad_degree _ _).2.le
  · intro i
    simpa only [three_quadratics hu δ, mul_assoc] using hz i
  · exact (quad_degree _ _).1.ne_zero
  · exact (quad_degree _ _).1.ne_zero
  · exact (quad_degree _ _).1.ne_zero

/-- The same explicit number field realizes both the degree bound and the Weil-height inequality. -/
theorem degree_eight_height {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0) :
    letI := weight_numberField hu hδ hz
    Module.finrank ℚ (weightField r) ≤ 8 ∧
      ZInQ.ratHeight (SixContact.J u) ≤ 5 * ThetaQuotient.normalizedHeight (weights r) + Real.log 3779136 :=
  ⟨paper_weightField_le_eight hu hδ hz,paper_J_height hu hδ hr hz⟩

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.paper_weightField_le_eight
#print axioms ZInQBlueprint.BranchHeight.degree_eight_height
