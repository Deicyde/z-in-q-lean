import TwoCurves
import TransferRows
import SwappedQuartic

namespace Sun28.WitnessHeight
open Sun28.PrimeTransfer Sun28.Ordinary
noncomputable section

theorem fibre_of_transfer (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (grid : PublishedRecurrence)
    (models : FixedClassModelInputs) (upper : RelativeUpperInputs)
    (points : GlobalDescent.TransposedResidual) (k : ℤ) :
    ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial (k:ℚ) w=0 :=
  fibre_of_hybrid realCurves quadric (hybrid_inputs_of_transfer grid models upper)
    (GlobalDescent.sections_iff_transposed_residual.mpr points) k

/-- A finite polynomial recurrence, the narrow-row transfer, the one-prime upper
moments and the prescribed-point construction are used only to build integer fibres. -/
theorem transfer_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (grid : PublishedRecurrence)
    (height : TwoLocusHeight) (models : FixedClassModelInputs) (upper : RelativeUpperInputs)
    (points : GlobalDescent.TransposedResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  refine ⟨integral_of_two_loci height x,?_⟩
  rintro ⟨k,rfl⟩
  exact fibre_of_transfer realCurves quadric grid models upper points k

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.fibre_of_transfer
#print axioms Sun28.WitnessHeight.transfer_projection
