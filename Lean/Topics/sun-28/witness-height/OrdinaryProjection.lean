import TransferProjection
import InteriorTransfer

namespace Sun28.WitnessHeight
open Sun28.PrimeTransfer Sun28.Ordinary
noncomputable section

/-- The single-prime ideal class enters only through its one-variable density.
The simultaneous lower estimate now uses an ordinary-prime dominated weight. -/
theorem ordinary_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (grid : PublishedRecurrence)
    (height : TwoLocusHeight) (density : OnePrimeDensity) (model : InteriorModel)
    (upper : RelativeUpperInputs) (points : GlobalDescent.TransposedResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  apply transfer_projection realCurves quadric grid height _ upper points x
  exact class_model_of_ordinary density (model_geometry model)

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.ordinary_projection
