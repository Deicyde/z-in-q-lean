import FrobeniusCount
import PairedUnits
import RatioResidual

namespace Sun28.CutoffCount
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary
noncomputable section

/-- A one-cutoff unweighted rational-prime estimate, the remaining five-mark
height, and the simultaneous-point problem suffice for the fixed polynomial. -/
theorem integer_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (height : HeightBalance.Remaining)
    (lower : TraceInputs) (points : PointFibres.PencilResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x = (z:ℚ) := by
  have h := (HeightBalance.original_iff_pairs units pell classes characters).mpr height
  have s := count_surplus (of_trace lower) (ConeSieve.row_of_congruences (ConeCount.upper_sieve quadric))
  exact TwistExtension.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp h) s
    (PrescribedPoints.core_iff_residual.mp (PointDescent.core_of_norm_residual (PointFibres.norm_residual_iff_pencil.mpr points))) x

end
end Sun28.CutoffCount
#print axioms Sun28.CutoffCount.integer_projection
