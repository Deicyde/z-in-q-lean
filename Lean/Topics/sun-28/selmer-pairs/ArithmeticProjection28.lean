import RayCorrelation
import MixedSector
import LocalRatioResidual
import TraceProjection

namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary
noncomputable section

/-- The single-cutoff integer-pair count may also be used directly. -/
theorem trace_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount)
    (mordell : ZInQBlueprint.TwistDescent.SupportedMordell74)
    (height : HeightCubics.MixedRemaining) (lower : CutoffCount.TraceInputs)
    (points : PointLifts.LocalRatioResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  have h := (HeightCubics.original_iff_mixed units pell classes characters mordell).mpr height
  exact CutoffCount.integer_projection realCurves units pell classes characters quadric
    ((HeightBalance.original_iff_pairs units pell classes characters).mp h) lower
    (PointLifts.pencil_residual_iff_local_ratios.mpr points) x

/-- The finite Gaussian fibre estimates, the unequal powers in the Mordell
equation, and the local restrictions on the physical ratio enter at the
three arithmetic inputs of the same explicitly constructed polynomial. -/
theorem integer_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount)
    (mordell : ZInQBlueprint.TwistDescent.SupportedMordell74)
    (height : HeightCubics.MixedRemaining) (primeCount : RayDensity.CorrelationInputs)
    (points : PointLifts.LocalRatioResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  have h := (HeightCubics.original_iff_mixed units pell classes characters mordell).mpr height
  have low := FinitePattern.lower_of_paper (RayDensity.paper_of_correlation primeCount)
  have sel := PointLifts.pencil_residual_iff_local_ratios.mpr points
  exact ConeCount.integer_projection realCurves units pell classes characters quadric
    ((HeightBudget.original_iff_budget units pell classes characters).mp h) low
    (PointDescent.core_of_norm_residual (PointFibres.norm_residual_iff_pencil.mpr sel)) x

end
end Sun28.ReducedArithmetic
#print axioms Sun28.ReducedArithmetic.trace_projection
#print axioms Sun28.ReducedArithmetic.integer_projection
