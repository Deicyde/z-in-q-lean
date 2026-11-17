import ArithmeticProjection28
import OrdinateHeight

namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary
noncomputable section

/-- The two-coordinate published Mordell bound yields the smaller height
residual at the same polynomial, prime test and physical-ratio equation. -/
theorem ordinate_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount)
    (mordell : HeightCubics.Ordinate.PublishedCoordinates)
    (height : HeightCubics.Ordinate.Remaining) (primeCount : RayDensity.CorrelationInputs)
    (points : PointLifts.LocalRatioResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  have full := (HeightCubics.Ordinate.original_iff_ordinate units pell classes characters mordell).mpr height
  have old := HeightCubics.Ordinate.supported_abscissa mordell
  exact integer_projection realCurves units pell classes characters quadric old
    ((HeightCubics.original_iff_mixed units pell classes characters old).mp full) primeCount points x

end
end Sun28.ReducedArithmetic
#print axioms Sun28.ReducedArithmetic.ordinate_projection
