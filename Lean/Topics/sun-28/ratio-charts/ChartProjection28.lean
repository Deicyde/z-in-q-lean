import AdmissibleTwists
import SelmerResidual
import PooledEndpoint

namespace Sun28.ReducedArithmetic
open Sun28.HeightExtension Sun28.HeightBudget Sun28.HeightFibres.Sharp Sun28.Ordinary

/-- The two conic equations are needed only on their regular locus. -/
theorem chart_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (elliptic : HeightCubics.Refinement.PublishedElliptic)
    (height : HeightCubics.Pooled.Remaining) (primeCount : RayDensity.CorrelationInputs)
    (points : PointLifts.RegularResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) :=
  conductor_projection realCurves units pell classes characters quadric elliptic
    ((HeightCubics.Pooled.refinement_iff_pooled elliptic).mpr height) primeCount
    (PointLifts.residual_iff_positive.mp (PointLifts.residual_iff_regular.mpr points)) x

/-- A stronger sufficient rational-point hypothesis among prime twists for which
the two homogeneous spaces are known to have primitive points at every place. -/
theorem prime_cover_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (elliptic : HeightCubics.Refinement.PublishedElliptic)
    (height : HeightCubics.Pooled.Remaining) (primeCount : RayDensity.CorrelationInputs)
    (points : LocalQuartics.PrimeCoverResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) :=
  chart_projection realCurves units pell classes characters quadric elliptic height primeCount
    (LocalQuartics.regular_of_prime_covers points) x

end Sun28.ReducedArithmetic
#print axioms Sun28.ReducedArithmetic.chart_projection
#print axioms Sun28.ReducedArithmetic.prime_cover_projection
