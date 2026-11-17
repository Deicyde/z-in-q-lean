import ScalarBranches
import RemainingSections

namespace ZInQBlueprint.FiveMetric
noncomputable section
set_option maxRecDepth 12000
open Sun28.ScalarRankZero
/-- Independent arithmetic route to the same polynomial, with the two elliptic alternatives removed. -/
theorem polynomial_of_reduced_loci (realCurves : Sun28.RealComponents.PublishedProposition72)
    (quadric : Sun28.ConeCount.PublishedQuadricCount) (units : Sun28.FiveMarkUnits.PublishedCorollary72)
    (pell : Sun28.HeightBudget.PublishedAllPell) (classes : Sun28.HeightExtension.PublishedClassRegulator)
    (disc : Sun28.HeightFibres.Sharp.QuadraticCharacterDiscriminants)
    (descent : TwoIsogenyRank) (reduction : OddGoodReduction) (reduced : ReducedExceptionalScalarBound)
    (ordinary : Sun28.ScalarDepth.OrdinaryBound) (moments : Sun28.PrimeValues.FirstMomentInputs)
    (points : RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Sun28.Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  Sun28.ScalarDepth.fixed_projection realCurves quadric units pell classes disc
    (scalar_of_reduced_exceptions descent reduction reduced) ordinary moments
    (remaining_sections_iff.mp points) x

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.polynomial_of_reduced_loci
