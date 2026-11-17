import DensityApplication
import SpecializedProjection

namespace Sun28.ConeCount
open Sun28.Ordinary Sun28.HeightFibres.Sharp Sun28.HeightExtension Sun28.HeightBudget
noncomputable section

/-- The ordinary upper congruence estimates for this polynomial follow from
the published quadric count and Mertens' theorem in progressions mod four. -/
theorem fixed_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : PublishedQuadricCount) (mertens : ConeEuler.PublishedMertensFour)
    (height : HeightBudget.Residual) (lower : FinitePattern.LowerInputs)
    (points : PrescribedPoints.CoreResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) :=
  SpecializedProjection.fixed_projection realCurves units pell classes characters height lower
    (congruences_from_mertens quadric mertens) points x

theorem paper_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : PublishedQuadricCount) (mertens : ConeEuler.PublishedMertensFour)
    (height : HeightBudget.Residual) (paper : FinitePattern.PaperInputs)
    (points : PrescribedPoints.CoreResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection realCurves units pell classes characters quadric mertens height
    (FinitePattern.lower_of_paper paper) points⟩

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.fixed_projection
#print axioms Sun28.ConeCount.paper_projection
