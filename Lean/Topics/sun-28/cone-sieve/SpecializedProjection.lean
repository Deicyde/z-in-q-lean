import CongruenceProjection
import BudgetSector
import ZeroOrdinateCore
import PaperPattern

namespace Sun28.SpecializedProjection
open Sun28.Ordinary Sun28.HeightFibres.Sharp Sun28.HeightExtension Sun28.HeightBudget
noncomputable section

/-- One rational variable and the 28 witnesses of the fixed polynomial. The
congruence input concerns weighted lattice points with no primality assumption. -/
theorem fixed_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (height : HeightBudget.Residual) (lower : FinitePattern.LowerInputs)
    (upper : ConeSieve.CongruenceInputs) (points : PrescribedPoints.CoreResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x = (z : ℚ) := by
  have h := (original_iff_budget units pell classes characters).mpr height
  have mass := FinitePattern.positive_surplus lower (FinitePattern.upper_of_prime (ConeSieve.row_of_congruences upper))
  exact TwistExtension.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp h) mass
    (PrescribedPoints.core_iff_residual.mp points) x

/-- The companion's two-sign count at the displayed logarithmic rate suffices for the finite lower input. -/
theorem paper_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (height : HeightBudget.Residual) (paper : FinitePattern.PaperInputs)
    (upper : ConeSieve.CongruenceInputs) (points : PrescribedPoints.CoreResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection realCurves units pell classes characters height
    (FinitePattern.lower_of_paper paper) upper points⟩

end
end Sun28.SpecializedProjection
#print axioms Sun28.SpecializedProjection.fixed_projection
#print axioms Sun28.SpecializedProjection.paper_projection
