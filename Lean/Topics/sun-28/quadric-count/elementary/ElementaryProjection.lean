import ElementaryEuler
import ArithmeticProjection

namespace Sun28.ConeCount
open Sun28.Ordinary Sun28.HeightFibres.Sharp Sun28.HeightExtension Sun28.HeightBudget
noncomputable section

open Sun28.ContactFactors

theorem elementary_products (A : Fin 3→ℚ) (one : A 0=1) : UniformProducts A := by
  have base : 64≤threshold A:=le_max_left ..
  have cap : (50:ℝ)≤(threshold A:ℝ) := by exact_mod_cast (show 50≤threshold A by omega)
  exact ConeEuler.Elementary.sieve_primes A base cap (by norm_num)
    (by have h:=enough_shifts A one;omega) (Sun28.GaussianSelection.shifts_card_le A)

theorem upper_sieve (quadric : PublishedQuadricCount) : ConeSieve.CongruenceInputs :=
  congruences quadric elementary_products

/-- The upper collision estimate for the fixed 28-witness polynomial follows
from the published rank-five counting theorem and an elementary sieve product. -/
theorem integer_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : PublishedQuadricCount)
    (height : HeightBudget.Residual) (lower : FinitePattern.LowerInputs)
    (points : PrescribedPoints.CoreResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) :=
  SpecializedProjection.fixed_projection realCurves units pell classes characters height lower
    (upper_sieve quadric) points x

theorem integer_definition (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : PublishedQuadricCount)
    (height : HeightBudget.Residual) (paper : FinitePattern.PaperInputs)
    (points : PrescribedPoints.CoreResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,integer_projection realCurves units pell classes characters quadric height
    (FinitePattern.lower_of_paper paper) points⟩

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.elementary_products
#print axioms Sun28.ConeCount.upper_sieve
#print axioms Sun28.ConeCount.integer_projection
#print axioms Sun28.ConeCount.integer_definition
