import PreparedProjection
import FivePencils
import SeparateEstimates

namespace Sun28.SinglePrime
open Sun28.Ordinary Sun28.HeightFibres

/-- The two arguments to the count theorem are independent analytic estimates.
The remaining height and twist obligations are restricted to the range actually used. -/
theorem restricted_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72)
    (pell : PublishedPell312) (regulator : RegulatorBound) (discriminant : BiquadraticDiscriminants)
    (height : AllFiveLarge) (estimates : SeparateInputs) (twists : TwistRank.LocalResidual) (x : ℚ) :
    (∃ w : Fin 28→ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) := by
  have original := (original_iff_all_five_large units pell regulator discriminant).mpr height
  exact TwistRank.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp original)
    (WeightedSelection.prime_values_iff_surplus.mp (prime_values (single_prime_inputs estimates))) twists x

theorem integer_definition_28 (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72)
    (pell : PublishedPell312) (regulator : RegulatorBound) (discriminant : BiquadraticDiscriminants)
    (height : AllFiveLarge) (estimates : SeparateInputs) (twists : TwistRank.LocalResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,restricted_projection realCurves units pell regulator discriminant height estimates twists⟩

end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.restricted_projection
#print axioms Sun28.SinglePrime.integer_definition_28
