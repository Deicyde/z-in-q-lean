import SquareSupport
import ReducedProjection

namespace Sun28.ReducedEndpoint
open Sun28.Ordinary Sun28.HeightFibres Sun28.HeightFibres.Sharp
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.MediumSieve
noncomputable section

/-- The fixed polynomial has exactly the integer inputs under the residual
square-part height estimate, the logarithmic sieve and the paired-point assertion. -/
theorem fixed_projection_log (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (integral : PublishedPell312)
    (finitePell : PublishedFinitePell) (classes : PublishedClassRegulator)
    (characters : QuadraticCharacterDiscriminants) (height : RepeatedResidual)
    (counts : LogInputs) (points : TwistExtension.Residual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x = (z : ℚ) := by
  have original := (original_iff_repeated units integral finitePell classes characters).mpr height
  exact TwistExtension.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp original)
    (log_positive_surplus counts) points x

/-- The sufficient one-prime estimate yields the same projection of the same polynomial. -/
theorem fixed_projection_prime (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (integral : PublishedPell312)
    (finitePell : PublishedFinitePell) (classes : PublishedClassRegulator)
    (characters : QuadraticCharacterDiscriminants) (height : RepeatedResidual)
    (counts : PrimeInputs) (points : TwistExtension.Residual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w = 0) ↔ ∃ z : ℤ, x = (z : ℚ) :=
  fixed_projection_log realCurves units integral finitePell classes characters height
    (log_of_prime counts) points x

end
end Sun28.ReducedEndpoint
#print axioms Sun28.ReducedEndpoint.fixed_projection_log
#print axioms Sun28.ReducedEndpoint.fixed_projection_prime
