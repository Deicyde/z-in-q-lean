import AnalyticInputs
import HusemollerClassification
import GenusTwoHeight

namespace Sun28.SieveProjection
open Sun28.Ordinary

theorem least_iff_sextic (units : FiveMarkUnits.PublishedCorollary72) :
    MinimalConductors.ExactLeastHeight ↔ FiveDescent.TwistHeight glazerConstant24 :=
  (MinimalConductors.original_iff_exact_least units).symm.trans FiveDescent.glazer_iff_twist

theorem fixed_projection (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (twists : PairedClasses.Residual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  RealProjection.fixed_projection (RealComponents.openComponent_of_published classification)
    units ((least_iff_sextic units).mpr height) (WeightedSelection.prime_values_iff_surplus.mpr sieve) twists x

theorem integer_definition_28 (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (twists : PairedClasses.Residual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection classification units height sieve twists⟩

theorem of_count_estimates (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (counts : WeightedSelection.AnalyticCounts) (twists : PairedClasses.Residual) : IntegerDefinition28 :=
  integer_definition_28 classification units height
    (WeightedSelection.prime_values_iff_surplus.mp (WeightedSelection.prime_values_of_counts counts)) twists

end Sun28.SieveProjection
#print axioms Sun28.SieveProjection.least_iff_sextic
#print axioms Sun28.SieveProjection.fixed_projection
#print axioms Sun28.SieveProjection.integer_definition_28
#print axioms Sun28.SieveProjection.of_count_estimates
