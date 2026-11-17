import CMProjection
import BonferroniRows
import RemainingSections

namespace ZInQBlueprint.CMPeriods
open Sun28 Sun28.Concrete Sun28.MultiplierChoice Sun28.PrimeModel ZInQBlueprint.FiveMetric
open ZInQBlueprint.DiamondHeight
noncomputable section
set_option maxRecDepth 12000
set_option exponentiation.threshold 250
/-- The aggregate sieve loss is measured on the same rows that supply the
ordinary parameters. The simultaneous-point hypothesis supplies their global lifts. -/
theorem integer_fibre_of_aggregate (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (loss : CofinalBonferroni)
    (points : RemainingSections) (k : ℤ) :
    ∃ w : Fin 28 → ℚ, eval28 oneSignPolynomial (k:ℚ) w=0 := by
  exact (compiled_one_sign _).mpr (WitnessHeight.fibre_of_hybrid realCurves quadric
    (hybrid_of_bonferroni loss) (GlobalDescent.sections_iff_descent.mpr (remaining_sections_iff.mp points)) k)

/-- A separated endpoint for the original arithmetic route to the one-sign polynomial. -/
theorem one_sign_of_aggregate (table : SmallClassDiscriminants)
    (fibres : MarkedFibres (210^300) 128) (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (loss : CofinalBonferroni)
    (points : RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 oneSignPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro root
    exact WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
      (original_height_of_quotients (marked_quotients table fibres))) x ((compiled_one_sign x).mp root)
  · rintro ⟨k,rfl⟩
    exact integer_fibre_of_aggregate realCurves quadric loss points k
end
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.integer_fibre_of_aggregate
#print axioms ZInQBlueprint.CMPeriods.one_sign_of_aggregate
