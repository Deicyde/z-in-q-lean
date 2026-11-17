import IntegralPencilEndpoint
import SharedSelection
import RemainingSections

namespace ZInQBlueprint.Diagonal210
open Sun28 Sun28.Concrete Sun28.MultiplierChoice ZInQBlueprint.FiveMetric
open ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods ZInQBlueprint.IntegralSections
noncomputable section
set_option maxRecDepth 12000
set_option exponentiation.threshold 250

/-- Integer inputs only require the common Gaussian row estimate, the stated
real and quadric results, and the simultaneous rational-point argument. -/
theorem integer_zero (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (rows : CommonRows.PairCorrectedInputs)
    (points : RemainingSections) (k : ℤ) :
    ∃ w : Fin 28 → ℚ,eval28 oneSignPolynomial (k:ℚ) w=0 := by
  have surplus := CommonRows.positive_surplus rows
    (ConeSieve.row_of_congruences (ConeCount.upper_sieve quadric))
  have sections := GlobalDescent.sections_iff_descent.mpr (remaining_sections_iff.mp points)
  exact (compiled_one_sign _).mpr (integer_root realCurves surplus (choice_of_sections sections) k)

/-- The sources of the forward and reverse implications are independent. The
geometric hypothesis concerns evaluations on an actual modular surface fibre. -/
theorem one_sign (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72) (quadric : ConeCount.PublishedQuadricCount)
    (rows : CommonRows.PairCorrectedInputs) (points : RemainingSections) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 oneSignPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro root
    have marked : MarkedFibres (210^300) 128 :=
      marked_fibres_of_pencil (by norm_num) (pencil_fibres_of_evaluations fibres)
    exact WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
      (original_height_of_quotients (marked_quotients table marked))) x ((compiled_one_sign x).mp root)
  · rintro ⟨k,rfl⟩
    exact integer_zero realCurves quadric rows points k

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.integer_zero
#print axioms ZInQBlueprint.Diagonal210.one_sign
