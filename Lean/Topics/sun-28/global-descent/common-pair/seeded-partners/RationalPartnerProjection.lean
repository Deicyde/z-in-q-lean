import PartnerProjection
import RationalRowSelection

namespace Sun28.SeededPartners
open Sun28 Sun28.QualitativeRows Sun28.MultiplierChoice Sun28.Concrete Sun28.RealCharts
open Sun28.CyclicOrbit Sun28.RealProjection Sun28.GlobalDescent ZInQ
open ZInQBlueprint.FiveMetric ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods
open ZInQBlueprint.IntegralSections
noncomputable section
set_option maxRecDepth 14000
set_option exponentiation.threshold 250

/-- The integer fibre only needs one finite arithmetic row and a lift of one companion. -/
theorem integer_of_rational_row {k : ℤ} (w : Window k) (row : RationalRow w) (lift : CompanionLift) :
    ∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial (k:ℚ) v=0 := by
  have sections := sections_iff_descent.mpr (remaining_sections_iff.mp (sections_of_companion lift))
  exact (compiled_one_sign _).mpr (integer_fibre (choice_of_sections sections) (selected_of_rational w row))

/-- All three project-specific obligations appear with their actual quantifiers. -/
theorem one_sign_of_rational_rows (table : SmallClassDiscriminants)
    (fibres : ActualPencilFibres (210^300))
    (rows : ∀ k : ℤ, ∃ w : Window k, RationalRow w) (lift : CompanionLift) (x : ℚ) :
    (∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro root
    have marked : MarkedFibres (210^300) 128 :=
      marked_fibres_of_pencil (by norm_num) (pencil_fibres_of_evaluations fibres)
    exact WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
      (original_height_of_quotients (marked_quotients table marked))) x ((compiled_one_sign x).mp root)
  · rintro ⟨k,rfl⟩
    obtain ⟨w,row⟩ := rows k
    exact integer_of_rational_row w row lift

end
end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.integer_of_rational_row
#print axioms Sun28.SeededPartners.one_sign_of_rational_rows
