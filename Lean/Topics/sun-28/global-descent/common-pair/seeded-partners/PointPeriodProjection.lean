import RationalPartnerProjection
import GeneratorRows

namespace Sun28.SeededPartners
open Sun28 Sun28.QualitativeRows Sun28.MultiplierChoice Sun28.Concrete Sun28.RealCharts
open Sun28.CyclicOrbit Sun28.RealProjection Sun28.GlobalDescent ZInQ
open ZInQBlueprint.FiveMetric ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods
open ZInQBlueprint.IntegralSections
noncomputable section
set_option maxRecDepth 14000
set_option exponentiation.threshold 250

private theorem section_rule (lift : CompanionLift) : ChoiceResidual :=
  choice_of_sections (sections_iff_descent.mpr (remaining_sections_iff.mp (sections_of_companion lift)))

theorem integer_of_point_periods {k : ℤ} (w : Window k) (row : PointRow w) (lift : CompanionLift) :
    ∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial (k:ℚ) v=0 :=
  (compiled_one_sign _).mpr (integer_fibre (section_rule lift) (selected_of_point w row))

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

/-- The real window is fixed before the existence question for the integer prime tuple. -/
def integerWindow (realCurves : RealComponents.PublishedProposition72) (k : ℤ) : Window k :=
  let component := RealComponents.openComponent_of_published realCurves
  let orbit := of_open_component diagonalGenerator component
  fixedWindow orbit (parameterModel_on_subgroup DiagonalClosure orbit (generator_value diagonalGenerator component)) k

/-- A window at each integer suffices. One may always use the window supplied by the real classification. -/
theorem one_sign_of_point_periods (table : SmallClassDiscriminants)
    (fibres : ActualPencilFibres (210^300)) (rows : ∀ k : ℤ, ∃ w : Window k, PointRow w)
    (lift : CompanionLift) (x : ℚ) :
    (∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro root
    have marked : MarkedFibres (210^300) 128 :=
      marked_fibres_of_pencil (by norm_num) (pencil_fibres_of_evaluations fibres)
    exact WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
      (original_height_of_quotients (marked_quotients table marked))) x ((compiled_one_sign x).mp root)
  · rintro ⟨k,rfl⟩
    obtain ⟨w,row⟩ := rows k
    exact integer_of_point_periods w row lift

theorem one_sign_of_fixed_windows (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72)
    (rows : ∀ k, PointRow (integerWindow realCurves k)) (lift : CompanionLift) (x : ℚ) :
    (∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  one_sign_of_point_periods table fibres (fun k => ⟨integerWindow realCurves k,rows k⟩) lift x

end
end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.integer_of_point_periods
#print axioms Sun28.SeededPartners.integerWindow
#print axioms Sun28.SeededPartners.one_sign_of_point_periods
#print axioms Sun28.SeededPartners.one_sign_of_fixed_windows
