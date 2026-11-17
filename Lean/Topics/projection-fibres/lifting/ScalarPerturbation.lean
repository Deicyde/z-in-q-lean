import Std

namespace ProjectionFibres.Lifting

/-- The order of the unrestricted correction when the frozen centre is a unit. -/
theorem unrestricted_correction_order (η j : Int) (odd : ∃ k, η = 2*k+1) :
    η < 2 * (η + j - min 0 (η + 2*j)) := by
  obtain ⟨k, hk⟩ := odd
  by_cases h : η + 2*j ≤ 0
  · rw [Int.min_eq_right h]
    omega
  · rw [Int.min_eq_left (show (0 : Int) ≤ η + 2*j by omega)]
    omega

/-- At a ramified prime, integrality of the trace makes the correction deep. -/
theorem integral_correction_order (η j : Int) (positive : 0 < η)
    (integral : 0 ≤ j) : η < 2 * (η+j) := by
  omega

/-- The two raw inequalities used at the archived and bounded physical indices. -/
theorem physical_trace_order (e : Int) (index : 19 ≤ e) :
    2 ≤ 2*e-32 ∧ 0 < (2*e-32)-1 := by
  omega

end ProjectionFibres.Lifting

#print axioms ProjectionFibres.Lifting.unrestricted_correction_order
#print axioms ProjectionFibres.Lifting.integral_correction_order
#print axioms ProjectionFibres.Lifting.physical_trace_order
