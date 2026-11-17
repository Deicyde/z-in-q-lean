import DoubleVanishing
import PreparedExample
import Mathlib.Data.Rat.Sqrt

namespace Sun28.MultiplierChoice
open Sun28.ScalarHeight Sun28.PointFibres
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-- Finite check on the paper's exact multiplier list, at the prescribed scalar argument. -/
private theorem hard_table : ∀ m ∈ smallMultipliers, m ≠ 0 ∧ pole ≠ m ∧
    ¬(IsSquare (1-pole/m) ∨ IsSquare (-3*(1-pole/m))) := by decide +kernel

theorem prescribed_no_double : Sun28.TwistRank.ClassPrepared pole ∧
    ∀ m ∈ smallMultipliers, ¬ DoubleRoot m pole := by
  refine ⟨scalar_input_prepared, ?_⟩
  intro m mem root
  obtain ⟨mn,diff,fail⟩ := hard_table m mem
  exact fail ((double_root_iff mn pole_prepared.2.1.ne' diff).mp root)
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.prescribed_no_double
