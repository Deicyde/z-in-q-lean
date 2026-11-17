import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Quartic262

def weight (weighted : Bool) (extra : ℕ) : ℚ :=
  if weighted then (extra : ℚ) + 1 else 1

theorem weight_pos (t : Bool) (w : ℕ) : 0 < weight t w := by
  cases t
  · exact zero_lt_one
  · change 0 < (w:ℚ)+1
    positivity

def squares (t : Bool) : List (ℕ × ℚ) → ℚ
  | [] => 0
  | (w,x) :: rest => weight t w * x^2 + squares t rest

theorem squares_nonneg (t : Bool) (values : List (ℕ × ℚ)) : 0 ≤ squares t values := by
  induction values with
  | nil => rfl
  | cons p _ ih =>
    exact add_nonneg (mul_nonneg (weight_pos t p.1).le (sq_nonneg p.2)) ih

theorem squares_zero_iff (t : Bool) (values : List (ℕ × ℚ)) :
    squares t values = 0 ↔ ∀ p ∈ values, p.2 = 0 := by
  induction values with
  | nil => simp [squares]
  | cons p rest ih =>
    rcases p with ⟨w,x⟩
    rw [squares, add_eq_zero_iff_of_nonneg (mul_nonneg (weight_pos t w).le (sq_nonneg x))
      (squares_nonneg t rest), ih]
    simp [ne_of_gt (weight_pos t w)]

theorem change_weights (values : List (ℕ × ℚ)) :
    squares true values = 0 ↔ squares false values = 0 :=
  (squares_zero_iff true values).trans (squares_zero_iff false values).symm

end Quartic262
