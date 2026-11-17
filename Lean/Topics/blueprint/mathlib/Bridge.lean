import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-! Algebra used when compiling rational residuals. The lemmas work for all
finite lists; they do not identify the concrete list with the source compiler. -/

namespace QuarticBlueprint

/-- Retaining a computed coordinate and its defining row preserves the input
projection, for any later predicate on that coordinate. -/
theorem introduceAssignment {Input Value : Type*} (f : Input → Value)
    (accept : Input → Value → Prop) (x : Input) :
    (∃ y, y = f x ∧ accept x y) ↔ accept x (f x) :=
  ⟨fun ⟨_, heq, h⟩ => heq ▸ h, fun h => ⟨f x, rfl, h⟩⟩

variable {K : Type*} [Field K]

/-- Inserting a guarded quotient coordinate preserves the old witness predicate. -/
theorem guardedQuotient (a b : K) (accept : K → Prop) :
    (∃ d y : K, b * d = 1 ∧ b * y = a ∧ accept y) ↔ b ≠ 0 ∧ accept (a / b) := by
  constructor
  · rintro ⟨d, y, hd, hy, h⟩
    have hb : b ≠ 0 := by
      intro hz
      exact zero_ne_one (by simpa only [hz, zero_mul] using hd)
    have heq : y = a / b := (eq_div_iff_mul_eq hb).2 ((mul_comm y b).trans hy)
    exact ⟨hb, heq ▸ h⟩
  · rintro ⟨hb, h⟩
    exact ⟨b⁻¹, a / b, mul_inv_cancel₀ hb,
      (mul_comm b (a / b)).trans (div_mul_cancel₀ a hb), h⟩

/-- The list form of the sum of the squares of the evaluated quadratic rows. -/
def rowSquares (rows : List K) : K := rows.foldr (fun r rest => r * r + rest) 0

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem rowSquares_nonneg (rows : List K) : 0 ≤ rowSquares rows := by
  induction rows with
  | nil => exact le_refl 0
  | cons r rows ih => exact add_nonneg (mul_self_nonneg r) ih

/-- Vanishing of the compiled sum is equivalent to simultaneous row vanishing. -/
theorem rowSquares_eq_zero_iff (rows : List K) :
    rowSquares rows = 0 ↔ ∀ r ∈ rows, r = 0 := by
  induction rows with
  | nil => simp [rowSquares]
  | cons r rows ih =>
    change r * r + rowSquares rows = 0 ↔ _
    rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg r) (rowSquares_nonneg rows),
      mul_self_eq_zero, ih]
    simp

end QuarticBlueprint

#check @eq_div_iff_mul_eq
#check @mul_self_nonneg
#check @add_eq_zero_iff_of_nonneg
#print axioms QuarticBlueprint.introduceAssignment
#print axioms QuarticBlueprint.guardedQuotient
#print axioms QuarticBlueprint.rowSquares_eq_zero_iff
