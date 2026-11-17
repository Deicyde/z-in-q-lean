import CoarseConic
import Mathlib.Data.Rat.Sqrt

/-! Absolute values of the coordinates in Errthum, Table 2. The row of
discriminant −3 is the point at infinity. Squaring is unnecessary for its
removal: the denominator test below treats it projectively. -/
namespace ZInQBlueprint.QuaternionLift
open SixContact CoarseConic

abbrev CMRow := ℤ × ℕ × ℕ

def rationalCMRows : List CMRow :=
  [
    (-3, 1, 0),
    (-4, 0, 1),
    (-24, 1, 1),
    (-40, 3 ^ 7, 5 ^ 3),
    (-52, 2 ^ 2 * 3 ^ 7, 5 ^ 6),
    (-19, 3 ^ 7, 2 ^ 10),
    (-84, 2 ^ 2 * 7 ^ 2, 3 ^ 3),
    (-88, 3 ^ 7 * 7 ^ 4, 5 ^ 6 * 11 ^ 3),
    (-100, 2 ^ 4 * 3 ^ 7 * 7 ^ 4 * 5, 11 ^ 6),
    (-120, 7 ^ 4, 3 ^ 3 * 5 ^ 3),
    (-132, 2 ^ 4 * 11 ^ 2, 5 ^ 6),
    (-148, 2 ^ 2 * 3 ^ 7 * 7 ^ 4 * 11 ^ 4, 5 ^ 6 * 17 ^ 6),
    (-168, 7 ^ 2 * 11 ^ 4, 5 ^ 6),
    (-43, 3 ^ 7 * 7 ^ 4, 2 ^ 10 * 5 ^ 6),
    (-51, 7 ^ 4, 2 ^ 10),
    (-228, 2 ^ 6 * 7 ^ 4 * 19 ^ 2, 3 ^ 6 * 5 ^ 6),
    (-232, 3 ^ 7 * 7 ^ 4 * 11 ^ 4 * 19 ^ 4, 5 ^ 6 * 23 ^ 6 * 29 ^ 3),
    (-67, 3 ^ 7 * 7 ^ 4 * 11 ^ 4, 2 ^ 16 * 5 ^ 6),
    (-75, 11 ^ 4, 2 ^ 10 * 3 ^ 3 * 5),
    (-312, 7 ^ 4 * 23 ^ 4, 5 ^ 6 * 11 ^ 6),
    (-372, 2 ^ 2 * 7 ^ 4 * 19 ^ 4 * 31 ^ 2, 3 ^ 3 * 5 ^ 6 * 11 ^ 6),
    (-408, 7 ^ 4 * 11 ^ 4 * 31 ^ 4, 3 ^ 6 * 5 ^ 6 * 17 ^ 3),
    (-123, 7 ^ 4 * 19 ^ 4, 2 ^ 10 * 5 ^ 6),
    (-147, 11 ^ 4 * 23 ^ 4, 2 ^ 10 * 3 ^ 3 * 5 ^ 6 * 7),
    (-163, 3 ^ 11 * 7 ^ 4 * 19 ^ 4 * 23 ^ 4, 2 ^ 10 * 5 ^ 6 * 11 ^ 6 * 17 ^ 6),
    (-708, 2 ^ 8 * 7 ^ 4 * 11 ^ 4 * 47 ^ 4 * 59 ^ 2, 5 ^ 6 * 17 ^ 6 * 29 ^ 6),
    (-267, 7 ^ 4 * 31 ^ 4 * 43 ^ 4, 2 ^ 16 * 5 ^ 6 * 11 ^ 6) ]

def absoluteCoordinate (a : CMRow) : ℚ := (a.2.1 : ℚ) / (a.2.2 : ℚ)

def splitTests (t : ℚ) : Prop :=
  0 < t ∧ t < 1 ∧ IsSquare (t / 3) ∧ IsSquare (1 - t)

instance (t : ℚ) : Decidable (splitTests t) :=
  inferInstanceAs (Decidable (0 < t ∧ t < 1 ∧ IsSquare (t / 3) ∧ IsSquare (1 - t)))

/-- For values strictly between zero and one, the first square test leaves
only the four displayed discriminants in the published table. -/
theorem first_filter :
    ((rationalCMRows.filter fun a => let t := absoluteCoordinate a
      decide (0 < t ∧ t < 1 ∧ IsSquare (t / 3))).map Prod.fst) =
    [-52, -148, -43, -163] := by decide +kernel

theorem table_filter :
    (rationalCMRows.filter fun a => decide (splitTests (absoluteCoordinate a))) = [] := by
  decide +kernel

/-- Errthum's coordinate is −27j/16. The two identities hold at every
rational parameter outside the six contacts. -/
theorem tests_at_slope {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    splitTests (-27 * J u / 16) := by
  obtain ⟨lo,hi⟩ := unmarked_range hu
  refine ⟨by linarith, by linarith, ⟨3 * r u / 4,?_⟩, ⟨h u,?_⟩⟩
  · rw [first_square]
    ring
  · have e := pullback_square u
    change 1 + 27 * J u / 16 = (h u)^2 at e
    linear_combination e

/-- No row in the entire rational CM table can be the coordinate of our
fibre. Cross-products make the statement apply to the infinite row too. -/
theorem avoids_cm_table {u : ℚ} (hu : u ∉ ZInQ.contactSet) {a : CMRow}
    (ha : a ∈ rationalCMRows) :
    |(-27 * J u / 16) * (a.2.2 : ℚ)| ≠ (a.2.1 : ℚ) := by
  let t := -27 * J u / 16
  have tests : splitTests t := tests_at_slope hu
  intro he
  by_cases hn : a.2.2 = 0
  · have inf : (rationalCMRows.filter fun b => decide (b.2.2 = 0)) = [(-3,1,0)] := by decide +kernel
    have mem : a ∈ rationalCMRows.filter (fun b => decide (b.2.2 = 0)) := List.mem_filter.mpr ⟨ha,by simp [hn]⟩
    rw [inf,List.mem_singleton] at mem
    subst a
    norm_num at he
  · have hn' : (a.2.2 : ℚ) ≠ 0 := by exact_mod_cast hn
    have ht : t = absoluteCoordinate a := by
      apply (eq_div_iff hn').mpr
      change |t * (a.2.2 : ℚ)| = _ at he
      rw [abs_of_nonneg (mul_nonneg tests.1.le (by positivity))] at he
      exact he
    have mem : a ∈ rationalCMRows.filter (fun b => decide (splitTests (absoluteCoordinate b))) :=
      List.mem_filter.mpr ⟨ha,by simp [← ht,tests]⟩
    rw [table_filter] at mem
    exact List.not_mem_nil mem

end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.first_filter
#print axioms ZInQBlueprint.QuaternionLift.table_filter
#print axioms ZInQBlueprint.QuaternionLift.tests_at_slope
#print axioms ZInQBlueprint.QuaternionLift.avoids_cm_table
