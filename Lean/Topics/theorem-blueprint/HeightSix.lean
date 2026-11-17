import ApplicationLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.IntervalCases

namespace ZInQBlueprint.SixContact
open ZInQBlueprint

def F (u : ℚ) := u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
def G (u : ℚ) := 7*u^2+300*u+3600
def H (u : ℚ) := (u^2-60*u-1800)*(13*u^2+480*u+3600)*(11*u^2+600*u+7200)
def J (u : ℚ) := -57600*(F u)^2/(G u)^6
def contacts : Finset ℚ := {0,-15,-20,-24,-30,-60}

theorem positive_denominator (u : ℚ) : 0 < G u := by
  unfold G
  nlinarith [sq_nonneg (7*u+150)]

/-- The affine pullback of the third marked value is a rational square. -/
theorem pullback_square (u : ℚ) : 1+27*J u/16 = (H u/(G u)^3)^2 := by
  have hg : G u ≠ 0 := ne_of_gt (positive_denominator u)
  unfold J
  field_simp
  unfold H F G
  ring

private theorem nonsquare_three (x : ℚ) : x^2 ≠ 3 := by
  intro e
  have hs : IsSquare (3:ℚ) := ⟨x,by simpa [sq] using e.symm⟩
  have hn : IsSquare (3:ℕ) := Rat.isSquare_natCast_iff.mp hs
  obtain ⟨k,hk⟩ := hn
  by_cases hk1 : k ≤ 1
  · interval_cases k <;> norm_num at hk
  · have h4 := Nat.mul_self_le_mul_self (show 2 ≤ k by omega)
    omega

/-- All three apparent quadratic exceptions are absent over the rationals. -/
theorem third_fibre_empty (u : ℚ) : H u ≠ 0 := by
  unfold H
  intro eqn
  rcases mul_eq_zero.mp eqn with h | h
  · rcases mul_eq_zero.mp h with h | h
    · apply nonsquare_three ((u-30)/30)
      linear_combination h/900
    · apply nonsquare_three ((13*u+240)/60)
      linear_combination 13*h/3600
  · apply nonsquare_three ((11*u+300)/60)
    linear_combination 11*h/3600

theorem avoids_third_value (u : ℚ) : J u ≠ -16/27 := by
  intro eqn
  have hs := pullback_square u
  rw [eqn] at hs
  have hne := div_ne_zero (third_fibre_empty u) (pow_ne_zero 3 (ne_of_gt (positive_denominator u)))
  norm_num at hs
  exact (pow_ne_zero 2 hne) hs.symm

noncomputable def ratHeight (u : ℚ) : ℝ := Real.log (max |(u.num : ℝ)| (u.den : ℝ))
def rationalOrder (p : ℕ) (v : ℚ) : ℤ := (padicValNat p v.num.natAbs : ℤ) - padicValNat p v.den
noncomputable def support (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contacts, (u-c).num.natAbs).primeFactors with
    p ∉ S ∧ ∃ c ∈ contacts, 0 < rationalOrder p (u-c) ∧ Odd (rationalOrder p (u-c)), p

/-- The geometry must realize the same fibre and normalization in both estimates.
This records the numerical consequences consumed by the final computation. -/
structure FibreBounds (u : ℚ) (S : Finset ℕ) (B : ℝ) where
  stableHeight : ℝ
  thetaHeight : ℝ
  rootBound : ratHeight u ≤ ratHeight (J u) + 74
  igusa : ratHeight (J u) ≤ 40*thetaHeight + 22
  theta : thetaHeight ≤ (10000*2^24)*max 1 stableHeight
  conductor : max 1 stableHeight ≤ B*(support S u : ℝ)^24

theorem contact_bound {u : ℚ} {S : Finset ℕ} {B : ℝ} (data : FibreBounds u S B) :
    ratHeight u ≤ (2*10^13*B)*(support S u : ℝ)^24 := by
  apply six_contact_comparison _ data.stableHeight _ _ _ data.conductor
  have h := le_max_left (1:ℝ) data.stableHeight
  linarith [data.rootBound,data.igusa,data.theta]

#print axioms pullback_square
#print axioms third_fibre_empty
#print axioms avoids_third_value
#print axioms contact_bound
end ZInQBlueprint.SixContact
