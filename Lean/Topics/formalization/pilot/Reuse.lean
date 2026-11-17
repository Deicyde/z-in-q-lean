module

public import ZInQ.AlphaCongruence
public import ZInQ.AlphaPowerBounds
import ZInQ.EquationCompression
import ZInQ.ModelCoordinateIdentities
import ZInQ.PoleValuation
import ZInQ.RationalSeparation
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.LinearCombination

public section

namespace QuarticReuse
open ZInQ.AlphaPower

/-- The signed recurrence gives the index modulo B+2, including B=0 and n=0. -/
theorem plusTwo_signed_congruence (B n : ℕ) :
    (B : ℤ) + 2 ∣ (-1 : ℤ) ^ n * alphaZ B n + (n : ℤ) := by
  have pair : ∀ k : ℕ,
      ((B : ℤ) + 2 ∣ (-1 : ℤ) ^ k * alphaZ B k + (k : ℤ)) ∧
      ((B : ℤ) + 2 ∣ (-1 : ℤ) ^ (k + 1) * alphaZ B (k + 1) + ((k+1 : ℕ) : ℤ)) := by
    intro k
    induction k with
    | zero => simp [alphaZ_zero, alphaZ_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨u, hu⟩ := ih.1
      obtain ⟨v, hv⟩ := ih.2
      refine ⟨(k : ℤ) + 1 - (B : ℤ)*v - u, ?_⟩
      change (-1 : ℤ)^(k+2) * alphaZ B (k+2) + ((k+2 : ℕ) : ℤ) = _
      rw [alphaZ_add_two]
      push_cast at hu hv ⊢
      simp only [pow_succ] at hv ⊢
      linear_combination -(B : ℤ) * hv - hu
  exact (pair n).1

/-- The two modulus choices used after Lucas descent in S19. -/
theorem both_index_divisibilities (B n : ℕ) :
    (((B : ℤ) - 2 ∣ alphaZ B n) → (B : ℤ) - 2 ∣ (n : ℤ)) ∧
    (((B : ℤ) + 2 ∣ alphaZ B n) → (B : ℤ) + 2 ∣ (n : ℤ)) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := sub_two_dvd_alphaZ_sub_index B n
    refine ⟨u-v, ?_⟩
    linear_combination hu - hv
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := plusTwo_signed_congruence B n
    refine ⟨v-(-1 : ℤ)^n*u, ?_⟩
    linear_combination hv - (-1 : ℤ)^n * hu

/-- The normalized Lucas estimate of S19, with A=k+7 and W the absolute
value of the second coordinate. Both signs of the original parameter occur. -/
theorem normalized_lucas_growth (k T W : ℕ) (hwpos : 0 < W)
    (hcurve : T*T + W*W = 1 + (k+7)*T*W)
    (hdiv : k+5 ∣ W ∨ k+9 ∣ W) : 2^(k+3) ≤ T := by
  have indexLower (j : ℕ) (hw : (W : ℤ) = alphaZ (k+7) j) : k+5 ≤ j := by
    have hj : 0 < j := by
      by_contra! h
      have : j = 0 := by omega
      rw [this, alphaZ_zero] at hw
      omega
    have h := both_index_divisibilities (k+7) j
    rw [← hw] at h
    have hm : ((k+7 : ℕ) : ℤ) - 2 = ((k+5 : ℕ) : ℤ) := by push_cast; ring
    have hp : ((k+7 : ℕ) : ℤ) + 2 = ((k+9 : ℕ) : ℤ) := by push_cast; ring
    rw [hm, hp] at h
    rcases hdiv with hd | hd
    · exact Nat.le_of_dvd hj (Int.natCast_dvd_natCast.mp (h.1 (Int.natCast_dvd_natCast.mpr hd)))
    · have := Nat.le_of_dvd hj (Int.natCast_dvd_natCast.mp (h.2 (Int.natCast_dvd_natCast.mpr hd)))
      omega
  have growth (j : ℕ) (hj : k+3 < j) : (2 : ℤ)^(k+3) ≤ alphaZ (k+7) j := by
    have mono : Monotone (alphaZ (k+7)) :=
      monotone_nat_of_le_succ fun n => (alphaZ_succ_strict _ n (by omega)).le
    have base : (2 : ℤ) ≤ ((k+6 : ℕ) : ℤ) := by omega
    calc
      (2 : ℤ)^(k+3) ≤ ((k+6 : ℕ) : ℤ)^(k+3) :=
        pow_le_pow_left₀ (by decide) base _
      _ ≤ alphaZ (k+7) ((k+3)+1) := pow_le_alphaZ_succ (k+6) (k+3) (by omega)
      _ ≤ alphaZ (k+7) j := mono (by omega)
  have target : (2 : ℤ)^(k+3) ≤ (T : ℤ) := by
    rcases lt_trichotomy T W with h | h | h
    · have eqn : 1 + (k+7)*W*T = W*W + T*T := by nlinarith only [hcurve]
      obtain ⟨n, ht, hw⟩ := alphaZ_descent (k+7) T W h eqn
      have := indexLower (n+1) hw
      rw [ht]
      exact growth n (by omega)
    · subst W
      have hh : 2*(T*T) ≤ (k+7)*(T*T) := Nat.mul_le_mul_right _ (by omega)
      nlinarith only [hcurve, hh]
    · obtain ⟨n, hw, ht⟩ := alphaZ_descent (k+7) W T h hcurve.symm
      have := indexLower n hw
      rw [ht]
      exact growth (n+1) (by omega)
  exact_mod_cast target

/-- S19 on the signed integer inputs of the original rational system. -/
theorem lucas_growth (a t b : ℤ) (hb : b ≠ 0) (ha : 7 ≤ a.natAbs)
    (hf : t^2 - a*(a-2)*t*b + (a-2)^2*b^2 - 1 = 0) :
    2^(a.natAbs - 4) ≤ t.natAbs := by
  let k := a.natAbs - 7
  have hk : a.natAbs = k+7 := by dsimp [k]; omega
  let w := (a-2)*b
  have hA : a-2 ≠ 0 := by
    intro h
    have h2 : a = 2 := by omega
    rw [h2] at ha
    exact (by decide : ¬7 ≤ (2 : ℤ).natAbs) ha
  have hw : w ≠ 0 := mul_ne_zero hA hb
  have hcurve : t*t+w*w = 1+a*t*w := by
    dsimp [w]
    linear_combination hf
  have hpos : 0 ≤ a*t*w := by
    have h1 : 0 < w*w := mul_self_pos.mpr hw
    have h2 : 0 ≤ t*t := mul_self_nonneg t
    omega
  have hZ : (t.natAbs : ℤ)*(t.natAbs : ℤ)+(w.natAbs : ℤ)*(w.natAbs : ℤ) =
      1+(a.natAbs : ℤ)*(t.natAbs : ℤ)*(w.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs, ← abs_mul, abs_of_nonneg (mul_self_nonneg t),
      abs_of_nonneg (mul_self_nonneg w), abs_of_nonneg hpos] using hcurve
  have hN : t.natAbs*t.natAbs+w.natAbs*w.natAbs =
      1+a.natAbs*t.natAbs*w.natAbs := by exact_mod_cast hZ
  rw [hk] at hN
  have hd : (a-2).natAbs ∣ w.natAbs := by
    dsimp [w]
    rw [Int.natAbs_mul]
    exact ⟨b.natAbs, rfl⟩
  have ha' := Int.natCast_natAbs a
  have hw' := Int.natCast_natAbs (a-2)
  have hmod : k+5 ∣ w.natAbs ∨ k+9 ∣ w.natAbs := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h] at ha'
      rw [abs_of_nonneg (by omega : 0 ≤ a-2)] at hw'
      rw [show (a-2).natAbs = k+5 by omega] at hd
      exact Or.inl hd
    · rw [abs_of_nonpos (by omega : a ≤ 0)] at ha'
      rw [abs_of_nonpos (by omega : a-2 ≤ 0)] at hw'
      rw [show (a-2).natAbs = k+9 by omega] at hd
      exact Or.inr hd
  rw [show a.natAbs - 4 = k+3 by omega]
  exact normalized_lucas_growth k _ _ (Int.natAbs_pos.mpr hw) hN hmod

end QuarticReuse

#check @ZInQ.AlphaPower.alphaZ_descent
#check @ZInQ.AlphaPower.pow_le_alphaZ_succ
#check @ZInQ.AlphaPower.sub_two_dvd_alphaZ_sub_index
#check @ZInQ.EquationCompression.eval_compile_eq_zero_iff
#check @ZInQ.ModelCoordinates.tangent_coordinates
#check @ZInQ.ValuationObstruction.curve_rhs_nonzero_and_valuation
#check @ZInQ.eq_int_of_abs_sub_lt_inv_den
#check @FormalGroup
#check @WeierstrassCurve.Affine.approx_parallelogram_law
#check @groupCohomology.H1InfRes_exact
#print axioms QuarticReuse.plusTwo_signed_congruence
#print axioms QuarticReuse.both_index_divisibilities
#print axioms QuarticReuse.normalized_lucas_growth
#print axioms QuarticReuse.lucas_growth
