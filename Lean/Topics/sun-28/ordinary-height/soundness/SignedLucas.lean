import ZInQ.AlphaCongruence
import ZInQKernel.Compiler.Exponential.AlphaPell
import OrdinaryAnchors
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The signed Lucas bound in Sun, Proposition 7.3, from adjacent Pell coordinates. -/
namespace Sun28.Ordinary
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


private theorem normalized_lucas_power (k T W : ℕ) (hwpos : 0<W)
    (hcurve : T*T+W*W=1+(k+7)*T*W) (hdiv : k+5∣W ∨ k+9∣W) :
    (k+6)^(k+3)≤T := by
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
  have growth (j : ℕ) (hj : k+3<j) : ((k+6:ℕ):ℤ)^(k+3)≤alphaZ (k+7) j := by
    have mono : Monotone (alphaZ (k+7)) :=
      monotone_nat_of_le_succ fun r => (alphaZ_succ_strict _ r (by omega)).le
    exact (pow_le_alphaZ_succ (k+6) (k+3) (by omega)).trans (mono (by omega))
  obtain ⟨j,⟨ht,hw⟩|⟨ht,hw⟩⟩ := alphaZ_pell_unordered (b:=k+7) (x:=T) (y:=W)
    (by omega) (by nlinarith only [hcurve])
  · have bound:=indexLower (j+1) hw
    have target:=growth j (by omega)
    rw [←ht] at target
    exact_mod_cast target
  · have bound:=indexLower j hw
    have target:=growth (j+1) (by omega)
    rw [←ht] at target
    exact_mod_cast target

/-- The full base |a|−1 in the original recurrence for Sun's signed parameters. -/
theorem signed_lucas_power (a t b : ℤ) (hb : b≠0) (ha : 7≤a.natAbs)
    (hf : lucas a t b=0) :
    (a.natAbs-1)^(a.natAbs-4)≤t.natAbs := by
  unfold lucas at hf
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
  rw [show a.natAbs-1=k+6 by omega,show a.natAbs - 4 = k+3 by omega]
  exact normalized_lucas_power k _ _ (Int.natAbs_pos.mpr hw) hN hmod

/-- Glazer's strict logarithmic growth lemma, including negative parameters and ordinates. -/
theorem signed_lucas_log (s t z : ℤ) (nz : z≠0) (large : 7≤s.natAbs)
    (eqn : lucas s t z=0) : |(s:ℝ)|-3<Real.log |(t:ℝ)| := by
  let k := s.natAbs-4
  have kl : 3≤k := by dsimp [k]; omega
  have hk : s.natAbs=k+4 := by dsimp [k]; omega
  have power := signed_lucas_power s t z nz large eqn
  have lb : (4:ℕ)^k≤t.natAbs := (Nat.pow_le_pow_left (by omega : 4≤s.natAbs-1) k).trans power
  have lbR : (4:ℝ)^k≤(t.natAbs:ℝ) := by exact_mod_cast lb
  have logs := Real.log_le_log (by positivity : 0<(4:ℝ)^k) lbR
  have four : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_pow,four] at logs
  have klR : (3:ℝ)≤k := by exact_mod_cast kl
  have hkR : (s.natAbs:ℝ)=(k:ℝ)+4 := by exact_mod_cast hk
  rw [←Int.cast_abs,←Nat.cast_natAbs,←Int.cast_abs,←Nat.cast_natAbs]
  have l2 : (2:ℝ)/3<Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_pos (show 0<(k:ℝ) by linarith) (sub_pos.mpr l2)]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.plusTwo_signed_congruence
#print axioms Sun28.Ordinary.both_index_divisibilities
#print axioms Sun28.Ordinary.signed_lucas_power
#print axioms Sun28.Ordinary.signed_lucas_log
