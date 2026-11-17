import NormLocal
import Mathlib.Data.Rat.Lemmas

/-! Reduction of the fraction representing one signed square root of the Hauptmodul. -/
namespace ZInQBlueprint.PoleNorm

def reduced (p q : ℤ) : ℤ := norm p q / factor p q
def reducedNumerator (p q : ℤ) : ℤ := sineNumerator p q / (factor p q)^3

theorem factor_pos (p q : ℤ) : 0 < factor p q := by
  unfold factor dyadicFactor triadicFactor
  split <;> split <;> decide

private theorem factor_dvd {p q : ℤ} (hc : IsCoprime p q) : factor p q ∣ norm p q := by
  obtain ⟨k,hk,_⟩ := dyadic_norm hc
  obtain ⟨m,hm,_⟩ := triadic_norm hc
  have cop : IsCoprime (dyadicFactor p q) (triadicFactor p) := by
    unfold dyadicFactor triadicFactor
    split <;> split <;> decide
  exact cop.mul_dvd ⟨k,hk⟩ ⟨m,hm⟩

theorem norm_eq {p q : ℤ} (hc : IsCoprime p q) : norm p q = factor p q * reduced p q := by
  exact (Int.mul_ediv_cancel' (factor_dvd hc)).symm

theorem numerator_eq (p q : ℤ) : sineNumerator p q = (factor p q)^3 * reducedNumerator p q := by
  exact (Int.mul_ediv_cancel' (factor_cube_dvd p q)).symm

theorem reduced_pos {p q : ℤ} (hc : IsCoprime p q) (hq : 0 < q) : 0 < reduced p q := by
  have hn : 0 < norm p q := by unfold norm; positivity
  rw [norm_eq hc] at hn
  exact pos_of_mul_pos_right hn (factor_pos p q).le

/-- Both small primes are units in the reduced norm, including in mixed parity charts. -/
theorem reduced_units {p q : ℤ} (hc : IsCoprime p q) :
    ¬ (2:ℤ) ∣ reduced p q ∧ ¬ (3:ℤ) ∣ reduced p q := by
  obtain ⟨k,hk,hu⟩ := dyadic_norm hc
  obtain ⟨m,hm,hv⟩ := triadic_norm hc
  have fac := norm_eq hc
  unfold factor at fac
  have hd : dyadicFactor p q ≠ 0 := by unfold dyadicFactor; split <;> decide
  have ht : triadicFactor p ≠ 0 := by unfold triadicFactor; split <;> decide
  have hk' : k=triadicFactor p * reduced p q := by
    apply mul_left_cancel₀ hd
    rw [← hk, ← mul_assoc,← fac]
  have hm' : m=dyadicFactor p q * reduced p q := by
    apply mul_left_cancel₀ ht
    rw [← hm, ← mul_assoc,mul_comm (triadicFactor p), ← fac]
  refine ⟨fun h => ?_,fun h => ?_⟩
  · have h₂ : (2:ℤ) ∣ k := hk' ▸ dvd_mul_of_dvd_right h _
    have := Int.emod_eq_zero_of_dvd h₂
    omega
  · have h₃ : (3:ℤ) ∣ m := hm' ▸ dvd_mul_of_dvd_right h _
    exact hv (Int.emod_eq_zero_of_dvd h₃)

/-- No further prime cancels. -/
theorem reduced_coprime {p q : ℤ} (hc : IsCoprime p q) :
    (reducedNumerator p q).natAbs.Coprime (reduced p q).natAbs := by
  by_contra h
  obtain ⟨l,hl,hA,hD⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have a : (l:ℤ) ∣ reducedNumerator p q := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hA)
  have d : (l:ℤ) ∣ reduced p q := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hD)
  have hn : (l:ℤ) ∣ norm p q := norm_eq hc ▸ dvd_mul_of_dvd_right d _
  have hu : (l:ℤ) ∣ sineNumerator p q := numerator_eq p q ▸ dvd_mul_of_dvd_right a _
  rcases prime_exception hc hl hn hu with rfl|rfl
  · exact (reduced_units hc).1 d
  · exact (reduced_units hc).2 d

def sine (p q : ℤ) : ℚ := (sineNumerator p q:ℚ)/(norm p q:ℚ)^3

theorem sine_fraction {p q : ℤ} (hc : IsCoprime p q) :
    sine p q = (reducedNumerator p q:ℚ)/(reduced p q:ℚ)^3 := by
  have h : (factor p q:ℚ) ≠ 0 := by exact_mod_cast (factor_pos p q).ne'
  unfold sine
  rw [numerator_eq p q,norm_eq hc]
  push_cast
  rw [mul_pow]
  field_simp

theorem sine_den {p q : ℤ} (hc : IsCoprime p q) (hq : 0 < q) :
    ((sine p q).den:ℤ) = (reduced p q)^3 := by
  have hpos := pow_pos (reduced_pos hc hq) 3
  have cop := (reduced_coprime hc).pow_right 3
  rw [sine_fraction hc, ← Int.cast_pow]
  apply Rat.den_div_eq_of_coprime hpos
  simpa only [Int.natAbs_pow] using cop

/-- The norm identity for the real and imaginary parts of a sixth power in Q(√−3). -/
theorem sixth_power (p q : ℤ) :
    16*norm p q^6-27*sineNumerator p q^2 =
      16*(p^6-45*p^4*q^2+135*p^2*q^4-27*q^6)^2 := by
  unfold norm sineNumerator
  ring

theorem sine_abs_le_one {p q : ℤ} (hq : 0 < q) : |sine p q| ≤ 1 := by
  have hn : 0 < norm p q := by unfold norm; positivity
  have hsq : sineNumerator p q ^ 2 ≤ (norm p q ^ 3)^2 := by
    nlinarith only [sixth_power p q, sq_nonneg (p^6-45*p^4*q^2+135*p^2*q^4-27*q^6),
      sq_nonneg (sineNumerator p q)]
  have ha : |sineNumerator p q| ≤ norm p q ^ 3 := by
    nlinarith [sq_abs (sineNumerator p q),abs_nonneg (sineNumerator p q),pow_pos hn 3]
  unfold sine
  have hpos : 0 < (norm p q:ℚ)^3 := by exact_mod_cast pow_pos hn 3
  rw [abs_div,abs_of_pos hpos,div_le_one hpos]
  exact_mod_cast ha

end ZInQBlueprint.PoleNorm
#print axioms ZInQBlueprint.PoleNorm.norm_eq
#print axioms ZInQBlueprint.PoleNorm.numerator_eq
#print axioms ZInQBlueprint.PoleNorm.reduced_units
#print axioms ZInQBlueprint.PoleNorm.reduced_coprime
#print axioms ZInQBlueprint.PoleNorm.sine_den
#print axioms ZInQBlueprint.PoleNorm.sixth_power
#print axioms ZInQBlueprint.PoleNorm.sine_abs_le_one
