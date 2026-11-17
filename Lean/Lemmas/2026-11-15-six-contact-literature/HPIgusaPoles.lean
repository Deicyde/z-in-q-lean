import ParameterReturn
import Mathlib

/-! Nonarchimedean part of Habegger--Pazuki, Theorem 4.5, on the
discriminant-six family. The polynomial invariants have half-weights 1 and 5. -/
namespace SixContactHP
open ZInQ ZInQBlueprint.PoleNorm
noncomputable section

/-- The absolute invariant J₁₀/J₂⁵ of the six-contact fibre. -/
def igusaPole (j : ℚ) : ℚ := j^3 / (12*(j+1))^5

theorem igusaPole_of_weighted {j scale : ℚ} (hs : scale ≠ 0) :
    scale^5*j^3/(scale*(12*(j+1)))^5 = igusaPole j := by
  unfold igusaPole
  rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero 5 hs)]

/-- The product in the universal finite summand costs exactly twice a pole of j. -/
theorem pole_order {j : ℚ} {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (neg : padicValRat p j < 0) :
    padicValRat p (igusaPole j) = -2 * padicValRat p j := by
  have hj : j ≠ 0 := by rintro rfl; simp at neg
  have hs : j+1 ≠ 0 := by
    intro he
    have hh : j = -1 := by linarith
    simp [hh] at neg
  have hsum := padicValRat.add_eq_of_lt hs hj one_ne_zero (by simpa using neg)
  have unit : ¬ p ∣ 12 := by
    intro h
    have hm : p ∣ 3*2^2 := h
    rcases hp.out.dvd_mul.mp hm with ha|hb
    · exact (Nat.not_dvd_of_pos_of_lt (by decide) hp3) ha
    · have hz := hp.out.dvd_of_dvd_pow hb
      exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)) hz
  have vt : padicValRat p (12 : ℚ) = 0 := by
    change padicValRat p ((12:ℕ):ℚ) = 0
    exact (padicValRat.of_nat (p := p) (n := 12)).trans (by exact_mod_cast padicValNat.eq_zero_of_not_dvd unit)
  unfold igusaPole
  rw [padicValRat.div (pow_ne_zero _ hj) (pow_ne_zero _ (mul_ne_zero (by norm_num) hs)),
    padicValRat.pow, padicValRat.pow, padicValRat.mul (by norm_num) hs, vt,hsum]
  norm_num
  ring

private theorem prime_den_order (j : ℚ) {p : ℕ} (hp : p ∈ j.den.primeFactors) :
    0 < padicValNat p j.den ∧ padicValRat p j = -(j.den.factorization p : ℤ) := by
  have prime := Nat.prime_of_mem_primeFactors hp
  let _ : Fact p.Prime := ⟨prime⟩
  have pos := one_le_padicValNat_of_dvd j.den_nz (Nat.dvd_of_mem_primeFactors hp)
  rcases Rat.num_or_den_zero_padicVal j prime with h|h
  · refine ⟨by omega, ?_⟩
    simp [padicValRat_def,h,Nat.factorization_def j.den prime]
  · omega

/-- The denominator of J(u) is prime to 6, including rational inputs with dyadic denominator. -/
theorem prime_den_large (u : ℚ) (hu : u ≠ 0) {p : ℕ}
    (hp : p ∈ (JHeight.Jmap u).den.primeFactors) : 3 < p := by
  have prime := Nat.prime_of_mem_primeFactors hp
  let t := parameter u
  have cop : IsCoprime t.num (t.den:ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact t.reduced
  have units := reduced_units cop
  have nd := Nat.dvd_of_mem_primeFactors hp
  have dd : (p : ℤ) ∣ denominatorRoot u ^ 6 := by
    rw [← j_denominator u hu]
    exact_mod_cast nd
  have d : (p:ℤ) ∣ denominatorRoot u := (Nat.prime_iff_prime_int.mp prime).dvd_of_dvd_pow dd
  change (p:ℤ) ∣ reduced t.num (t.den:ℤ) at d
  have hp2 := prime.two_le
  by_contra! sm
  rcases (show p=2 ∨ p=3 by omega) with rfl|rfl
  · exact units.1 d
  · exact units.2 d

/-- Drop all finite contributions except the poles of J. -/
def retained (j : ℚ) : ℝ :=
  ∑ p ∈ j.den.primeFactors, (max (0:ℤ) (padicValRat p (igusaPole j)) : ℝ) * Real.log p

theorem retained_eq (u : ℚ) (hu : u ≠ 0) :
    retained (JHeight.Jmap u) = 2*ratHeight (JHeight.Jmap u) := by
  let j := JHeight.Jmap u
  have hl : ratHeight j = Real.log j.den := by
    have hh := j_height_exact u hu
    have he : (j.den : ℝ) = (denominatorRoot u:ℝ)^6 := by exact_mod_cast j_denominator u hu
    rw [he,Real.log_pow,hh]
    norm_num
  rw [show JHeight.Jmap u=j from rfl,hl, Real.log_nat_eq_sum_factorization]
  unfold retained
  simp only [Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  let _ : Fact p.Prime := ⟨prime⟩
  obtain ⟨positive,order⟩ := prime_den_order j hp
  have neg : padicValRat p j < 0 := by
    rw [order,Nat.factorization_def j.den prime]
    exact neg_neg_of_pos (by exact_mod_cast positive)
  rw [pole_order (prime_den_large u hu hp) neg,order]
  push_cast
  ring_nf
  rw [max_eq_right (by positivity)]
  ring

end
end SixContactHP

#print axioms SixContactHP.igusaPole_of_weighted
#print axioms SixContactHP.pole_order
#print axioms SixContactHP.prime_den_large
#print axioms SixContactHP.retained_eq
