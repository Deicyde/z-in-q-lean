import PaperDiscriminant

/-! At every unexceptional prime, a positive valuation of the Liu invariant
occurs exactly at a zero or a pole of the rational parameter. -/
namespace ZInQBlueprint.JacobianHeight
open SixContactHP
noncomputable section

/-- Zeros have coefficient three and poles have coefficient two.
Primes at which j and 12 are units contribute nothing, even when j+1 vanishes modulo p. -/
theorem tame_order {p : ℕ} [hp : Fact p.Prime] (large : 3 < p) {j : ℚ}
    (nz : j ≠ 0) (succ : j+1 ≠ 0) :
    max 0 (padicValRat p (igusaPole j)) =
      3 * max 0 (padicValRat p j) + 2 * max 0 (-padicValRat p j) := by
  have unit12 : padicValRat p (12:ℚ) = 0 := by
    have nd : ¬p ∣ 12 := fun hd => by
      rcases hp.out.dvd_mul.mp (show p ∣ 3*2^2 from hd) with h | h
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) large) h
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)) (hp.out.dvd_of_dvd_pow h)
    exact (padicValRat.of_nat (p:=p) (n:=12)).trans (by exact_mod_cast padicValNat.eq_zero_of_not_dvd nd)
  by_cases pole : padicValRat p j < 0
  · rw [pole_order large pole, max_eq_left pole.le, max_eq_right (by omega : 0 ≤ -padicValRat p j),
      max_eq_right (by omega : 0 ≤ -2*padicValRat p j)]
    ring
  have nonneg : 0 ≤ padicValRat p j := le_of_not_gt pole
  have sumpos : 0 ≤ padicValRat p (j+1) := by
    have he := padicValRat.min_le_padicValRat_add succ (p:=p) (q:=j) (r:=1)
    simpa [min_eq_right nonneg] using he
  have v : padicValRat p (igusaPole j) = 3*padicValRat p j - 5*padicValRat p (j+1) := by
    unfold igusaPole
    rw [padicValRat.div (pow_ne_zero _ nz) (pow_ne_zero _ (mul_ne_zero (by norm_num) succ)),
      padicValRat.pow, padicValRat.pow, padicValRat.mul (by norm_num) succ, unit12]
    push_cast
    ring
  rw [v, max_eq_right nonneg, max_eq_left (by omega : -(padicValRat p j) ≤ 0)]
  by_cases pos : 0 < padicValRat p j
  · have lt : padicValRat p (1:ℚ) < padicValRat p j := by simpa using pos
    have he := padicValRat.add_eq_of_lt (by simpa [add_comm] using succ : (1:ℚ)+j ≠ 0) one_ne_zero nz lt
    rw [add_comm] at he
    simp only [padicValRat.one] at he
    rw [he, mul_zero, sub_zero, max_eq_right (by omega : 0 ≤ 3*padicValRat p j)]
    ring
  · have zero : padicValRat p j = 0 := by omega
    rw [zero, mul_zero, zero_sub, max_eq_left (by omega : -(5*padicValRat p (j+1)) ≤ 0)]
    ring

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.tame_order
