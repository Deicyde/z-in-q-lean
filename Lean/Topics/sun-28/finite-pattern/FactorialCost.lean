import ReducedProjection
import Mathlib.Data.Nat.Choose.Factorization

namespace Sun28.FinitePattern
open Finset Real Sun28.SinglePrime
noncomputable section

/-- The first term of Legendre's formula already controls the reciprocal-prime sum. -/
theorem factorial_prime_sum {L : ℕ} (hL : 0 < L) (P : Finset ℕ)
    (primes : ∀ p ∈ P, p.Prime ∧ p ≤ L) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ 2 * Real.log L := by
  let F := L.factorial
  have factor (p : ℕ) (hp : p.Prime) : L / p ≤ F.factorization p := by
    rw [show F = L.factorial from rfl,
      Nat.factorization_factorial hp (by omega : Nat.log p L < Nat.log p L + 2)]
    simpa using (Finset.single_le_sum (f := fun i => L / p ^ i)
      (fun i _ => Nat.zero_le _) (show 1 ∈ Finset.Ico 1 (Nat.log p L + 2) by simp))
  have sub : P ⊆ F.primeFactors := by
    intro p hp
    obtain ⟨q, le⟩ := primes p hp
    exact Nat.mem_primeFactors.mpr ⟨q, Nat.dvd_factorial q.pos le, Nat.factorial_ne_zero _⟩
  have mass : (∑ p ∈ P, (F.factorization p : ℝ) * Real.log p) ≤ Real.log F := by
    rw [Real.log_nat_eq_sum_factorization]
    change _ ≤ ∑ p ∈ F.primeFactors, (F.factorization p : ℝ) * Real.log p
    apply sum_le_sum_of_subset_of_nonneg sub
    intro p hp _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  have compare (p : ℕ) (hp : p ∈ P) :
      (L : ℝ) * (Real.log p / p) ≤ 2 * ((F.factorization p : ℝ) * Real.log p) := by
    obtain ⟨q, le⟩ := primes p hp
    have pp : (0 : ℝ) < p := by exact_mod_cast q.pos
    have rem := Nat.mod_lt L q.pos
    have eq := Nat.mod_add_div L p
    have quot := (Nat.one_le_div_iff q.pos).mpr le
    have nq : L ≤ 2 * (L / p) * p := by
      nlinarith only [rem, eq, Nat.mul_le_mul_right p quot]
    have cap : (L : ℝ) ≤ 2 * (F.factorization p : ℝ) * p := by
      exact_mod_cast nq.trans (Nat.mul_le_mul_right p (Nat.mul_le_mul_left 2 (factor p q)))
    have pl := Real.log_nonneg (show 1 ≤ (p : ℝ) by exact_mod_cast q.one_le)
    apply (le_of_mul_le_mul_right (a := (p : ℝ)) _ pp)
    calc
      _ = (L : ℝ) * Real.log p := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right cap pl
      _ = _ := by ring
  have factlog : Real.log (F : ℝ) ≤ L * Real.log L := by
    have h := Real.log_le_log (show 0 < (F : ℝ) by exact_mod_cast Nat.factorial_pos L)
      (show (F : ℝ) ≤ (L : ℝ)^L by exact_mod_cast Nat.factorial_le_pow L)
    simpa only [Real.log_pow] using h
  apply le_of_mul_le_mul_left (a := (L : ℝ)) _ (by exact_mod_cast hL)
  calc
    _ = ∑ p ∈ P, (L : ℝ) * (Real.log p / p) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ P, 2 * ((F.factorization p : ℝ) * Real.log p) := sum_le_sum compare
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ 2 * (L * Real.log L) := by linarith only [mass, factlog]
    _ = _ := by ring

/-- A lower factor for the proportion left on each norm fibre after one sign is excluded. -/
def atom (p : ℕ) : ℝ := 1 - 2 / ((p : ℝ) - 1)

private theorem log_atom {p : ℕ} (big : 7 ≤ p) :
    0 < atom p ∧ -(8 / (p : ℝ)) ≤ Real.log (atom p) := by
  have hp : (7 : ℝ) ≤ p := by exact_mod_cast big
  have h1 : 0 < (p : ℝ) - 1 := by linarith
  have h3 : 0 < (p : ℝ) - 3 := by linarith
  have e : atom p = ((p : ℝ) - 3) / ((p : ℝ) - 1) := by unfold atom; field_simp; ring
  have pos : 0 < atom p := e ▸ div_pos h3 h1
  refine ⟨pos, le_trans ?_ (Real.one_sub_inv_le_log_of_pos pos)⟩
  rw [e, inv_div]
  field_simp [show (0:ℝ) < p by linarith, h3]
  linarith

/-- The loss for all k positions is at most a square root of the cutoff.
The base can be chosen once, independently of the last obstruction prime. -/
theorem product_cost {K L k : ℕ} (big : 7 ≤ K) (logK : 416 ≤ Real.log K)
    (kl : K ≤ L) (hk : k ≤ 13) :
    1 / Real.sqrt (L : ℝ) ≤ ∏ p ∈ places K L, (atom p)^k := by
  let P := places K L
  have Lp : 0 < L := by omega
  have LP : 0 < (L : ℝ) := by exact_mod_cast Lp
  have kp : (k : ℝ) ≤ 13 := by exact_mod_cast hk
  have deg (p : ℕ) (hp : p ∈ P) : -((Real.log p / p) / 4) ≤ Real.log ((atom p)^k) := by
    obtain ⟨above,_,prime⟩ := mem_places.mp hp
    have pp : (0 : ℝ) < p := by exact_mod_cast prime.pos
    have logs : (416:ℝ) ≤ Real.log p := logK.trans (Real.log_le_log
      (show 0 < (K : ℝ) by exact_mod_cast (by omega : 0 < K))
      (by exact_mod_cast above.le))
    obtain ⟨_,loc⟩ := log_atom (show 7 ≤ p by omega)
    rw [Real.log_pow]
    apply le_trans _ (mul_le_mul_of_nonneg_left loc (Nat.cast_nonneg k))
    field_simp [pp]
    linarith
  have all := factorial_prime_sum Lp P fun p hp => ⟨(mem_places.mp hp).2.2,(mem_places.mp hp).2.1⟩
  have pr (p : ℕ) (hp : p ∈ P) : 0 < (atom p)^k :=
    pow_pos (log_atom (show 7 ≤ p by have := (mem_places.mp hp).1; omega)).1 _
  apply (Real.log_le_log_iff (by positivity) (Finset.prod_pos pr)).mp
  rw [Real.log_div one_ne_zero (Real.sqrt_pos.2 LP).ne', Real.log_one,
    Real.log_sqrt LP.le, Real.log_prod (fun p hp => (pr p hp).ne')]
  change 0 - Real.log L / 2 ≤ ∑ p ∈ P, Real.log ((atom p)^k)
  apply le_trans _ (sum_le_sum deg)
  rw [Finset.sum_neg_distrib, ←Finset.sum_div]
  linarith

end
end Sun28.FinitePattern
#print axioms Sun28.FinitePattern.factorial_prime_sum
#print axioms Sun28.FinitePattern.product_cost
