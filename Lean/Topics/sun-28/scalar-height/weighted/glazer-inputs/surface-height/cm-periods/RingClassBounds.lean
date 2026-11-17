import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
namespace ZInQBlueprint.CMPeriods
open Finset
/-- Euler's product for the conductor, including the exceptional unit indices at -3 and -4. -/
theorem totient_le_class_index {f h hK u : ℕ} (hf : 0 < f) (hKp : 0 < hK)
    (c : ℕ → ℕ) (localLower : ∀ p ∈ f.primeFactors, p - 1 ≤ c p)
    (formula : u*h = hK * ∏ p ∈ f.primeFactors, p^(f.factorization p-1)*c p) :
    f.totient ≤ u*h := by
  rw [Nat.totient_eq_prod_factorization hf.ne', Finsupp.prod] 
  change ∏ p ∈ f.primeFactors, p ^ (f.factorization p - 1) * (p-1) ≤ _
  rw [formula]
  apply le_trans (Finset.prod_le_prod (fun p hp => Nat.mul_le_mul_left _ (localLower p hp)))
  exact Nat.le_mul_of_pos_left _ hKp
private def ratio (p : ℕ) : ℚ := (p : ℚ) / ((p-1 : ℕ) : ℚ)
private theorem ratio_one {p : ℕ} (hp : Nat.Prime p) : 1 ≤ ratio p := by
  have h := hp.one_lt
  unfold ratio
  have pos : (0 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (show 0 < p-1 by omega)
  apply (le_div_iff₀ pos).2
  simp only [one_mul]
  exact_mod_cast Nat.sub_le p 1
/-- A uniform conductor estimate for ring class number at most sixteen. -/
theorem conductor_le {f : ℕ} (hf : 0 < f) (h : f.totient ≤ 48) : f ≤ 384 := by
  let S := (Finset.range 50).filter Nat.Prime
  have subset : f.primeFactors ⊆ S := by
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    have d := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.totient_prime pr] at d
    have l := Nat.le_of_dvd (Nat.totient_pos.mpr hf) d
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), pr⟩
  have padded : ∏ p ∈ f.primeFactors, ratio p ≤ ∏ p ∈ S, ratio p := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ subset (fun p hp => zero_le_one.trans (ratio_one (Nat.prime_of_mem_primeFactors hp)))
    intro p hp _
    exact ratio_one (Finset.mem_filter.mp hp).2
  have list : S = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47} := by decide
  have small : ∏ p ∈ S, ratio p ≤ 8 := by rw [list]; norm_num [ratio, Finset.prod_insert]
  have prodpos : 0 < ∏ p ∈ f.primeFactors, ((p-1 : ℕ) : ℚ) := by
    apply Finset.prod_pos
    intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    exact_mod_cast (show 0 < p-1 by omega)
  have e := Nat.totient_mul_prod_primeFactors f
  have e' : (f.totient : ℚ)*(∏ p ∈ f.primeFactors, (p:ℚ)) =
      (f:ℚ)*(∏ p ∈ f.primeFactors, ((p-1 : ℕ):ℚ)) := by simpa only [Nat.cast_mul,Nat.cast_prod] using congrArg (Nat.cast : ℕ → ℚ) e
  have eq : (f:ℚ) = f.totient * ∏ p ∈ f.primeFactors, ratio p := by
    simp only [ratio, Finset.prod_div_distrib, ← mul_div_assoc]
    exact (eq_div_iff prodpos.ne').mpr e'.symm
  have bound : (f:ℚ) ≤ 48*8 := calc
    _ = _ := eq
    _ ≤ _ := mul_le_mul (by exact_mod_cast h) (padded.trans small)
      (Finset.prod_nonneg fun p hp => (zero_le_one.trans (ratio_one (Nat.prime_of_mem_primeFactors hp)))) (by norm_num)
  exact_mod_cast bound
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.conductor_le
#print axioms ZInQBlueprint.CMPeriods.totient_le_class_index
