import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Divisors

/-! Expanding a weight in the number of distinct primes by squarefree divisors. -/
namespace ZInQBlueprint.TwistCount
open Finset
open scoped Classical

/-- The number of distinct prime divisors, including none for 1. -/
def omega (m : ℕ) := m.primeFactors.card

theorem add_weight_le_divisors (a m : ℕ) (hm : m≠0) :
    (a+1)^omega m ≤ ∑ d ∈ m.divisors, a^omega d := by
  let S:=m.primeFactors
  let f (s : Finset ℕ) := ∏ p ∈ s,p
  have key {s : Finset ℕ} (h:s∈S.powerset) : (f s).primeFactors=s :=
    Nat.primeFactors_prod (fun p hp=>Nat.prime_of_mem_primeFactors ((mem_powerset.mp h) hp))
  have member {s : Finset ℕ} (h:s∈S.powerset) : f s∈m.divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨?_,hm⟩
    exact (Finset.prod_dvd_prod_of_subset _ _ (fun p:ℕ=>p) (mem_powerset.mp h)).trans m.prod_primeFactors_dvd
  have injective : Set.InjOn f (S.powerset:Set (Finset ℕ)) := by
    intro s hs t ht eq
    exact (key hs).symm.trans ((congrArg Nat.primeFactors eq).trans (key ht))
  calc
    _ = ∏ _p ∈ S, (a+1) := by simp [S,omega]
    _ = ∑ s ∈ S.powerset, ∏ _p ∈ s,a := prod_add_one _
    _ = ∑ d ∈ S.powerset.image f, a^omega d := by
      rw [sum_image injective]
      apply sum_congr rfl
      intro s hs
      simp only [prod_const,omega,key hs]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
      intro d hd; obtain ⟨s,hs,rfl⟩:=mem_image.mp hd;exact member hs) (by simp)

end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.add_weight_le_divisors
