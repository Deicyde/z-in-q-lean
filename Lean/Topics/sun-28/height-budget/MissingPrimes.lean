import BudgetSector

namespace Sun28.HeightBudget
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightFibres Sun28.HeightFibres.Sharp
  Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Sun28.FiveMarkTriples
noncomputable section

/-- Every row of a possible counterexample contains a prime invisible to the
global odd detector. In particular its order in this row is positive and even. -/
theorem missing_even_prime {A B : ℤ} (i : Fin 5)
    (high : heightRadical A B<primeProduct (repeatedPrimes i A B)) :
    ∃ p : ℕ, p.Prime ∧ 76176<p ∧ p^2∣(oldForm i A B).natAbs ∧
      p∉oddSupport A B ∧ Even (padicValInt p (oldForm i A B)) := by
  classical
  have miss : ¬repeatedPrimes i A B⊆support A B := by
    intro sub
    exact high.not_ge ((support_mono sub (fun _ m=>support_primes m)).trans_eq (product_support A B))
  obtain ⟨p,mem,out⟩:=Finset.not_subset.mp miss
  obtain ⟨m,sq⟩:=Finset.mem_filter.mp mem
  have pr:=Nat.prime_of_mem_primeFactors m
  have ncut : p∉oldCutoff:=fun x=>out (Finset.mem_union_left _ x)
  have nodd : p∉oddSupport A B:=fun x=>out (Finset.mem_union_right _ x)
  have big : 76176<p:=by
    by_contra! lo
    exact ncut (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),pr⟩)
  refine ⟨p,pr,big,sq,nodd,?_⟩
  apply Nat.not_odd_iff_even.mp
  intro odd
  have pos : 0<padicValInt p (oldForm i A B):=by obtain ⟨q,e⟩:=odd;omega
  exact nodd (mem_oldContactPrimes.mpr ⟨pr,ncut,i,pos,odd⟩)

theorem distinct_hidden_primes {A B : ℤ} (cop : Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (high:∀ i,heightRadical A B<primeProduct (repeatedPrimes i A B)) :
    ∃ p : Fin 5→ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ 76176<p i ∧
      (p i)^2∣(oldForm i A B).natAbs ∧ p i∉oddSupport A B ∧
      Even (padicValInt (p i) (oldForm i A B)) := by
  choose p prime large sq outside order using fun i=>missing_even_prime i (high i)
  refine ⟨p,?_,fun i=>⟨prime i,large i,sq i,outside i,order i⟩⟩
  intro i j eq
  have mem (k):p k∈formPrimes k A B:=Nat.mem_primeFactors.mpr ⟨prime k,
    (dvd_pow_self _ two_ne_zero).trans (sq k),Int.natAbs_ne_zero.mpr (off k)⟩
  have away : p i∉core:=by
    intro h
    have low := (Finset.mem_filter.mp (core_subset h)).1
    have lt:=Finset.mem_range.mp low
    have hi:=large i
    omega
  exact unique_mark cop away (mem i) (eq ▸ mem j)

end
end Sun28.HeightBudget
#print axioms Sun28.HeightBudget.missing_even_prime
#print axioms Sun28.HeightBudget.distinct_hidden_primes

