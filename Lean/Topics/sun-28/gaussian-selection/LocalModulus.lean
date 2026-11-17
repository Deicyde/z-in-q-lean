import GaussianHeader
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Squarefree

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic

def avoidPrimes (T : Finset ℕ) (κ : ℕ) : Finset ℕ :=
  (T∪κ.primeFactors).filter fun p=>p≠2 ∧ p≠7

def avoidModulus (T : Finset ℕ) (κ : ℕ) : ℕ := ∏ p∈avoidPrimes T κ,p

theorem avoid_modulus_spec (T : Finset ℕ) (κ : ℕ) (hp : ∀ p∈T,p.Prime) :
    0<avoidModulus T κ ∧ Odd (avoidModulus T κ) ∧ squarefree (avoidModulus T κ) ∧
    ¬7∣avoidModulus T κ ∧ ∀ p∈T∪κ.primeFactors,p≠2 → p∣7*avoidModulus T κ := by
  let S:=avoidPrimes T κ
  have mem {p} : p∈S ↔ (p∈T ∨ p∈κ.primeFactors) ∧ p≠2 ∧ p≠7 := by simp [S,avoidPrimes]
  have primes (p) (h : p∈S) : p.Prime :=
    (mem.mp h).1.elim (hp p) Nat.prime_of_mem_primeFactors
  have positive : 0<∏ p∈S,p := Finset.prod_pos (fun p h=>(primes p h).pos)
  have sht (p : ℕ) (pp : p.Prime) (absent : p∉S) : ¬p∣∏ l∈S,l := by
    intro d
    obtain ⟨l,hl,pl⟩:=(Nat.prime_iff.mp pp |>.dvd_finsetProd_iff id).mp d
    exact absent (((Nat.prime_dvd_prime_iff_eq pp (primes l hl)).mp pl) ▸ hl)
  have no2:=sht 2 Nat.prime_two (by simp [mem])
  have no7:=sht 7 (by decide) (by simp [mem])
  have square : Squarefree (∏ p∈S,p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp' l hl e=>Nat.coprime_iff_isRelPrime.mp ((primes p hp').coprime_iff_not_dvd.mpr
        (fun d=>e ((Nat.prime_dvd_prime_iff_eq (primes p hp') (primes l hl)).mp d))))
      (fun p hp'=>(Nat.prime_iff.mp (primes p hp')).irreducible.squarefree)
  refine ⟨positive,?_,?_,no7,?_⟩
  · change Odd (∏ p∈S,p)
    rw [Nat.odd_iff]
    omega
  · simpa only [squarefree,pow_two,S,avoidModulus] using Nat.squarefree_iff_prime_squarefree.mp square
  · intro p h odd
    by_cases seven : p=7
    · exact seven ▸ dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id
        (mem.mpr ⟨Finset.mem_union.mp h,odd,seven⟩)) _

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.avoid_modulus_spec
