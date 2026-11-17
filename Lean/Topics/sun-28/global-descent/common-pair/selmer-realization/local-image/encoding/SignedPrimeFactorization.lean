import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int

namespace Sun28.FixedLocalRows.WordEncoding

/-- Positive generators, in the literal order of the published word table. -/
def primes : List ℕ := [2, 3, 11, 109, 439, 283, 1433, 4373, 14557]

/-- Membership in the fixed support is tested on the absolute value. -/
def Supported (z : ℤ) : Prop := z.natAbs.primeFactors ⊆ primes.toFinset

theorem supported_of_prime_divisors {z : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ z → p ∈ primes) : Supported z := by
  intro p hp
  obtain ⟨prime, divides, _⟩ := Nat.mem_primeFactors.mp hp
  exact List.mem_toFinset.mpr (h p prime (Int.natCast_dvd.mpr divides))

def signedProduct (z : ℤ) : ℤ :=
  (if decide (z < 0) then -1 else 1) *
    (primes.map fun p => if decide (p ∈ z.natAbs.primeFactors) then (p : ℤ) else 1).prod

/-- The sign and the distinct prime divisors recover a signed squarefree integer.
This includes both units. -/
theorem signedProduct_eq {z : ℤ} (hz : Squarefree z) (hs : Supported z) :
    signedProduct z = z := by
  have hn : primes.Nodup := by decide
  have hfilter : primes.toFinset.filter (· ∈ z.natAbs.primeFactors) = z.natAbs.primeFactors := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hp => ⟨hs hp, hp⟩⟩
  have hf : (∏ p ∈ z.natAbs.primeFactors, (p : ℤ)) = (z.natAbs : ℤ) := by
    rw [← Nat.cast_prod]
    exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hz))
  unfold signedProduct
  simp only [decide_eq_true_eq]
  rw [← List.prod_toFinset _ hn, ← Finset.prod_filter, hfilter, hf, Int.natCast_natAbs]
  split
  next h => simp [abs_of_neg h]
  next h => simp [abs_of_nonneg (le_of_not_gt h)]

end Sun28.FixedLocalRows.WordEncoding

#print axioms Sun28.FixedLocalRows.WordEncoding.supported_of_prime_divisors
#print axioms Sun28.FixedLocalRows.WordEncoding.signedProduct_eq
