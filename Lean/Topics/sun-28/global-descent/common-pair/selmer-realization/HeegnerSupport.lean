import MandatorySupport

namespace Sun28.SelmerRealization
open Sun28.PairedClasses Sun28.PreparedPoles

/-- Residue condition on each prime in He--Hu--Tian, Theorem 1.1. -/
def TilingPrime (p : ℕ) : Prop := p % 24 = 1 ∨ p % 24 = 23

private theorem prod_signed_residues (s : Finset ℕ) (h : ∀ p ∈ s, TilingPrime p) :
    TilingPrime (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TilingPrime]
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hx' := h x (Finset.mem_insert_self _ _)
    have hs := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    unfold TilingPrime at *
    rcases hx' with x1|x23 <;> rcases hs with s1|s23 <;>
      rw [Nat.mul_mod] <;> simp_all

/-- Every admissible marked twist violates the published prime support
criterion, regardless of the auxiliary primes added to its parameter. -/
theorem unavoidable_prime {b l : ℕ} (sf : Squarefree b) (b6 : b.Coprime 6)
    (b24 : b % 24 = 17) (lp : 0 < l) (pt : TwistPoint b l) :
    ∃ p : ℕ, p.Prime ∧ p ∣ b ∧ p ∣ l ∧ ¬ TilingPrime p := by
  have bl := beta_dvd_of_twist sf b6 lp pt
  by_contra! h
  have allgood : ∀ p ∈ b.primeFactors, TilingPrime p := by
    intro p hp
    obtain ⟨pp,db,_⟩ := Nat.mem_primeFactors.mp hp
    exact h p pp db (dvd_trans db bl)
  have pr := prod_signed_residues _ allgood
  rw [Nat.prod_primeFactors_of_squarefree sf] at pr
  rcases pr with h1|h23 <;> omega

end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.unavoidable_prime
