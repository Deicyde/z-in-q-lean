import QuarticBlocks
import Mathlib.Tactic.Simproc.Factors

namespace Sun28.ScalarRankZero
open Sun28.FactorHeights
set_option maxRecDepth 32000
set_option maxHeartbeats 1500000

private def products : List ℕ → List ℤ
  | [] => [1,-1]
  | p::ps =>
    let rest:=products ps
    rest ++ rest.map (fun e=> (p:ℤ)*e)

/-- Select each prime divisor once or zero times and either sign. -/
def signedDivisors (B:ℤ) : Finset ℤ :=
  (products B.natAbs.primeFactorsList.eraseDups).toFinset

/-- Rationally soluble primitive quartics on the signed squarefree divisors of B. -/
noncomputable def images (A B:ℤ) : Finset ℤ :=
  by classical exact (signedDivisors B).filter (represented A B)

theorem supports :
    signedDivisors 24={1,-1,2,-2,3,-3,6,-6} ∧
    signedDivisors 4={1,-1,2,-2} ∧
    signedDivisors 28096={1,-1,2,-2,439,-439,878,-878} ∧
    signedDivisors 140625={1,-1,3,-3,5,-5,15,-15} := by
  have h1 : (24:ℤ).natAbs.primeFactorsList.eraseDups=[2,3] := by
    change (24:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  have h2 : (4:ℤ).natAbs.primeFactorsList.eraseDups=[2] := by
    change (4:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  have h3 : (28096:ℤ).natAbs.primeFactorsList.eraseDups=[2,439] := by
    change (28096:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  have h4 : (140625:ℤ).natAbs.primeFactorsList.eraseDups=[3,5] := by
    change (140625:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  simp only [signedDivisors,h1,h2,h3,h4,products]
  decide

theorem direct_images :
    images 10 24⊆({1,-1,6,-6}:Finset ℤ) ∧
    images 503 28096⊆({1,-1,439,-439}:Finset ℤ) := by
  classical
  obtain ⟨a,b,c,d,e,f,g,h⟩:=direct_exclusions
  obtain ⟨s,_,t,_⟩:=supports
  constructor
  · intro i hi
    obtain ⟨m,n⟩:=Finset.mem_filter.mp hi
    rw [s] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m ⊢
    rcases m with v|v|v|v|v|v|v|v <;> subst i <;> tauto
  · intro i hi
    obtain ⟨m,n⟩:=Finset.mem_filter.mp hi
    rw [t] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m ⊢
    rcases m with v|v|v|v|v|v|v|v <;> subst i <;> tauto

theorem dual_images :
    images (-20) 4⊆({1}:Finset ℤ) ∧ images (-1006) 140625⊆({1}:Finset ℤ) := by
  classical
  obtain ⟨a,b,c,d,e,f⟩:=dual_exclusions
  obtain ⟨_,s,_,t⟩:=supports
  constructor
  · intro i hi
    obtain ⟨m,n⟩:=Finset.mem_filter.mp hi
    rw [s] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m ⊢
    rcases m with v|v|v|v <;> subst i
    · rfl
    · exact False.elim (a _ (by decide) (by decide) n)
    · exact False.elim (b n)
    · exact False.elim (a _ (by decide) (by decide) n)
  · intro i hi
    obtain ⟨m,n⟩:=Finset.mem_filter.mp hi
    rw [t] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m ⊢
    rcases m with v|v|v|v|v|v|v|v <;> subst i
    · rfl
    · exact False.elim (c _ (by decide) (by decide) n)
    · exact False.elim (d n)
    · exact False.elim (c _ (by decide) (by decide) n)
    · exact False.elim (e n)
    · exact False.elim (c _ (by decide) (by decide) n)
    · exact False.elim (f n)
    · exact False.elim (c _ (by decide) (by decide) n)

theorem image_products :
    (images 10 24).card*(images (-20) 4).card≤4 ∧
    (images 503 28096).card*(images (-1006) 140625).card≤4 := by
  exact ⟨(Nat.mul_le_mul (Finset.card_le_card direct_images.1) (Finset.card_le_card dual_images.1)).trans
      (by decide), (Nat.mul_le_mul (Finset.card_le_card direct_images.2) (Finset.card_le_card dual_images.2)).trans
      (by decide)⟩

end Sun28.ScalarRankZero
#print axioms Sun28.ScalarRankZero.supports
#print axioms Sun28.ScalarRankZero.direct_images
#print axioms Sun28.ScalarRankZero.dual_images
#print axioms Sun28.ScalarRankZero.image_products
