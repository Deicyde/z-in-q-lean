import RemainingRank
import HomogeneousQuartics
import SignedImages
import QuarticBlocks

namespace Sun28.ConicRemaining
open Sun28.ScalarRankZero Sun28.FactorHeights
open Sun28.ScalarDepth Sun28.ConicArithmetic Sun28.ScalarHeight Sun28.Ordinary
open private products from SignedImages
open private blocked exclude negative_quartic from QuarticBlocks
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

/-- Three primitive homogeneous quartics left by the two-isogeny calculation. -/
def ThreeQuarticExclusions : Prop :=
  (¬ represented 735 134288 2) ∧ (¬ represented 735 134288 77) ∧
    (¬ represented 735 134288 154)

private theorem switch (A B e f c:ℤ) (cn:c≠0) (h:B/e=f*c^2) (h':B/f=e*c^2)
    (rep:represented A B e) : represented A B f := by
  apply (represented_iff_projective A B f).mpr
  obtain ⟨u,v,z,nz,eq⟩:=(represented_iff_projective A B e).mp rep
  refine ⟨c*v,u,c*z,?_,?_⟩
  · rcases nz with un|vn
    · exact Or.inr un
    · exact Or.inl (mul_ne_zero (by exact_mod_cast cn) vn)
  · rw [h] at eq
    rw [h']
    push_cast at eq ⊢
    unfold quartic at eq ⊢
    linear_combination (c:ℚ)^2*eq

private theorem both_supports :
  signedDivisors 134288={-16786,-8393,-2398,-1526,-1199,-763,-218,-154,-109,-77,-22,-14,-11,-7,-2,-1,1,2,7,11,14,22,77,109,154,218,763,1199,1526,2398,8393,16786} ∧ signedDivisors 3073={-3073,-439,-7,-1,1,7,439,3073} := by
  have h:(134288:ℤ).natAbs.primeFactorsList.eraseDups=[2,7,11,109] := by
    change (134288:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  have g:(3073:ℤ).natAbs.primeFactorsList.eraseDups=[7,439] := by
    change (3073:ℕ).primeFactorsList.eraseDups=_
    simp only [Nat.primeFactorsList_ofNat];decide
  simp only [signedDivisors,h,g,products]
  decide

private theorem direct_local : images 735 134288 ⊆ ({1,2,77,109,154,218,8393,16786}:Finset ℤ) := by
  classical
  intro e he
  obtain ⟨m,hp⟩:=Finset.mem_filter.mp he
  rw [both_supports.1] at m
  simp only [Finset.mem_insert,Finset.mem_singleton] at m
  rcases m with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · decide
  · decide
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · decide
  · decide
  · decide
  · decide
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=64) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=2) (n:=32) (by decide) (by decide) (by decide) hp)
  · decide
  · decide

private theorem dual_local : images (-1470) 3073 ⊆ ({1,3073}:Finset ℤ) := by
  classical
  intro e he
  obtain ⟨m,hp⟩:=Finset.mem_filter.mp he
  rw [both_supports.2] at m
  simp only [Finset.mem_insert,Finset.mem_singleton] at m
  rcases m with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact False.elim (negative_quartic (by decide) (by decide) (by decide) hp)
  · exact False.elim (negative_quartic (by decide) (by decide) (by decide) hp)
  · exact False.elim (negative_quartic (by decide) (by decide) (by decide) hp)
  · exact False.elim (negative_quartic (by decide) (by decide) (by decide) hp)
  · decide
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · exact False.elim (exclude (p:=7) (n:=49) (by decide) (by decide) (by decide) hp)
  · decide

/-- Kernel-checked upper bounds for both actual rational descent images. -/
theorem small_images (g:ThreeQuarticExclusions) :
    images 735 134288 ⊆ ({1,8393}:Finset ℤ) ∧ images (-1470) 3073 ⊆ ({1,3073}:Finset ℤ) := by
  classical
  refine ⟨?_,dual_local⟩
  intro e he
  have mem:=direct_local he
  have hh:represented 735 134288 e := (Finset.mem_filter.mp he).2
  simp only [Finset.mem_insert,Finset.mem_singleton] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · exact False.elim (g.1 hh)
  · exact False.elim (g.2.1 hh)
  · exact False.elim (g.2.1 (switch _ _ _ _ 4 (by decide) (by decide) (by decide) hh))
  · exact False.elim (g.2.2 hh)
  · exact False.elim (g.2.2 (switch _ _ _ _ 2 (by decide) (by decide) (by decide) hh))
  · decide
  · exact False.elim (g.1 (switch _ _ _ _ 2 (by decide) (by decide) (by decide) hh))

theorem short_rank_of_three (descent:TwoIsogenyRank) (g:ThreeQuarticExclusions) : ShortRankZero := by
  obtain ⟨r,hr,he⟩:=descent 735 134288 (by decide) (by decide)
  have q:(images 735 134288).card*(images (-1470) 3073).card≤4 :=
    (Nat.mul_le_mul (Finset.card_le_card (small_images g).1)
      (Finset.card_le_card (small_images g).2)).trans (by decide)
  change 2^(r+2)=(images 735 134288).card*(images (-1470) 3073).card at he
  have rz:r=0:=by
    by_contra! pos
    have eight:(2:ℕ)^3≤2^(r+2):=Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simpa [ShortRankZero,rz] using hr

theorem scalar_of_three_quartics (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (sel:PositiveSelmerSelection) (g:ThreeQuarticExclusions) (est:NegativeExceptionalScalarBound) :
    ScalarBound := scalar_of_short_rank descent reduction sel (short_rank_of_three descent g) est

end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.small_images
#print axioms Sun28.ConicRemaining.short_rank_of_three
#print axioms Sun28.ConicRemaining.scalar_of_three_quartics
