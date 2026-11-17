import FixedClass

namespace Sun28.PrimeTransfer
open Finset Filter Topology Sun28.ContactFactors Sun28.FinitePattern
open scoped Classical
noncomputable section

/-- The polylogarithmic conclusion of Tao–Ziegler's published Theorem 6, weakened
to m^4 ≤ n and stated for the one oriented class. Chebotarev supplies its density. -/
def NarrowClassRecurrence : Prop :=
  ∀ (K : ℕ) (c : Finset ℤ) (Y : ℕ), ∃ u > Y, ∃ m : ℕ, 0 < m ∧ m^4 ≤ u ∧
    ∀ h∈c, ∃ p:ℕ, (p:ℤ)=(u:ℤ)+h*(m:ℤ)^2 ∧ oneClass K p

/-- Positive primes past any bound at arbitrarily large rational slopes, with
the prescribed divisibility of the square step, at one fixed cutoff. -/
theorem guarded_prime_pattern (narrow : NarrowClassRecurrence) (A : Fin 3→ℚ)
    (K Y H d : ℕ) (dp : 0 < d) :
    ∃ u w : ℕ, 0 < w ∧ d∣w ∧ H*((dilation A)*w)^2 < u ∧
      ∀ i : ↥(shifts A), ∃ p > Y, (p:ℤ)=form A (u,w) i ∧ commonPrime K K p := by
  let C:=(shifts A).image fun r => offset (dilation A) r*(d:ℤ)^2
  let B:=C.sup Int.natAbs+H*((dilation A)*d)^2+Y+1
  have bp : 0 < B := by dsimp [B];omega
  obtain ⟨u,large,m,mp,quartic,seq⟩ := narrow K C (4*B^2)
  have safe : B*m^2+B < u := by
    by_cases sm : m^2 ≤ B
    · have v:=Nat.mul_le_mul_left B sm
      nlinarith only [large,v,bp,Nat.le_mul_self B]
    · have v : B+1 ≤ m^2 := by omega
      have p := Nat.mul_le_mul_right (m^2) v
      have more : 2 ≤ m^2 := by omega
      nlinarith only [quartic,p,more,v]
  refine ⟨u,d*m,Nat.mul_pos dp mp,dvd_mul_right ..,?_,?_⟩
  · have le : H*((dilation A)*d)^2 ≤ B := by dsimp [B]; omega
    nlinarith only [safe,Nat.mul_le_mul_right (m^2) le]
  · intro i
    let h:=offset (dilation A) i*(d:ℤ)^2
    have mem : h∈C := mem_image_of_mem _ i.property
    have size : h.natAbs ≤ B := (Finset.le_sup (f:=Int.natAbs) mem).trans (by dsimp [B];omega)
    obtain ⟨p,eq,ok⟩:=seq h mem
    have s : -(B:ℤ) ≤ h := by omega
    have z : (B:ℤ)*(m:ℤ)^2+B < (u:ℤ) := by exact_mod_cast safe
    have low : (Y:ℤ) < p := by
      have yB : Y ≤ B := by dsimp [B];omega
      have v := mul_le_mul_of_nonneg_right s (sq_nonneg (m:ℤ))
      nlinarith only [z,eq,v,show (Y:ℤ) ≤ B by exact_mod_cast yB]
    refine ⟨p,by exact_mod_cast low,?_,fixed_class_common _ _ ok⟩
    rw [eq]
    unfold form
    dsimp only [h,Prod.fst,Prod.snd]
    push_cast
    ring

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.guarded_prime_pattern
