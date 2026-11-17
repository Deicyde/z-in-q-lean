import TorsionPermutations
import GoodMarked

namespace Sun28.LocalOrbit
open Sun28.SelmerRealization Sun28.MarkedDescent

def eight : Finset (ℤ×ℤ) :=
  {(1,1),(526361,1),((Sun28.SelmerRealization.multiplier:ℤ),1),((n:ℤ),1),
    (3,-(n:ℤ)),(3*526361,-(n:ℤ)),(3*(Sun28.SelmerRealization.multiplier:ℤ),-(n:ℤ)),(3*(n:ℤ),-(n:ℤ))}

theorem eight_card : eight.card=8 := by decide

private theorem identity {K : Type*} [Field K] [CharZero K] (l : ℕ) : Cover K l 1 1 := by
  refine ⟨1,1,1,0,Or.inl one_ne_zero,?_,?_⟩ <;> push_cast <;> ring

private theorem all_at {K : Type*} [Field K] [CharZero K] (M : Cover K n 526361 1) :
    ∀ ab ∈ eight, Cover K n ab.1 ab.2 := by
  have l : n≠0 := by decide
  have I := identity (K:=K) n
  have C := exchange (c:=(Sun28.SelmerRealization.multiplier:ℤ)) (by decide) (by decide) l M
  have D := exchange (c:=(n:ℤ)) (by decide) (by decide) l I
  have I' := signed_translate (by decide : (1:ℤ)≠0) l I
  have M' := signed_translate (by decide : (526361:ℤ)≠0) l M
  have C' := signed_translate (by decide : (Sun28.SelmerRealization.multiplier:ℤ)≠0) l C
  have D' := signed_translate (by decide : (n:ℤ)≠0) l D
  intro ab member
  simp only [eight,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact I
  · exact M
  · exact C
  · exact D
  · simpa only [mul_one] using I'
  · exact M'
  · exact C'
  · exact D'

private theorem compatible_divisors : Squarefree (3*(n:ℤ)) := by
  have s : Squarefree (3*n) := Nat.squarefree_mul_iff.mpr
    ⟨by decide,(by norm_num : Nat.Prime 3).squarefree,n_shape.2.1⟩
  exact_mod_cast Int.squarefree_natCast.mpr s

/-- Eight distinct ordered signed squarefree pairs lie on the actual projective
cover over every completion. -/
theorem eight_subset : (eight : Set (ℤ×ℤ)) ⊆ localClasses n := by
  intro ab h
  have divs : ∀ q ∈ eight, q.1∣3*(n:ℤ) ∧ q.2∣3*(n:ℤ) := by decide
  obtain ⟨d1,d2⟩:=divs ab h
  have M:=fixed_membership
  exact ⟨compatible_divisors.squarefree_of_dvd d1,compatible_divisors.squarefree_of_dvd d2,
    all_at M.2.2.1 ab h,fun p _=>all_at (M.2.2.2 p) ab h⟩

theorem eight_le_encard : 8 ≤ (localClasses n).encard := by
  have h := Set.encard_mono eight_subset
  rw [Set.encard_coe_eq_coe_finsetCard,eight_card] at h
  exact h

end Sun28.LocalOrbit
#print axioms Sun28.LocalOrbit.eight_card
#print axioms Sun28.LocalOrbit.eight_subset
#print axioms Sun28.LocalOrbit.eight_le_encard
