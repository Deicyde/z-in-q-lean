import Necessity
import LeastChart

/-! The quartic orbits force the remaining row to carry all odd contacts. -/
namespace Sun28.FourContact
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors
noncomputable section

def rowSupport (i : Fin 5) (A B : ℤ) : Finset ℕ :=
  ((oldForm i A B).natAbs.primeFactors.filter (fun p => Odd (padicValInt p (oldForm i A B)))) \ oldCutoff

theorem contacts_split (i : Fin 5) (A B : ℤ) :
    oldContactPrimes oldCutoff A B = rowSupport i A B ∪ retainedSupport i A B := by
  ext p
  simp only [oldContactPrimes,rowSupport,retainedSupport,Finset.mem_sdiff,Finset.mem_union,
    Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_erase,Finset.mem_filter]
  constructor
  · rintro ⟨⟨j,f,o⟩,out⟩
    by_cases h : j=i
    · subst j; exact Or.inl ⟨⟨f,o⟩,out⟩
    · exact Or.inr ⟨⟨j,⟨h,trivial⟩,f,o⟩,out⟩
  · rintro (h|h)
    · exact ⟨⟨i,h.1.1,h.1.2⟩,h.2⟩
    · obtain ⟨⟨j,_,f,o⟩,out⟩:=h
      exact ⟨⟨j,f,o⟩,out⟩

theorem only_omitted_row (i : Fin 5) (n : ℕ)
    (off : ∀ j,oldForm j (slope i n).num (slope i n).den≠0) :
    oddSupport (slope i n).num (slope i n).den =
      rowSupport i (slope i n).num (slope i n).den := by
  rw [oddSupport,contacts_split i,retainedSupport_empty i n off,Finset.union_empty]

/-- The public estimate would force unbounded odd radical in the omitted form
alone, while the other four are even outside the original exceptional set. -/
theorem omitted_row_unbounded (estimate : OriginalFiveHeight glazerConstant24 oldCutoff)
    (i : Fin 5) (R : ℕ) :
    ∃ A B : ℤ, Int.gcd A B=1 ∧ (∀ j,oldForm j A B≠0) ∧
      retainedSupport i A B=∅ ∧ R<primeProduct (rowSupport i A B) := by
  obtain ⟨A,B,cop,off,empty,high⟩:=four_contacts_insufficient i (glazerConstant24*(R:ℝ)^24)
  refine ⟨A,B,cop,off,empty,?_⟩
  have h:=estimate A B cop off
  rw [contacts_split i,empty,Finset.union_empty] at h
  by_contra! small
  have er : (∏ p∈rowSupport i A B,(p:ℝ))≤(R:ℝ) := by
    rw [←Nat.cast_prod];exact_mod_cast small
  have nonneg : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  exact (not_le_of_gt high) (h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) er _) nonneg))

end
end Sun28.FourContact
#print axioms Sun28.FourContact.contacts_split
#print axioms Sun28.FourContact.only_omitted_row
#print axioms Sun28.FourContact.omitted_row_unbounded
