import TYZFactorizations

/-! Unordered factorizations in the usual multiset sense. -/
open Finset

namespace ZInQBlueprint.TYZ

theorem nodup_of_squarefree_product (s : Multiset ℕ) (hs : Squarefree s.prod)
    (hlt : ∀ a ∈ s, 1 < a) : s.Nodup := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have hprod : Squarefree (a*s.prod) := by simpa using hs
    have has : 1 < a := hlt a (by simp)
    refine Multiset.nodup_cons.mpr ⟨?_, ih (Squarefree.squarefree_of_dvd (dvd_mul_left s.prod a) hprod)
      (fun b hb => hlt b (Multiset.mem_cons_of_mem hb))⟩
    intro ha
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (ne_of_gt has)
    have hps : p ∣ s.prod := hpa.trans (Multiset.dvd_prod ha)
    exact (Nat.squarefree_iff_prime_squarefree.mp hprod p hp) (Nat.mul_dvd_mul hpa hps)

/-- Every unordered multiset factorization of a squarefree integer is represented
by a unique set of integer factors. No multiplicity is lost. -/
def unorderedFactorizationEquiv (d : ℕ) (hs : Squarefree d) :
    {s : Multiset ℕ // (∀ a ∈ s, 1 < a) ∧ s.prod = d} ≃ ↥(factorizations d) where
  toFun s := by
    have hsq : Squarefree s.val.prod := by rw [s.property.2]; exact hs
    let F : Finset ℕ := ⟨s.val, nodup_of_squarefree_product s.val hsq s.property.1⟩
    refine ⟨F, (mem_factorizations hs.ne_zero F).mpr ⟨s.property.1, ?_⟩⟩
    simpa [Finset.prod, F] using s.property.2
  invFun F := by
    obtain ⟨hlt,hprod⟩ := (mem_factorizations hs.ne_zero _).mp F.property
    refine ⟨F.val.val, hlt, ?_⟩
    change (F.val.val.map id).prod = d at hprod
    simpa only [Multiset.map_id] using hprod
  left_inv _ := rfl
  right_inv _ := rfl

#print axioms nodup_of_squarefree_product
#print axioms unorderedFactorizationEquiv

end ZInQBlueprint.TYZ
