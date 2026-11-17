import TYZUnordered
import PublishedGenusRows

namespace ZInQBlueprint.TYZ

/-- The unordered-factorization bijection preserves products for every weight.
In particular, taking the class-group weight gives the terms of Tian's sum. -/
theorem unorderedFactorization_weight {M : Type*} [CommMonoid M] (w : ℕ → M)
    {d : ℕ} (hs : Squarefree d) (s : {s : Multiset ℕ // (∀ a ∈ s, 1 < a) ∧ s.prod = d}) :
    ∏ a ∈ ((unorderedFactorizationEquiv d hs) s).val, w a = (s.val.map w).prod := rfl

/-- The weighted sum over all unordered multiset factorizations of a squarefree
integer, restricted by a predicate on the set of factors. -/
noncomputable def unorderedSum {d : ℕ} (hs : Squarefree d) (keep : Finset ℕ → Prop)
    (w : ℕ → ℕ) : ℕ := by
  classical
  let e := unorderedFactorizationEquiv d hs
  let _ := Fintype.ofEquiv _ e.symm
  exact ∑ s : {s : Multiset ℕ // (∀ a ∈ s, 1 < a) ∧ s.prod = d},
    if keep s.val.toFinset then (s.val.map w).prod else 0

/-- Replacing unordered multisets by sets preserves each of Tian's genus sums. -/
theorem unorderedGenusSum_eq {d : ℕ} (hs : Squarefree d) (keep : Finset ℕ → Prop) :
    unorderedSum hs keep genusNumber = OriginalRank.PublishedGenusRows.rowSum d keep := by
  classical
  let e := unorderedFactorizationEquiv d hs
  let _ := Fintype.ofEquiv _ e.symm
  unfold unorderedSum OriginalRank.PublishedGenusRows.rowSum
  calc
    _ = ∑ s, if keep (e s).val then ∏ a ∈ (e s).val, genusNumber a else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      have he : s.val.toFinset = (e s).val :=
        Finset.ext (fun _ => Multiset.mem_toFinset)
      rw [he, unorderedFactorization_weight genusNumber hs s]
    _ = ∑ F : ↥(factorizations d), if keep F.val then ∏ a ∈ F.val, genusNumber a else 0 :=
      e.sum_comp (fun F => if keep F.val then ∏ a ∈ F.val, genusNumber a else 0)
    _ = _ := Finset.sum_coe_sort (factorizations d)
      (fun F => if keep F then ∏ a ∈ F, genusNumber a else 0)

/-- At four the unordered factorization 2·2 loses its product on passing to a set. -/
theorem repeated_factor_four :
    (2 ::ₘ 2 ::ₘ (0 : Multiset ℕ)).prod = 4 ∧
      (2 ::ₘ 2 ::ₘ (0 : Multiset ℕ)).toFinset ∉ factorizations 4 := by
  constructor
  · decide
  · intro h
    have bad := ((mem_factorizations (by decide : 4 ≠ 0) _).mp h).2
    norm_num at bad

end ZInQBlueprint.TYZ

#print axioms ZInQBlueprint.TYZ.unorderedFactorization_weight
#print axioms ZInQBlueprint.TYZ.unorderedGenusSum_eq
#print axioms ZInQBlueprint.TYZ.repeated_factor_four
