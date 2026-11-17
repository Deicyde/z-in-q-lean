import OddRadicalField
import Mathlib.Data.Nat.Squarefree

/-! The mixed quadratic obstruction when adjoining the odd divisor radicals
to the remaining extended CM fields. -/
namespace ZInQBlueprint.TYZ.Specialization
noncomputable section
open IntermediateField

private theorem mem_of_same_square {F : SubfieldQ} {x y : K}
    (hy : y ∈ F) (he : x^2 = y^2) : x ∈ F := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · rwa [h]
  · rw [h]; exact F.neg_mem hy

private def primeExtension (F : SubfieldQ) (s : Finset ℕ) : SubfieldQ :=
  F ⊔ IntermediateField.adjoin ℚ (sqrtDivisor '' (↑s : Set ℕ))

private theorem root_mem_primeExtension {n d : ℕ} (hs : Squarefree n) (hd : d ∣ n) (F : SubfieldQ) :
    sqrtDivisor d ∈ primeExtension F n.primeFactors := by
  let v := ∏ p ∈ d.primeFactors, sqrtDivisor p
  have hm : v ∈ primeExtension F n.primeFactors := by
    apply (primeExtension F n.primeFactors).prod_mem
    intro p hp
    apply (show IntermediateField.adjoin ℚ _ ≤ primeExtension F n.primeFactors from le_sup_right)
    apply IntermediateField.subset_adjoin ℚ _
    have h := Nat.mem_primeFactors.mp hp
    exact ⟨p,Nat.mem_primeFactors.mpr ⟨h.1,h.2.1.trans hd,hs.ne_zero⟩,rfl⟩
  apply mem_of_same_square hm
  rw [sqrtDivisor_sq]
  dsimp [v]
  rw [←Finset.prod_pow]
  simp_rw [sqrtDivisor_sq]
  rw [←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree (hs.squarefree_of_dvd hd)]

/-- A rational square root belongs to a multiquadratic extension only if
multiplying it by a square root of a subset product puts it in the base. -/
private theorem descend_root (F : SubfieldQ) (s : Finset ℕ) {a : K} {q : ℚ}
    (ha : a^2=(q:K)) (hm : a ∈ primeExtension F s) :
    ∃ t ⊆ s, a*sqrtDivisor (∏ p ∈ t, p) ∈ F := by
  classical
  induction s using Finset.induction_on generalizing a q with
  | empty =>
    have h : a ∈ F := by simpa [primeExtension] using hm
    refine ⟨∅,Finset.empty_subset _,?_⟩
    apply mem_of_same_square h
    simp [mul_pow,sqrtDivisor_sq]
  | @insert d s hd ih =>
    have eq : primeExtension F (insert d s) =
        primeExtension F s ⊔ IntermediateField.adjoin ℚ {sqrtDivisor d} := by
      unfold primeExtension
      rw [Finset.coe_insert,Set.image_insert_eq,sup_assoc,←IntermediateField.adjoin_union,Set.union_singleton]
    rw [eq] at hm
    have sq : (sqrtDivisor d)^2 = ((d:ℚ):K) := by simpa using sqrtDivisor_sq d
    rcases squareRoot_quadratic_step sq ha hm with h | h
    · obtain ⟨t,ht,hh⟩ := ih ha h
      exact ⟨t,ht.trans (Finset.subset_insert ..),hh⟩
    · have hh : (a*sqrtDivisor d)^2=((q*d : ℚ):K) := by simp [mul_pow,ha,sqrtDivisor_sq]
      obtain ⟨t,ht,hh'⟩ := ih hh h
      have hdt : d ∉ t := fun htt => hd (ht htt)
      refine ⟨insert d t, Finset.insert_subset_insert d ht,mem_of_same_square hh' ?_⟩
      rw [Finset.prod_insert hdt]
      simp [mul_pow,sqrtDivisor_sq]
      ring

/-- Exact interaction of an arbitrary base field with the radical factor
Lₙ(i). The test family includes d=1, which checks the base itself. -/
theorem sqrtTwo_mem_sup_radicalField_iff {n : ℕ} (hs : Squarefree n) (F : SubfieldQ)
    (hi : Rank.sqrtMinus 1 ∈ F) :
    sqrtDivisor 2 ∈ F ⊔ radicalField n ↔ ∃ d, d ∣ n ∧ sqrtDivisor (2*d) ∈ F := by
  have eq : F ⊔ radicalField n = primeExtension F n.primeFactors := by
    apply le_antisymm
    · apply sup_le (show F ≤ primeExtension F n.primeFactors from le_sup_left)
      apply IntermediateField.adjoin_le_iff.mpr
      rintro a (ha | ⟨d,hd,rfl⟩)
      · rw [ha]; exact (show F ≤ primeExtension F n.primeFactors from le_sup_left) hi
      · exact root_mem_primeExtension hs (Nat.mem_divisors.mp hd).1 F
    · apply sup_le le_sup_left
      apply IntermediateField.adjoin_le_iff.mpr
      rintro a ⟨p,hp,rfl⟩
      apply (show radicalField n ≤ F ⊔ radicalField n from le_sup_right)
      apply IntermediateField.subset_adjoin ℚ _
      apply Set.mem_insert_of_mem
      exact ⟨p,Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1,hs.ne_zero⟩,rfl⟩
  rw [eq]
  constructor
  · intro hm
    have sq : sqrtDivisor 2 ^ 2 = ((2:ℚ):K) := by simpa using sqrtDivisor_sq 2
    obtain ⟨t,ht,hm'⟩ := descend_root F n.primeFactors sq hm
    let d := ∏ p ∈ t, p
    have hdiv : d ∣ n := by
      rw [←Nat.prod_primeFactors_of_squarefree hs]
      exact Finset.prod_dvd_prod_of_subset t n.primeFactors (fun q : ℕ => q) ht
    refine ⟨d,hdiv,mem_of_same_square hm' ?_⟩
    simp [d,mul_pow,sqrtDivisor_sq]
  · rintro ⟨d,hd,hm⟩
    let P := primeExtension F n.primeFactors
    have hf : F ≤ P := le_sup_left
    have hrd := root_mem_primeExtension hs hd F
    apply mem_of_same_square (P.div_mem (hf hm) hrd)
    have hd0 : (d:K) ≠ 0 := by exact_mod_cast (Nat.pos_of_dvd_of_pos hd hs.ne_zero.bot_lt).ne'
    simp [div_pow,sqrtDivisor_sq,hd0]

/-- The class-five and class-six extended fields together with i, before adjoining
the radical genus field. The class-six factors are absent for odd n. -/
def extendedFieldWithI (H : ℕ → SubfieldQ) (n : ℕ) : SubfieldQ :=
  IntermediateField.adjoin ℚ {Rank.sqrtMinus 1} ⊔ (n.divisors.filter fun d => d%8=5 ∨ d%8=6).sup H

/-- In the literal TYZ compositum, excluding √2 reduces precisely to excluding
the finitely many mixed quadratic fields from the extended-field part. -/
theorem sqrtTwo_not_mem_genusCompositum_iff {n : ℕ} (hs : Squarefree n) (H : ℕ → SubfieldQ) :
    sqrtDivisor 2 ∉ genusCompositum H n ↔
      ∀ d, d ∣ n → sqrtDivisor (2*d) ∉ extendedFieldWithI H n := by
  have hi : Rank.sqrtMinus 1 ∈ extendedFieldWithI H n :=
    (show IntermediateField.adjoin ℚ {Rank.sqrtMinus 1} ≤ extendedFieldWithI H n from le_sup_left)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have incl : IntermediateField.adjoin ℚ {Rank.sqrtMinus 1} ≤ radicalField n :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)))
  have eq : genusCompositum H n = extendedFieldWithI H n ⊔ radicalField n := by
    unfold genusCompositum extendedFieldWithI
    apply le_antisymm
    · exact sup_le le_sup_right (le_trans le_sup_right le_sup_left)
    · exact sup_le (sup_le (incl.trans le_sup_left) le_sup_right) le_sup_left
  rw [eq,sqrtTwo_mem_sup_radicalField_iff hs _ hi]
  push Not
  rfl

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.sqrtTwo_mem_sup_radicalField_iff
#print axioms ZInQBlueprint.TYZ.Specialization.sqrtTwo_not_mem_genusCompositum_iff
