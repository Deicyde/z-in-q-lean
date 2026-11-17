import TYZFactorizations

open Finset
open ZInQ.RouteK.Rank5b
open scoped BigOperators

namespace ZInQBlueprint.TYZ

/-- Exactly one factor has residue seven, exactly one has residue three, and
each remaining factor has residue one. -/
def Residues (F : Finset ℕ) : Prop :=
  (F.filter (fun a => a % 8 = 7)).card = 1 ∧
  (F.filter (fun a => a % 8 = 3)).card = 1 ∧
  ∀ a ∈ F, a % 8 = 7 ∨ a % 8 = 3 ∨ a % 8 = 1

instance (F : Finset ℕ) : Decidable (Residues F) := by unfold Residues; infer_instance

theorem residues_factors {d : ℕ} (P : PrimePartition d) :
    Residues (factors P) ↔ Admissible5bNat d P := by
  unfold Residues Admissible5bNat factors
  simp only [filter_map, card_map, forall_mem_map]
  rfl

/-- Weighted reindexing over any commutative semiring. -/
theorem sum_by_factorizations {R : Type*} [CommSemiring R] {d : ℕ}
    (hs : Squarefree d) (w : ℕ → R) :
    (∑ F ∈ factorizations d, if Residues F then ∏ a ∈ F, w a else 0) =
    ∑ P : PrimePartition d, if Admissible5bNat d P then ∏ B ∈ P.parts, w (dProd B) else 0 := by
  classical
  let e : PrimePartition d ↪ Finset ℕ := ⟨factors, factors_injective⟩
  have hmap : factorizations d = (univ : Finset (PrimePartition d)).map e := by
    ext F
    rw [mem_map]
    constructor
    · intro hF
      exact ⟨partitionOf hs F hF, mem_univ _, factors_partitionOf hs hF⟩
    · rintro ⟨P, _, rfl⟩
      exact factors_mem hs P
  rw [hmap, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro P _
  change (if Residues (factors P) then ∏ a ∈ factors P, w a else 0) = _
  by_cases h : Admissible5bNat d P
  · rw [ite_eq_left ((residues_factors P).mpr h), ite_eq_left h, factors, Finset.prod_map]
    rfl
  · rw [ite_eq_right (fun hc => h ((residues_factors P).mp hc)), ite_eq_right h]

/-- The class-group weight on positive integers, extended by zero at zero. -/
noncomputable def genusNumber (a : ℕ) : ℕ :=
  if ha : a ≠ 0 then
    letI : NeZero a := ⟨ha⟩
    gCl a
  else 0

@[simp] theorem genusNumber_dProd {d : ℕ} (B : Finset d.primeFactors) :
    genusNumber (dProd B) = gCl (dProd B) := by simp [genusNumber, NeZero.ne (dProd B)]

/-- The integer coefficient indexed by unordered factorizations into integers. -/
noncomputable def integerCoefficient (d : ℕ) : ℕ :=
  ∑ F ∈ factorizations d, if Residues F then ∏ a ∈ F, genusNumber a else 0

theorem integerCoefficient_mod_two {d : ℕ} (hs : Squarefree d) :
    (integerCoefficient d : ZMod 2) = T5bCl d := by
  classical
  rw [integerCoefficient, Nat.cast_sum, T5bCl]
  calc
    _ = ∑ F ∈ factorizations d,
        if Residues F then ∏ a ∈ F, (genusNumber a : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      by_cases hF : Residues F <;> simp [hF]
    _ = _ := by
      rw [sum_by_factorizations hs]
      simp only [genusNumber_dProd]

#print axioms sum_by_factorizations
#print axioms integerCoefficient_mod_two

end ZInQBlueprint.TYZ
