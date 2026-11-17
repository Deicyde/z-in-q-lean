import ClassWeights
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

namespace Sun28.PrimeClasses
open Finset Sun28.FinitePattern Sun28.ContactFactors
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- none chooses the all-plus box. some j records the first failed plus condition. -/
def rectangle (safe : Bool→ι→Prop) (r : Option ι) (i : ι) : Prop :=
  match r with
  | none => safe true i
  | some j => safe false i ∧ (i<j → safe true i) ∧ (i=j → ¬safe true i)

theorem unique_rectangle (safe : Bool→ι→Prop) :
    ( (∀ i,safe true i) ∨ (∀ i,safe false i) ) ↔ ∃! r,∀ i,rectangle safe r i := by
  constructor
  · intro good
    by_cases pos : ∀ i,safe true i
    · refine ⟨none,pos,?_⟩
      rintro (_|j) h
      · rfl
      · exact ((h j).2.2 rfl (pos j)).elim
    · have non : (univ.filter (fun i => ¬safe true i)).Nonempty := by
        obtain ⟨i,hi⟩ := not_forall.mp pos
        exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
      let j := (univ.filter (fun i => ¬safe true i)).min' non
      have hj : ¬safe true j := (mem_filter.mp (min'_mem _ non)).2
      have before (i : ι) (h : i<j) : safe true i := by
        by_contra bad
        exact (not_le_of_gt h) (min'_le _ i (mem_filter.mpr ⟨mem_univ _,bad⟩))
      refine ⟨some j,fun i => ⟨good.resolve_left pos i,before i,fun e => e ▸ hj⟩,?_⟩
      rintro (_|k) h
      · exact (hj (h j)).elim
      · congr 1
        apply le_antisymm
        · by_contra! h'
          exact hj ((h j).2.1 h')
        · by_contra! h'
          exact (h k).2.2 rfl (before k h')
  · rintro ⟨(_|j),h,_⟩
    · exact Or.inl h
    · exact Or.inr fun i => (h i).1

omit [LinearOrder ι] in
private theorem bool_product (P : ι→Prop) : (∏ i, if P i then (1:ℕ) else 0)=if ∀ i,P i then 1 else 0 := by
  by_cases h : ∀ i,P i
  · simp [h]
  · obtain ⟨i,bad⟩ := not_forall.mp h
    have zero := Finset.prod_eq_zero (s:=univ) (f:=fun i => if P i then (1:ℕ) else 0)
      (mem_univ i) (by simp [bad])
    simp [h,zero]

theorem positive_expansion (safe : Bool→ι→Prop) :
    (if (∀ i,safe true i) ∨ (∀ i,safe false i) then (1:ℕ) else 0)=
    ∑ r : Option ι, ∏ i, if rectangle safe r i then 1 else 0 := by
  simp_rw [bool_product]
  by_cases good : (∀ i,safe true i) ∨ (∀ i,safe false i)
  · obtain ⟨r,sol,alone⟩ := (unique_rectangle safe).mp good
    rw [ite_eq_left good,Finset.sum_eq_single r]
    · simp [sol]
    · intro k _ ne
      exact ite_eq_right fun all => ne (alone k all)
    · simp
  · rw [ite_eq_right good]
    symm
    apply sum_eq_zero
    rintro (_|j) _
    · exact ite_eq_right (fun h => good (Or.inl h))
    · exact ite_eq_right (fun h => good (Or.inr fun i => (h i).1))

/-- Nonnegative finite expansion in position-wise conditions. -/
def expansion {P : Type*} [Fintype P] (safe : P→Bool→ι→Prop) : Prop :=
    (∏ q,if (∀ i,safe q true i) ∨ (∀ i,safe q false i) then (1:ℕ) else 0)=
    ∑ r : P→Option ι, ∏ i,∏ q, if rectangle (safe q) (r q) i then 1 else 0

theorem cutoff_expansion {P : Type*} [Fintype P] (safe : P→Bool→ι→Prop) : expansion safe := by
  unfold expansion
  simp_rw [positive_expansion]
  rw [Fintype.prod_sum]
  exact sum_congr rfl fun r _ => Finset.prod_comm

def splitSafe (A : Fin 3→ℚ) (x : ℕ×ℕ) (T : Finset ℕ) (q : ↥T) (s : Bool) (i : ↥(shifts A)) : Prop :=
  ¬(q.val:ℤ)∣signedOrder (form A x i).toNat s

/-- Conjugation-free split-prime conditions on the actual polynomial values. -/
theorem split_class_expansion (A : Fin 3→ℚ) (x : ℕ×ℕ) (T : Finset ℕ) :
    expansion (splitSafe A x T) := cutoff_expansion _

end
end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.unique_rectangle
#print axioms Sun28.PrimeClasses.positive_expansion
#print axioms Sun28.PrimeClasses.cutoff_expansion
#print axioms Sun28.PrimeClasses.split_class_expansion
