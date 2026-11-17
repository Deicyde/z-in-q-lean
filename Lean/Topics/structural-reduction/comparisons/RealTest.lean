import BoundedTest
namespace StructuralReduction
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

/-- Both embeddings use the same calculation. -/
theorem real_range {c y : K} (hc : 0<c) :
    0<1+scaled c y ∧ 0≤bounded c y ∧ bounded c y<1 := by
  have hsq : 0≤y*y := by
    by_cases h : 0≤y
    · exact OrderedRing.mul_nonneg h h
    · have hn : 0≤ -y := by grind
      have hs := OrderedRing.mul_nonneg hn hn
      rwa [show -y * (-y) = y*y by grobner] at hs
  have hnum : 0≤scaled c y := OrderedRing.mul_nonneg (Preorder.le_of_lt hc) hsq
  have hp : 0<1+scaled c y := by grind
  have den : 1+scaled c y ≠ 0 := Preorder.ne_of_gt hp
  have same : bounded c y * (1+scaled c y)=scaled c y := Field.div_mul_cancel den
  have lower : 0≤bounded c y := by
    apply Classical.byContradiction; intro h
    have neg : bounded c y<0 := by grind
    have := OrderedRing.mul_neg_of_neg_of_pos neg hp
    grind
  have upper : bounded c y<1 := by
    apply Classical.byContradiction; intro h
    have hh : 0≤bounded c y-1 := by grind
    have hz := OrderedRing.mul_nonneg hh (Preorder.le_of_lt hp)
    have eq : (bounded c y-1)*(1+scaled c y) = bounded c y*(1+scaled c y)-(1+scaled c y) := by grobner
    rw [eq,same] at hz
    grind
  exact ⟨hp,lower,upper⟩

private theorem product_bound (xs : List K) {b : K} (one : 1≤b)
    (h : ∀ x∈xs, 1≤x ∧ x≤b) :
    1≤xs.foldr (·*·) 1 ∧ xs.foldr (·*·) 1≤b^xs.length := by
  induction xs with
  | nil => simp [Semiring.pow_zero]; grind
  | cons x xs ih =>
    obtain ⟨a,d⟩ := h x (by simp)
    obtain ⟨l,r⟩ := ih (fun z hz=>h z (List.mem_cons_of_mem _ hz))
    simp only [List.foldr_cons,List.length_cons,Semiring.pow_succ]
    have z0 : (0:K)≤1 := OrderedRing.zero_le_one
    have l0 : 0≤xs.foldr (·*·) 1 := by grind
    have b0 : 0≤b := by grind
    have lo := OrderedRing.mul_le_mul_of_nonneg_right a l0
    have u := OrderedRing.mul_le_mul_of_nonneg_right d l0
    have v := OrderedRing.mul_le_mul_of_nonneg_left r b0
    rw [Semiring.one_mul] at lo
    rw [CommSemiring.mul_comm b (b^xs.length)] at v
    grind

theorem real_product (xs : List K) (h : ∀ x∈xs, 1≤x ∧ x≤17/16)
    (n : xs.length=16) : 1≤xs.foldr (·*·) 1 ∧ xs.foldr (·*·) 1<3 := by
  have one : (1:K)≤17/16 := by grind
  obtain ⟨l,r⟩ := product_bound xs one h
  rw [n] at r
  have bound : (17/16:K)^16<3 := by grind
  exact ⟨l,Preorder.lt_of_le_of_lt r bound⟩

#print axioms real_range
#print axioms real_product
end StructuralReduction
