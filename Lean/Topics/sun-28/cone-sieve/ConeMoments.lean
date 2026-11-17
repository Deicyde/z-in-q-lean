import ConeExpansion

namespace Sun28.ConeSieve
open Finset
noncomputable section
open scoped Classical

private theorem extend_product (P r : Finset ℕ) (sub : r⊆P) (f : ℕ → ℝ) :
    (∏ p ∈ P, (if p∈r then f p else 1)) = ∏ p ∈ r, f p := by
  classical
  rw [prod_ite,prod_const_one,mul_one]
  have h : (P.filter (fun p=>p∈r))=r := by ext p; simp; exact fun hp=>sub hp
  rw [h]

/-- Distinct centered products are orthogonal under the finite product measure. -/
theorem orthogonal (P r s : Finset ℕ) (g : ℕ → ℝ) (hr : r⊆P) (hs : s⊆P)
    (lt : ∀ p∈P, g p < 1) :
    (∑ U ∈ P.powerset, probability P g U * (basis g r U * basis g s U)) =
    if r=s then ∏ p ∈ r, odds g p else 0 := by
  classical
  let A := fun p : ℕ => (if p∈r then (-1:ℝ) else 1)*(if p∈s then (-1:ℝ) else 1)
  let B := fun p : ℕ => (if p∈r then odds g p else 1)*(if p∈s then odds g p else 1)
  have product (U : Finset ℕ) : basis g r U * basis g s U =
      ∏ p ∈ P, (if p∈U then A p else B p) := by
    unfold basis
    rw [←extend_product P r hr,←extend_product P s hs,←prod_mul_distrib]
    apply prod_congr rfl; intro p _
    by_cases x : p∈r <;> by_cases y : p∈s <;> by_cases u : p∈U <;> simp [A,B,x,y,u]
  simp_rw [product]
  rw [factor_average]
  have mean (p : ℕ) (hp : p∈P) : g p * (-1)+(1-g p)*odds g p=0 := by
    dsimp [odds];field_simp [ne_of_gt (sub_pos.mpr (lt p hp))];ring
  have variance (p : ℕ) (hp : p∈P) : g p+(1-g p)*(odds g p*odds g p) = odds g p := by
    dsimp [odds];field_simp [ne_of_gt (sub_pos.mpr (lt p hp))];ring
  by_cases e : r=s
  · subst s; rw [ite_eq_left rfl,←extend_product P r hr]
    apply prod_congr rfl; intro p hp
    by_cases a : p∈r
    · simpa [A,B,a] using variance p hp
    · simp [A,B,a]
  · rw [ite_eq_right e]
    by_cases sub : r⊆s
    · obtain ⟨p,ps,pr⟩:=not_subset.mp (show ¬s⊆r from fun h=>e (Subset.antisymm sub h))
      apply prod_eq_zero (hs ps)
      simpa [A,B,pr,ps] using mean p (hs ps)
    · obtain ⟨p,pr,ps⟩:=not_subset.mp sub
      apply prod_eq_zero (hr pr)
      simpa [A,B,pr,ps] using mean p (hr pr)

def denominator (g : ℕ → ℝ) (I : Finset (Finset ℕ)) := ∑ r ∈ I, ∏ p ∈ r, odds g p
def testSum (g : ℕ → ℝ) (I : Finset (Finset ℕ)) (U : Finset ℕ) := ∑ r ∈ I, basis g r U

/-- The unnormalised Selberg test has second moment equal to its value on a surviving record. -/
theorem model_second (P : Finset ℕ) (g : ℕ → ℝ) (I : Finset (Finset ℕ))
    (sub : ∀ r∈I,r⊆P) (lt : ∀ p∈P,g p<1) :
    (∑ U∈P.powerset,probability P g U*(testSum g I U)^2) = denominator g I := by
  classical
  simp only [testSum,pow_two,mul_sum,sum_mul]
  rw [sum_comm]
  unfold denominator
  apply sum_congr rfl; intro r hr
  rw [sum_comm]
  calc
    _ = ∑ s ∈ I, (if r=s then ∏ p ∈ r, odds g p else 0) := by
      apply sum_congr rfl; intro s hs; simpa only [mul_comm (basis g r _) (basis g s _)] using orthogonal P r s g (sub r hr) (sub s hs) lt
    _ = _ := by simp [hr]

theorem test_empty (g : ℕ → ℝ) (I : Finset (Finset ℕ)) :
    testSum g I ∅=denominator g I := by simp [testSum,denominator,basis]

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.orthogonal
#print axioms Sun28.ConeSieve.model_second
#print axioms Sun28.ConeSieve.test_empty
