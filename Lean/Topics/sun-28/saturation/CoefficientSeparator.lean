import CollisionResultant

/-! A bounded list of coefficient tests for a separating linear form. -/
open Polynomial Finset ZInQBlueprint.SunTower
namespace Sun28.Collision
noncomputable section
variable {K ι : Type*} [Field K]

theorem resultant_nonzero (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    shiftedResultant (projected S ell wt) ≠ 0 := by
  rw [resultant_differences]
  exact (monic_prod_of_monic _ _ (fun z _ => (monic_X_sub_C _).pow _)).ne_zero

theorem resultant_degree (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    (shiftedResultant (projected S ell wt)).natDegree=(∑ x ∈ S, wt x)^2 := by
  classical
  rw [resultant_differences,differences,natDegree_prod]
  · simp only [natDegree_pow,natDegree_X_sub_C,mul_one,Finset.sum_product]
    simp only [←Finset.mul_sum,←Finset.sum_mul,pow_two]
  · intro z _
    exact ((monic_X_sub_C _).pow _).ne_zero

/-- A branch for (b,d) tests one coefficient for nonvanishing and all lower
coefficients in every candidate for vanishing. All tests are polynomial equalities or inequations. -/
def CoefficientMinimum (R : ℕ → K[X]) (B b d : ℕ) : Prop :=
  (R b).coeff d≠0 ∧ ∀ j ≤ B, ∀ k<d, (R j).coeff k=0

theorem coefficientMinimum_iff {R : ℕ → K[X]} (live : ∀ j, R j≠0) {B b : ℕ} :
    (∃ d≤(R b).natDegree, CoefficientMinimum R B b d) ↔
    ∀ j≤B, (R b).natTrailingDegree≤(R j).natTrailingDegree := by
  constructor
  · rintro ⟨d,_,hd,lower⟩ j hj
    have rb : (R b).natTrailingDegree≤d := le_of_not_gt (fun e => hd (coeff_eq_zero_of_lt_natTrailingDegree e))
    apply rb.trans
    exact le_of_not_gt (fun e => (coeff_natTrailingDegree_ne_zero.mpr (live j)) (lower j hj _ e))
  · intro h
    refine ⟨_,natTrailingDegree_le_natDegree _,(coeff_natTrailingDegree_ne_zero.mpr (live b)),?_⟩
    intro j hj k hk
    exact coeff_eq_zero_of_lt_natTrailingDegree (hk.trans_le (h j hj))

/-- Finite coefficient test equivalent to injectivity on the specialized fibre.
The number of distinct geometric tuples need not be known to perform the test. -/
theorem separates_iff_coefficient_branch [CharZero K] {n : ℕ} (S : Finset (Fin n → K))
    (wt : (Fin n → K) → ℕ) (positive : ∀ x ∈ S, 0<wt x)
    {b B : ℕ} (bound : S.card.choose 2*(n-1)≤B) :
    Set.InjOn (separator (b:K)) (S : Set (Fin n → K)) ↔
    ∃ d≤(∑ x ∈ S, wt x)^2, CoefficientMinimum
      (fun j : ℕ => shiftedResultant (projected S (separator (j:K)) wt)) B b d := by
  rw [←resultant_degree S (separator (b:K)) wt]
  rw [coefficientMinimum_iff (fun j => resultant_nonzero S (separator (j:K)) wt)]
  simpa only [resultant_differences,rootMultiplicity_eq_natTrailingDegree'] using
    (separates_iff_minimizes S wt positive b B bound)

#print axioms resultant_nonzero
#print axioms resultant_degree
#print axioms coefficientMinimum_iff
#print axioms separates_iff_coefficient_branch
end
end Sun28.Collision
