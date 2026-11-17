import CollisionOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The literal Sylvester determinant and its first nonzero coefficient. -/
open Polynomial Finset
namespace Sun28.Collision
noncomputable section
variable {K ι : Type*} [Field K]

/-- The weighted monic characteristic polynomial on the split fibre. -/
def projected (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) : K[X] :=
  ∏ x ∈ S, (X-C (ell x))^wt x

/-- The literal Sylvester determinant Res_T(P(T),P(T+V)), in the coefficient variable V. -/
def shiftedResultant (P : K[X]) : K[X] :=
  let q := P.map (C : K →+* K[X])
  Polynomial.resultant q (q.comp (X+C X)) q.natDegree (q.comp (X+C X)).natDegree

private theorem lift_projected (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    (projected S ell wt).map (C : K →+* K[X]) =
    ∏ x ∈ S, ((X : K[X][X])-C (C (ell x)))^wt x := by
  classical
  simp [projected,Polynomial.map_prod]

theorem resultant_differences (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    shiftedResultant (projected S ell wt) = differences S ell wt := by
  classical
  let U : ι → K[X][X] := fun x => (X-C (C (ell x)))^wt x
  let Q : K[X][X] := ∏ x ∈ S,U x
  let H := Q.comp (X+C X)
  have lift : (projected S ell wt).map (C : K →+* K[X])=Q := lift_projected S ell wt
  have mon (x : ι) : (U x).Monic := (monic_X_sub_C _).pow _
  have lead : ∏ x ∈ S, (U x).leadingCoeff ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun x _ => (mon x).leadingCoeff ▸ one_ne_zero)
  unfold shiftedResultant
  dsimp only
  rw [lift]
  change Polynomial.resultant (∏ x ∈ S,U x) H (∏ x ∈ S,U x).natDegree H.natDegree=_
  rw [resultant_prod_left _ _ _ _ lead le_rfl]
  unfold differences
  rw [Finset.prod_product]
  apply Finset.prod_congr rfl
  intro x hx
  have factor : (U x).natDegree = wt x := by simp [U,natDegree_pow]
  rw [factor,show U x=(X-C (C (ell x)))^wt x from rfl,resultant_X_sub_C_pow_left _ _ _ _ le_rfl]
  have ev : H.eval (C (ell x)) = ∏ y ∈ S, ((X:K[X])-C (ell y-ell x))^wt y := by
    simp [H,Q,U,eval_comp,eval_prod,map_sub]
    apply Finset.prod_congr rfl
    intro y hy
    congr 1
    ring
  rw [ev,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro y hy
  rw [←pow_mul,Nat.mul_comm (wt y) (wt x)]

/-- The collision order is the index of the first nonzero coefficient of the determinant.
This coefficient exists also when the tuple set is empty. -/
theorem resultant_coefficient [DecidableEq K] (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    let d := ∑ z ∈ S ×ˢ S, if ell z.1=ell z.2 then wt z.1*wt z.2 else 0
    let R := shiftedResultant (projected S ell wt)
    R.coeff d≠0 ∧ ∀ j<d, R.coeff j=0 := by
  classical
  dsimp only
  rw [resultant_differences,←order_differences,rootMultiplicity_eq_natTrailingDegree']
  apply And.intro
  · apply coeff_natTrailingDegree_ne_zero.mpr
    exact (monic_prod_of_monic _ _ (fun z _ => (monic_X_sub_C _).pow _)).ne_zero
  · intro j hj; exact coeff_eq_zero_of_lt_natTrailingDegree hj

#print axioms resultant_differences
#print axioms resultant_coefficient
end
end Sun28.Collision
