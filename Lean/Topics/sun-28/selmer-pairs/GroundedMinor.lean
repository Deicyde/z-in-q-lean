import SupportMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block

namespace Sun28.SupportMatrix
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Idx (ι : Type*) := ι ⊕ Unit
def column : Matrix ι Unit F := fun _ _ => 1
def pivot : Vec (Idx ι) := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Restore the distinguished row and column from the zero sums. -/
def balanced (M : Matrix ι ι F) : Matrix (Idx ι) (Idx ι) F :=
  let c : Matrix ι Unit F := column
  fromBlocks M (-(M*c)) (-(cᵀ*M)) (cᵀ*M*c)

noncomputable def groundedInverse (M : Matrix ι ι F) : Matrix (Idx ι) (Idx ι) F :=
  fromBlocks M⁻¹ 0 0 0

theorem inverse_products {M : Matrix ι ι F} (h : IsUnit M.det) :
    groundedInverse M * balanced M = 1-vecMulVec 1 pivot ∧
    balanced M * groundedInverse M = 1-vecMulVec pivot 1 := by
  simp only [groundedInverse, balanced, fromBlocks_multiply, mul_zero, zero_mul, add_zero,
    nonsing_inv_mul _ h, mul_nonsing_inv _ h]
  constructor <;> ext i j <;> cases i <;> cases j <;> simp [pivot, one_apply, vecMulVec]
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.one_mul]
    rfl
  · rw [Matrix.mul_assoc, mul_nonsing_inv _ h, Matrix.mul_one]
    rfl

/-- The finite-certificate test follows from nonsingularity of the literal
deleted minor and its row- and column-sum completion. -/
noncomputable def of_minor {K : Matrix (Idx ι) (Idx ι) F} {s l a b : Vec (Idx ι)}
    (M : Matrix ι ι F) (det : IsUnit M.det) (sum_zero : K+vecMulVec l a=balanced M)
    (constant : K *ᵥ 1 = 0) (marked : K *ᵥ b = 0) (odd : (1 : Vec (Idx ι)) ⬝ᵥ s=1)
    (total : a ⬝ᵥ 1=0) (mark : a ⬝ᵥ b=1)
    (reciprocity : K+Kᵀ=vecMulVec s s+diagonal s) :
    Certificate K s l a b pivot where
  inverse := groundedInverse M
  constants := constant
  marked := marked
  odd_sign := odd
  selector_total := total
  selector_mark := mark
  reciprocity := reciprocity
  left_product := sum_zero ▸ (inverse_products det).1
  right_product := sum_zero ▸ (inverse_products det).2

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.inverse_products
#print axioms Sun28.SupportMatrix.of_minor
