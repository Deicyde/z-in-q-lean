import SupportMatrix
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block

namespace Sun28.SupportMatrix
open Matrix
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The incidence block for the edges from each old index to an extra vertex. -/
def starIncidence : Matrix (ι ⊕ Unit) ι F := fun r j =>
  r.elim (fun i => if i=j then 1 else 0) (fun _ => 1)

theorem star_injective (y : Vec ι) (h : starIncidence *ᵥ y = 0) : y=0 := by
  ext i
  have row := congrFun h (Sum.inl i)
  simpa [starIncidence,mulVec,dotProduct] using row

theorem star_left_constant (x : Vec (ι ⊕ Unit)) (h : starIncidenceᵀ *ᵥ x = 0) :
    x = (x (Sum.inr ())) • 1 := by
  ext i
  cases i with
  | inl j =>
    have row := congrFun h j
    have hz : x (Sum.inl j) + x (Sum.inr ()) = 0 := by
      simpa [starIncidence,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type] using row
    simpa [ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left hz
  | inr j => simp

set_option maxHeartbeats 800000 in
/-- The initial principal minor. The sole condition on its upper-left block
is the parity of the sum of its entries. -/
theorem initial_minor (D : Matrix (ι ⊕ Unit) (ι ⊕ Unit) F)
    (odd : (1 : Vec (ι ⊕ Unit)) ⬝ᵥ (D *ᵥ 1) = 1) :
    IsUnit (fromBlocks D starIncidence starIncidenceᵀ (0 : Matrix ι ι F)).det := by
  let C : Matrix (ι ⊕ Unit) ι F := starIncidence
  let M := fromBlocks D C Cᵀ (0 : Matrix ι ι F)
  have vanish {z : Vec ((ι ⊕ Unit) ⊕ ι)} (zero : M *ᵥ z=0) : z=0 := by
    let x := z ∘ Sum.inl
    let y := z ∘ Sum.inr
    have first : D *ᵥ x + C *ᵥ y = 0 := by
      ext i
      simpa [M,fromBlocks_mulVec,x,y,Function.comp_def] using congrFun zero (Sum.inl i)
    have last : Cᵀ *ᵥ x = 0 := by
      ext i
      simpa [M,fromBlocks_mulVec,x,Function.comp_def] using congrFun zero (Sum.inr i)
    have const := star_left_constant x last
    have sumC : Cᵀ *ᵥ 1 = 0 := by
      ext i
      simp [C,starIncidence,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,ZModModule.add_self]
    have zsum : (1 : Vec (ι ⊕ Unit)) ⬝ᵥ (C *ᵥ y) = 0 := by
      have pair := dotProduct_transpose_mulVec Cᵀ (1 : Vec (ι ⊕ Unit)) y
      simpa [sumC] using pair
    have pair := congrArg (fun v : Vec (ι ⊕ Unit) => (1 : Vec (ι ⊕ Unit)) ⬝ᵥ v) first
    rw [dotProduct_add,zsum,add_zero,const,mulVec_smul,dotProduct_smul,odd] at pair
    simp only [smul_eq_mul,mul_one,dotProduct_zero] at pair
    have xz : x=0 := by simpa [pair] using const
    have yz := star_injective y (by simpa [xz,C] using first)
    ext i
    cases i with
    | inl j => exact congrFun xz j
    | inr j => exact congrFun yz j
  apply (isUnit_iff_isUnit_det M).mp
  apply (mulVec_injective_iff_isUnit (A:=M)).mp
  intro x y eq
  exact sub_eq_zero.mp (vanish (by rw [mulVec_sub,eq,sub_self]))

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.star_injective
#print axioms Sun28.SupportMatrix.star_left_constant
#print axioms Sun28.SupportMatrix.initial_minor
