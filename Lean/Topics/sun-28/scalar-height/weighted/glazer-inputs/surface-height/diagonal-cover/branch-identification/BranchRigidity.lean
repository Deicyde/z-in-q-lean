import QuarticCoordinates
import Mathlib.GroupTheory.Perm.Fin

namespace ZInQBlueprint.BranchId
open Diagonal210
noncomputable section

private def rowMark (i : Fin 4) (j : Fin 3) : ℚ := mark (keep i j)

private theorem rigidity_table (i : Fin 4) (π : Equiv.Perm (Fin 3)) :
    (rowMark i (π 1)-rowMark i (π 0))*(rowMark i 2-rowMark i 0) =
      (rowMark i (π 2)-rowMark i (π 0))*(rowMark i 1-rowMark i 0) →
      π=1 := by
  revert i π
  decide +kernel

/-- Fixing the distinguished point at infinity and preserving the unordered
three other branch values fixes the common base coordinate. -/
theorem unique_affine_coordinate (i : Fin 4) (a b : ℚ) (π : Equiv.Perm (Fin 3))
    (sends : ∀ j, a*mark (keep i j)+b=mark (keep i (π j))) : a=1 ∧ b=0 ∧ π=1 := by
  change ∀ j,a*rowMark i j+b=rowMark i (π j) at sends
  have perm : π=1 := by
    apply rigidity_table
    rw [←sends 0,←sends 1,←sends 2]
    ring
  subst π
  have distinct : rowMark i 1-rowMark i 0 ≠ 0 := by fin_cases i <;> norm_num [rowMark,keep,mark]
  have s₀:=sends 0; have s₁:=sends 1
  change a*rowMark i 0+b=rowMark i 0 at s₀
  change a*rowMark i 1+b=rowMark i 1 at s₁
  have prod : (a-1)*(rowMark i 1-rowMark i 0)=0 := by linear_combination s₁-s₀
  have ha:=sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right distinct)
  exact ⟨ha,by rw [ha,one_mul] at s₀; linarith,rfl⟩

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.unique_affine_coordinate
