import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace ZInQBlueprint.WildLevel
open Matrix
noncomputable section

/-- Dimension four makes any embedding in two-by-two matrices surjective.
A nontrivial idempotent in the matrix algebra then contradicts division. -/
theorem no_split_matrix_action (B : Type*) [DivisionRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] (dim : Module.finrank ℚ B=4)
    (f : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) : False := by
  let e : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,0]
  have matrixDim : Module.finrank ℚ (Matrix (Fin 2) (Fin 2) ℚ)=4 := by simp [Module.finrank_matrix]
  have surj : Function.Surjective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (dim.trans matrixDim.symm)).mp f.injective
  obtain ⟨x,hx⟩:=surj e
  change f x=e at hx
  have idem : e*e=e := by ext i j;fin_cases i <;> fin_cases j <;> norm_num [e,Matrix.mul_apply,Fin.sum_univ_two]
  have poly : x*(x-1)=0 := f.injective (by change f (x*(x-1))=f 0; rw [map_mul,map_sub,map_one,map_zero,hx,mul_sub,mul_one,idem,sub_self])
  rcases mul_eq_zero.mp poly with z|one
  · have he : (0:Matrix (Fin 2) (Fin 2) ℚ)=e := by simpa [z] using hx
    exact (by norm_num [e] : (0:ℚ)≠e 0 0) (congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℚ=>Z 0 0) he)
  · have one' := sub_eq_zero.mp one
    have he : (1:Matrix (Fin 2) (Fin 2) ℚ)=e := by simpa [one'] using hx
    exact (by norm_num [e] : (1:ℚ)≠e 1 1) (congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℚ=>Z 1 1) he)

/-- In semistable dimension two, restriction of the unital quaternion action
to the maximal torus would give precisely the forbidden representation. -/
theorem toric_rank_zero (B : Type*) [DivisionRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] (dim : Module.finrank ℚ B=4) (t:ℕ) (rank:t≤2)
    (action : 0<t → Nonempty (B →ₐ[ℚ] Matrix (Fin t) (Fin t) ℚ)) : t=0 := by
  by_contra! nz
  obtain ⟨f⟩:=action (by omega)

  interval_cases t
  · omega
  · have bound:=LinearMap.finrank_le_finrank_of_injective (f:=f.toLinearMap) f.injective
    simp [dim,Module.finrank_matrix] at bound
  · exact no_split_matrix_action B dim f

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.no_split_matrix_action
#print axioms ZInQBlueprint.WildLevel.toric_rank_zero
