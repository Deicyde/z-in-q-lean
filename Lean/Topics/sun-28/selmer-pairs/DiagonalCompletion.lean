import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic

namespace Sun28.SupportMatrix
open Matrix
variable {K : Type*} [Field K]

/-- Any finite matrix can be made unimodular by changing only its diagonal. -/
theorem complete_diagonal (n : ℕ) (M : Matrix (Fin n) (Fin n) K) :
    ∃ D : Matrix (Fin n) (Fin n) K, D.det = 1 ∧ ∀ i j, i ≠ j → D i j = M i j := by
  classical
  induction n with
  | zero =>
    exact ⟨M, by simp, fun _ _ _ => rfl⟩
  | succ n ih =>
    let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
    let B := M.submatrix e e
    obtain ⟨A, ha, off⟩ := ih B.toBlocks₁₁
    let _ : Invertible A := (isUnit_iff_isUnit_det A).mpr (ha ▸ isUnit_one) |>.invertible
    let E := fromBlocks A B.toBlocks₁₂ B.toBlocks₂₁ (1 + B.toBlocks₂₁ * ⅟A * B.toBlocks₁₂)
    have det : E.det = 1 := by simp [E,det_fromBlocks₁₁,ha]
    refine ⟨E.submatrix e.symm e.symm, (det_submatrix_equiv_self _ _).trans det, ?_⟩
    intro i j hij
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    simp only [submatrix_apply, Equiv.symm_apply_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact off i j (fun h => hij (by rw [h]))
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j => exact False.elim (hij (by rw [Subsingleton.elim i j]))

/-- Starting with any invertible grounded minor, the free new diagonals can
be chosen together while every prescribed off-diagonal entry is retained. -/
theorem complete_extension {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (A : Matrix ι ι K) (B : Matrix ι (Fin n) K) (C : Matrix (Fin n) ι K)
    (M : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det) :
    ∃ D : Matrix (Fin n) (Fin n) K,
      (fromBlocks A B C D).det = A.det ∧ ∀ i j, i ≠ j → D i j = M i j := by
  classical
  let _ : Invertible A := ((isUnit_iff_isUnit_det A).mpr hA).invertible
  let S := C * ⅟A * B
  obtain ⟨T, det, off⟩ := complete_diagonal n (M-S)
  refine ⟨T+S, ?_, ?_⟩
  · rw [det_fromBlocks₁₁]
    change A.det*(T+S-S).det = A.det
    simp [det]
  · intro i j hij
    change T i j + S i j = M i j
    rw [off i j hij]
    exact sub_add_cancel _ _

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.complete_diagonal
#print axioms Sun28.SupportMatrix.complete_extension
