import GaussianCRT
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.StdBasis

namespace Sun28.Reciprocity
noncomputable section

def gaussianPair : GaussianInt ≃+ (Fin 2 → ℤ) where
  toFun z := ![z.re,z.im]
  invFun f := ⟨f 0,f 1⟩
  left_inv _:=rfl
  right_inv f:=by funext j;fin_cases j <;> rfl
  map_add' x y:=by funext j;fin_cases j <;> rfl

def gaussianBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map gaussianPair.toIntLinearEquiv.symm

local instance : Module.Free ℤ GaussianInt := Module.Free.of_basis gaussianBasis
local instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis gaussianBasis

theorem multiplication_norm (z:GaussianInt) : Algebra.norm ℤ z=z.norm := by
  rw [Algebra.norm_eq_matrix_det gaussianBasis,Matrix.det_fin_two]
  have h (j k:Fin 2) : Algebra.leftMulMatrix gaussianBasis z j k =
      gaussianPair (z*gaussianPair.symm (Pi.single k 1)) j := by
    simp [Algebra.leftMulMatrix_apply,LinearMap.toMatrix_apply,gaussianBasis]
  rw [h,h,h,h]
  have b0 : gaussianPair.symm (Pi.single (0:Fin 2) 1) = 1 := by
    apply Zsqrtd.ext <;> decide
  have b1 : gaussianPair.symm (Pi.single (1:Fin 2) 1) = ⟨0,1⟩ := by
    apply Zsqrtd.ext <;> decide
  rw [b0,b1,mul_one]
  change z.re * (z.re*1+z.im*0) - (z.re*0+(-1)*z.im*1)*z.im = _
  simp [Zsqrtd.norm_def]


theorem quotient_card (z:GaussianInt) :
    Nat.card (GaussianInt ⧸ principal z)=z.norm.natAbs := by
  change Ideal.absNorm (principal z)=_
  rw [Ideal.absNorm_span_singleton,multiplication_norm]

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.multiplication_norm
#print axioms Sun28.Reciprocity.quotient_card
