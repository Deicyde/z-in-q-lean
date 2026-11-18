import PicardConjugateEnd
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! A division-quaternion presentation of the full geometric rational endomorphism algebra. -/
namespace ZOverQ.Qualitative.PicardPrym
open ZInQBlueprint.AbelianModel PicardConjugation PicardConjugateEnd
open scoped ZInQBlueprint.NormalDescent TensorProduct
noncomputable section

/-- A presentation of the entire rational endomorphism algebra over L,
together with surjectivity after passage to the algebraic closure. -/
structure QuaternionModel {L : FiniteGaloisIntermediateField ℚ Qbar} (Y : GroupScheme L) where
  D : Type
  [division : DivisionRing D]
  [rationalAlgebra : Algebra ℚ D]
  presentation : D ≃ₐ[ℚ] QEnd Y
  i : D
  j : D
  sq_i : i*i = algebraMap ℚ D (-3)
  sq_j : j*j = algebraMap ℚ D 2
  skew : j*i = -(i*j)
  generates : Algebra.adjoin ℚ ({i,j} : Set D) = ⊤
  geometric_surjective : Function.Surjective (change L.toIntermediateField.val.toRingHom Y)

attribute [instance] QuaternionModel.division QuaternionModel.rationalAlgebra

end
end ZOverQ.Qualitative.PicardPrym
#print axioms ZOverQ.Qualitative.PicardPrym.QuaternionModel.geometric_surjective
