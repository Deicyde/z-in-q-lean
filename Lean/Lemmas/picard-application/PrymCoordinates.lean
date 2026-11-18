import PicardPrym
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The genus-two curve of Ritzenthaler and Romagny

Theorem 1.1 of Ritzenthaler–Romagny, Épijournal de Géométrie Algébrique 2
(2018), https://doi.org/10.46298/epiga.2018.volume2.3663, uses the matrix
whose rows are the coefficients of the three binary quadratic forms f,h,g.
Its inverse yields the three polynomials in the genus-two equation. The
following identities recover Laga–Shnidman, Remark 2.12, over the given
coefficient field.
-/
namespace ZOverQ.Qualitative.PrymCoordinates

open Polynomial PicardPrym
noncomputable section
variable {K : Type*} [Field K]

/-- Rows representing f = z(wz−x), h = −az² and g = x²+wxz+w²z²,
in the ordered basis x²,xz,z². -/
def coefficients (a w : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0,-1,w; 0,0,-a; 1,w,w^2]

def inverseCoefficients (a w : K) : Matrix (Fin 3) (Fin 3) K :=
  !![w,2*w^2/a,1; -1,-w/a,0; 0,-1/a,0]

private def form (A : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) (x z : K) : K :=
  A i 0*x^2+A i 1*x*z+A i 2*z^2

/-- The ambient quartic is the homogeneous bielliptic Picard equation.
The matrix hypothesis in Theorem 1.1 is precisely a ≠ 0 here. -/
theorem quartic_data (a w : K) (ha : a ≠ 0) :
    (∀ x y z : K, y^4-form (coefficients a w) 1 x z*y^2+
      form (coefficients a w) 0 x z*form (coefficients a w) 2 x z =
        y^4+a*y^2*z^2+w^3*z^4-x^3*z) ∧
    (coefficients a w).det = a ∧ (coefficients a w)⁻¹ = inverseCoefficients a w := by
  refine ⟨?_,?_,?_⟩
  · intro x y z
    simp [form, coefficients]
    ring
  · simp [Matrix.det_fin_three,coefficients]
  · apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coefficients,inverseCoefficients,Matrix.mul_apply,Fin.sum_univ_succ] <;>
      field_simp <;> ring

/-- Columns of the inverse matrix define the polynomials A(T),B(T),C(T)
with the coefficient of T weighted by two as in Theorem 1.1. -/
private def column (M : Matrix (Fin 3) (Fin 3) K) (j : Fin 3) : K[X] :=
  C (M 0 j)+2*C (M 1 j)*X+C (M 2 j)*X^2

def rrPolynomial (a w : K) : K[X] :=
  let m := (coefficients a w)⁻¹
  column m 1*((column m 1)^2-column m 0*column m 2)

/-- The exact change (T,Y)=(wx,(w²/a)y) identifies the two published
genus-two equations over the ground field whenever aw is nonzero. -/
theorem sextic_substitution [CharZero K] (a w : K) (ha : a ≠ 0) (hw : w ≠ 0) :
    (rrPolynomial a w).comp (C w*X) = C ((w^2/a)^2)*publishedPolynomial a w := by
  apply Polynomial.funext
  intro x
  rw [rrPolynomial,(quartic_data a w ha).2.2,eval_comp]
  simp [column,inverseCoefficients,publishedPolynomial,PicardLocal.quadratic]
  field_simp [ha,hw]
  ring

end
end ZOverQ.Qualitative.PrymCoordinates

#print axioms ZOverQ.Qualitative.PrymCoordinates.quartic_data
#print axioms ZOverQ.Qualitative.PrymCoordinates.sextic_substitution
