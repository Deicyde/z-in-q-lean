import Std

namespace SquaredAbscissa

open Lean.Grind

/-- Norm of the numerator on u² = t − D t³. -/
theorem translate_norm {K : Type} [CommRing K] (a b c D t : K)
    (hc : a^2 = c) (hb : b^2 = c^2 - D) :
    (c*(1-D*t^2)+b^2*t)^2 - (-2*a*b)^2*(t-D*t^3)
      = (c+D*t)^2*(1-c*t)^2 := by grobner

/-- The two coefficients after reduction in the basis 1,u. -/
theorem collect_square {K : Type} [CommRing K] (n e u w j : K) (hw : u^2=w) :
    (n+e*u)^2*(j-u) = (n^2+e^2*w)*j-2*n*e*w +
      (2*n*e*j-(n^2+e^2*w))*u := by grobner

/-- The quadratic row recovers the square, including its literal rational witnesses. -/
theorem square_row {K : Type} [Field K] (B A F Y : K)
    (hB : B ≠ 0) (hF : B*F^2=A) : B*Y=A ↔ Y=F^2 := by
  have h := Field.mul_inv_cancel hB
  constructor <;> intro he <;> grobner

/-- A zero coefficient in the new row forces the right side to vanish. -/
theorem inconsistent_branch {K : Type} [CommRing K] (A B Y : K)
    (eqn : B*Y=A) (atZero : B=0) : A=0 := by grobner

#print axioms translate_norm
#print axioms collect_square
#print axioms square_row
#print axioms inconsistent_branch
end SquaredAbscissa
