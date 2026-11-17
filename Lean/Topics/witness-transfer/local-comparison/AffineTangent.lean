import PhysicalCurve

namespace WitnessTransfer
open Lean.Grind

/-- The dimensionless slope ell=lambda*x/y, abscissa ratio a=x(2P)/x(P),
and ordinate ratio b=y(2P)/y(P). -/
theorem normalized_tangent {A : Type} [CommRing A] (w ell a b z z2 : A)
    (slope : 2*(1-w)*ell=3-w) (abscissa : a=ell^2*(1-w)-2)
    (ordinate : b=ell*(1-a)-1) (parameter : z2*b=z*a) (hw : unit (1+w)) :
    z2*(1-6*w+w^2)=2*z*(1-w^2) := by
  have ha : 4*(1-w)*a=(1+w)^2 := by
    calc
      _=(2*(1-w)*ell)^2-8*(1-w) := by rw [abscissa];grobner
      _=_ := by rw [slope];grobner
  have hb : 8*(1-w)^2*b=(1+w)*(1-6*w+w^2) := by
    calc
      _=(2*(1-w)*ell)*(4*(1-w)-4*(1-w)*a)-8*(1-w)^2 := by rw [ordinate];grobner
      _=_ := by rw [slope,ha];grobner
  apply cancel_unit hw
  calc
    _=z2*(8*(1-w)^2*b) := by rw [hb];grobner
    _=(8*(1-w)^2)*(z*a) := by rw [← parameter];grobner
    _=2*z*(1-w)*(4*(1-w)*a) := by grobner
    _=_ := by rw [ha];grobner

private theorem cancelF {K : Type} [Field K] {k x y : K} (h : k≠0) (e : k*x=k*y) : x=y := by
  exact cancel_unit ⟨k⁻¹,Field.inv_mul_cancel h⟩ e

/-- The usual affine tangent and short-Weierstrass equation imply the z-ratio,
including at all formal affine points where the displayed ratios are units. -/
theorem affine_tangent {K : Type} [Field K] (x y D slope x2 y2 z z2 w ell a b : K)
    (hx : x≠0) (hy : y≠0) (unitw : 1+w≠0)
    (curve : y^2=x^3-D*x) (line : 2*y*slope=3*x^2-D)
    (doubleX : x2=slope^2-2*x) (doubleY : y2=slope*(x-x2)-y)
    (coord : w*x^2=D) (scoord : ell*y=slope*x) (acoord : a*x=x2) (bcoord : b*y=y2)
    (zcoord : z*y= -x) (z2coord : z2*y2= -x2) :
    z2*(1-6*w+w^2)=2*z*(1-w^2) := by
  have hc : x^3*(1-w)=y^2 := by rw [curve,← coord];grobner
  have hx3 : x^3≠0 := by
    intro k
    have h : x*x*x=0 := by simpa only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] using k
    rcases Field.of_mul_eq_zero h with q|q
    · rcases Field.of_mul_eq_zero q with v|v <;> exact hx v
    · exact hx q
  apply normalized_tangent w ell a b z z2 _ _ _ _ ⟨_,Field.inv_mul_cancel unitw⟩
  · apply cancelF hx3
    calc x^3*(2*(1-w)*ell) = 2*(x^3*(1-w))*ell := by grobner
         _=2*y*(ell*y) := by rw [hc];grobner
         _=x*(2*y*slope) := by rw [scoord];grobner
         _=x^3*(3-w) := by rw [line,← coord];grobner
  · apply cancelF hx3
    calc x^3*a=x^2*x2 := by rw [← acoord];grobner
         _= (slope*x)^2-2*x^3 := by rw [doubleX];grobner
         _= (x^3*(1-w))*ell^2-2*x^3 := by rw [hc,← scoord];grobner
         _=_ := by grobner
  · apply cancelF hy
    calc y*b=y2 := by rw [CommSemiring.mul_comm,bcoord]
         _=(slope*x)*(1-a)-y := by rw [doubleY,← acoord];grobner
         _=_ := by rw [← scoord];grobner
  · apply cancelF hy
    calc y*(z2*b)=z2*y2 := by rw [← bcoord];grobner
         _= -x2 := z2coord
         _=(z*y)*a := by rw [zcoord,← acoord];grobner
         _=_ := by grobner

#print axioms normalized_tangent
#print axioms affine_tangent
end WitnessTransfer
