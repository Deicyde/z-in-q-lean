module

public import Std

@[expose] public section

namespace PrescribedFibres
open Lean.Grind

/-- Two coordinates of the triple product, using the known norm of its first factor. -/
theorem norm_triple {R : Type} [CommRing R] (u v s t X Y E G norm : R)
    (he : E=u*s+2*v*t+X) (hg : G=u*t+v*s+Y) (hn : norm=u^2-2*v^2) :
    u*E-2*v*G-norm*s+4*v*Y=u*X+2*v*Y ∧
    v*E-u*G+norm*t+2*u*Y=v*X+u*Y ∧ E-u*s-2*v*t=X := by
  rw [he,hg,hn]
  constructor
  · grobner
  constructor <;> grobner

/-- The parametrization of (z−1)(z+3)=βd², with denominators cleared. -/
theorem abscissa_conic {R : Type} [CommRing R] (β a b : R) :
    ((b^2+3*β*a^2)-(b^2-β*a^2))*((b^2+3*β*a^2)+3*(b^2-β*a^2)) =
    β*(4*a*b)^2 := by grobner

/-- The form product is a square when the two conics supply their points. -/
theorem prescribed_product {R : Type} [CommRing R] (β θ s h d r u k v : R)
    (hh : s^2-β=h^2) (hr : s^2+3*β=d*r^2)
    (hv : 1-β*u^2=θ*v^2) (hk : 1+3*β*u^2=d*k^2) :
    θ*((s^2-β)*(s^2+3*β))*((1-β*u^2)*(1+3*β*u^2)) =
    (θ*h*d*r*k*v)^2 := by
  rw [hh,hr,hv,hk]
  grobner

/-- The concrete prepared conic and the two squareclasses, over the integers. -/
theorem fibre_409 :
    (17:Int)*24^2+409=101^2 ∧
    ((6:Int)^2-17)*(6^2+51)=1653 ∧
    ((81:Int)^2-17)*(81^2+51)=409*1653*8^2 := by decide

#print axioms norm_triple
#print axioms abscissa_conic
#print axioms prescribed_product
#print axioms fibre_409
end PrescribedFibres
