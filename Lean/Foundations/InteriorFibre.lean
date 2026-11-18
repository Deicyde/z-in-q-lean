module

public import Std

@[expose] public section

namespace InteriorFibre
open Lean.Grind

/-- The two positive factors on the symmetric surface coincide. -/
theorem equal_norms {R : Type} [CommRing R] (b x y : R) :
    (3*b*(x+y))^2 + 3*b*(1-3*b*x*y)^2 = 3*b*(1+3*b*x^2)*(1+3*b*y^2) ∧
    (3*b*(x-y))^2 + 3*b*(1+3*b*x*y)^2 = 3*b*(1+3*b*x^2)*(1+3*b*y^2) := by
  constructor <;> grobner

theorem symmetric_factors {R : Type} [CommRing R] (b x y : R) :
    let A := 1-9*b*x^2-9*b*y^2+9*b^2*x^2*y^2
    (3*b*(x+y))^2-b*(1-3*b*x*y)^2 = -b*(A-24*b*x*y) ∧
    (3*b*(x-y))^2-b*(1+3*b*x*y)^2 = -b*(A+24*b*x*y) := by
  dsimp
  constructor <;> grobner

theorem norm_parametrization {R : Type} [CommRing R] (b e f s w : R) :
    let y := f*(s^2+b*w^2)+2*e*s*w
    let z := e*(s^2+b*w^2)+2*b*f*s*w
    z^2-b*y^2=(e^2-b*f^2)*(s^2-b*w^2)^2 := by dsimp; grobner

/-- The conic and its binary quartic for the conductor-forty curve. -/
theorem small_conic {R : Type} [CommRing R] (s w : R) :
    let u := 149*(s^2+5*w^2)+452*s*w
    let v := 113*(s^2+5*w^2)+745*s*w
    5*u^2-4*v^2=59929*(s^2-5*w^2)^2 := by dsimp; grobner

theorem small_quartic {R : Type} [CommRing R] (s w : R) :
    let u := 149*(s^2+5*w^2)+452*s*w
    let v := 113*(s^2+5*w^2)+745*s*w
    v^2-u^2=((-36)*(s^2+5*w^2)+293*s*w)*(262*(s^2+5*w^2)+1197*s*w) := by
  dsimp
  grobner

theorem contact_gates {R : Type} [CommRing R] (b : R) :
    let u := b*(b-1)
    let v := u*(32*u-76457*b-823543)
    (2*b-1)*v = b*(b-1)*(b-2401)*(32*b+343)*(2*b-1) := by dsimp; grobner

theorem label_shear {R : Type} [CommRing R] (x : R) :
    204*(x+x^2)+2555=51*(2*x+1)^2+2504 := by grobner

#print axioms equal_norms
#print axioms symmetric_factors
#print axioms norm_parametrization
#print axioms small_conic
#print axioms small_quartic
#print axioms contact_gates
#print axioms label_shear
end InteriorFibre
