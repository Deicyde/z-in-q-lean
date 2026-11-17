import Std

namespace OrbitIdentification.Anchor
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- The reciprocal square root has the same tangent parameter up to a
    unit whose square is congruent to one throughout the formal branch. -/
theorem reciprocal_root_parameter {K : Type} [Field K] {D x y g z : K}
    (curve : y^2=x^3-D*x) (reciprocal : x*g^2=1) (parameter : z*y= -x) :
    g^2=z^2*(1-D*g^4) := by
  have clear : y^2*g^4=x*(1-D*g^4) := by grobner
  have eq : (z*y)^2*g^4=z^2*x*(1-D*g^4) := by rw [show (z*y)^2=z^2*y^2 by grobner]; grobner
  rw [parameter] at eq
  have inv : x*(g^2)=1 := reciprocal
  grobner

abbrev F9 := Fin 3 × Fin 3
private def times3 (a b : F9) : F9 :=
  (a.1*b.1+2*a.2*b.2,a.1*b.2+a.2*b.1)

/-- Reduction of the doubling formula using x(P)=ρ, y(P)/3=1+2ρ, D=2
    in the residue field of the inert prime. -/
theorem base_residue :
    let x : F9 := (0,1)
    let denominator : F9 := ((times3 x x).1+2,(times3 x x).2)
    denominator=(1,0) ∧ times3 (2,1) denominator=times3 (2,0) (1,2) := by decide +kernel

/-- The two signs of the normalized reciprocal square root. In particular
    both coordinates are nonzero when the multiplier is a three-adic unit. -/
theorem signed_root_residue (a b u : Fin 3) (unit : u≠0)
    (h : times3 (a,b) (a,b)=times3 (2*u,u) (2*u,u)) :
    ((a=2*u ∧ b=u) ∨ (a= -2*u ∧ b= -u)) ∧ a≠0 ∧ b≠0 := by
  revert a b u
  decide +kernel

end OrbitIdentification.Anchor

#print axioms OrbitIdentification.Anchor.reciprocal_root_parameter
#print axioms OrbitIdentification.Anchor.base_residue
#print axioms OrbitIdentification.Anchor.signed_root_residue
