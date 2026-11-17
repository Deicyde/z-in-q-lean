import Std

namespace StructuralReduction.MarkedBase

open Lean.Grind

def quartic {R : Type} [CommRing R] (β a b : R) : R :=
  (β*a^2-b^2)*(β*a^2-9*b^2)

/-- Coordinates on the conic obtained by eliminating the twist parameter from
the two defining quadrics of the marked two-covering. -/
theorem conic {R : Type} [CommRing R] (β a b : R) :
    β*(4*(β*a^2+3*b^2)^2-(2*(β*a^2-3*b^2))^2) = 3*(4*β*a*b)^2 := by
  grobner

/-- A value of the binary quartic times a square supplies both marked
coordinates on the original elliptic two-covering. -/
theorem marked_cover {R : Type} [CommRing R] (β a b d h : R)
    (hval : d*h^2 = quartic β a b) :
    β*(β*a^2+3*b^2)^2-(4*β*a*b)^2 = β*d*h^2 ∧
    β*(2*(β*a^2-3*b^2))^2-(4*β*a*b)^2 = 4*(β*d)*h^2 := by
  unfold quartic at hval
  constructor <;> grobner

/-- The marked curve point has rational abscissa and both full descent classes. -/
theorem elliptic_point {R : Type} [CommRing R] (β l u v w : R)
    (h₁ : β*u^2-w^2=l) (h₂ : β*v^2-w^2=4*l) :
    β*u^2-l=w^2 ∧ β*u^2+3*l=β*v^2 ∧
    (β*u*v*w)^2=(β*u^2)*(β*u^2-l)*(β*u^2+3*l) := by
  have h₃ : β*u^2-l=w^2 := by grobner
  have h₄ : β*u^2+3*l=β*v^2 := by grobner
  exact ⟨h₃,h₄,by rw [h₃,h₄]; grobner⟩

/-- The norm from the first quadratic field on each of the two factors. -/
theorem quartic_norm {R : Type} [CommRing R] (β a b : R) :
    quartic β a b = (3*b^2+β*a^2)^2-β*(4*a*b)^2 := by
  unfold quartic
  grobner

#print axioms conic
#print axioms marked_cover
#print axioms elliptic_point
#print axioms quartic_norm

end StructuralReduction.MarkedBase
