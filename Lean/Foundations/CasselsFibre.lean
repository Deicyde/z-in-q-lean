import Std
namespace CasselsFibre
open Lean.Grind

/-- Integral coordinates of a tangent point on the third diagonal conic. -/
theorem norm_tangent {R : Type} [CommRing R] (β θ a v c : R)
    (hn : c^2 = β*a^2 + θ*v^2) :
    (c^2+β*a^2)^2 - θ*(c*v)^2 = a^2*(3*β*θ*v^2+(2*β*a)^2) := by
  grobner

theorem tangent_product {R : Type} [CommRing R] (θ h s u z M t : R)
    (hp : h^2-θ*s^2 = M) (hc : u^2-θ*z^2 = M*t^2) :
    (h*u-θ*s*z-M*t)*(h*u-θ*s*z+M*t) = θ*(h*z-s*u)^2 := by
  grobner

/-- The rational conic point used for all nonsplit places has t = 2. -/
theorem local_conic {R : Type} [CommRing R] (β v : R) :
    (v*(1+3*β))^2 - (v*(1-3*β))^2 = (3*β*v^2)*2^2 := by grobner

theorem conic_parameter {R : Type} [CommRing R] (β a c s w : R) :
    let X := s^2+3*β*w^2
    let Y := β*a*(s^2-3*β*w^2)-6*β*c*s*w
    let Z := c*(s^2-3*β*w^2)+2*β*a*s*w
    Y^2+3*β*Z^2 = ((β*a)^2+3*β*c^2)*X^2 := by
  dsimp
  grobner

theorem split_quartic {R : Type} [CommRing R] (β a c s w : R) :
    let X := s^2+3*β*w^2
    let Y := β*a*(s^2-3*β*w^2)-6*β*c*s*w
    (2*β*a*X)^2-Y^2 = 3*β^2*(a*s^2+6*c*s*w+9*β*a*w^2)*(a*s^2-2*c*s*w+β*a*w^2) := by
  dsimp
  grobner

theorem two_norm_identities {R : Type} [CommRing R] (β a b c d : R) :
    (b^2-β*a^2)*(d^2-β*c^2)=(b*d-β*a*c)^2-β*(c*b-a*d)^2 ∧
    (b^2+3*β*a^2)*(d^2+3*β*c^2)=(b*d+3*β*a*c)^2+3*β*(c*b-a*d)^2 := by
  constructor <;> grobner

/-- Clear the denominators of the sign-changing involution on the second pencil. -/
theorem sign_reversal {R : Type} [CommRing R] (β μ a b : R) :
    let u := β*μ*a-b
    let v := β*a-β*μ*b
    let h := β*(β*μ^2-1)
    v^2-β*u^2=h*(b^2-β*a^2) ∧
    β*μ*u-v=h*a ∧ β*u-β*μ*v=h*b := by
  dsimp
  constructor
  · grobner
  · constructor <;> grobner

/-- The two finite numerators after negating one exterior parameter. -/
theorem exterior_numerators {R : Type} [CommRing R] (s u : R) :
    (1-s*u)-s*(u-s)=1-2*s*u+s^2 ∧
    (1-s*u)+u*(u-s)=1-2*s*u+u^2 := by
  constructor <;> grobner

#print axioms sign_reversal
#print axioms exterior_numerators
#print axioms norm_tangent
#print axioms tangent_product
#print axioms local_conic
#print axioms conic_parameter
#print axioms split_quartic
#print axioms two_norm_identities
end CasselsFibre
