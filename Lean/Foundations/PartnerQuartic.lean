import Std

namespace PartnerQuartic
open Lean.Grind

/-- Cross multiplication for the projective map comparing two quadratic factors. -/
theorem mobius_difference {R : Type} [CommRing R] (a b c d u v s t : R) :
    (a*u+b*v)*(c*s+d*t) - (a*s+b*t)*(c*u+d*v) =
    (a*d-b*c)*(u*t-s*v) := by grobner

theorem quotient_product {K : Type} [Field K] (l h : K) (hh : h ≠ 0) :
    (l/h)*h^2 = l*h := by
  have hi := Field.mul_inv_cancel hh
  simp only [Field.div_eq_mul_inv]
  grobner

/-- Every slope gives a base point, including the two endpoints. -/
theorem base_section {R : Type} [CommRing R] (β a c : R) :
    let L := c^2-β*a^2
    let H := c^2+3*β*a^2
    let m := β*L*H
    let x := β*H^2
    let y := 4*β^2*a*c*H^2
    x-m = 4*β^2*a^2*H ∧ x+3*m = 4*β*c^2*H ∧ y^2 = x*(x-m)*(x+3*m) := by
  dsimp
  constructor
  · grobner
  constructor <;> grobner

/-- An elliptic point with the prescribed full squareclass. -/
theorem canonical_section {R : Type} [CommRing R] (β j : R) :
    let k := β*j^2
    let n := β*(k-1)*(k-9)
    let x := β*(k+3)^2
    let y := 8*β^2*j*(k+3)*(k-3)
    x-n = (4*β*j)^2 ∧ x+3*n = β*(2*(k-3))^2 ∧ y^2 = x*(x-n)*(x+3*n) := by
  dsimp
  constructor
  · grobner
  constructor <;> grobner

/-- Reverse parametrization away from the root ordinate. -/
theorem canonical_inverse {K : Type} [Field K] (β u v w m r : K) (hw : w ≠ 0)
    (h₁ : β*u^2-m=w^2) (h₂ : β*v^2=β*u^2+3*m) (hr : r*w=2*u+v) :
    w^2*((β*r^2-1)*(β*r^2-9)) = 16*β*r^2*m := by
  have hi := Field.mul_inv_cancel hw
  have h : β*r*(2*u-v)=3*w := by grobner
  have h' : 4*β*r*u=(β*r^2+3)*w := by grobner
  grobner

theorem integer_square_gap (k : Int) (hk : 17 ≤ k) :
    (k-6)^2 < (k-1)*(k-9) ∧ (k-1)*(k-9) < (k-5)^2 := by
  have h : (k-1)*(k-9)-(k-6)^2 = 2*k-27 := by grobner
  have e : (k-5)^2-(k-1)*(k-9)=16 := by grobner
  omega

theorem square_twist_iff {K : Type} [Field K] (a h : K) (hh : h ≠ 0) :
    (∃ y : K, y^2 = h^2*a) ↔ ∃ z : K, z^2 = a := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y/h, ?_⟩
    have hi := Field.mul_inv_cancel hh
    simp only [Field.div_eq_mul_inv]
    grobner
  · rintro ⟨z, hz⟩
    exact ⟨h*z, by grobner⟩

end PartnerQuartic
#print axioms PartnerQuartic.mobius_difference
#print axioms PartnerQuartic.quotient_product
#print axioms PartnerQuartic.base_section
#print axioms PartnerQuartic.canonical_section
#print axioms PartnerQuartic.canonical_inverse
#print axioms PartnerQuartic.integer_square_gap
#print axioms PartnerQuartic.square_twist_iff
