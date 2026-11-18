module

public import Std

@[expose] public section

namespace WeakFibre
open Lean.Grind

/-- The integral matrix fixes the positive binary norm up to its determinant. -/
theorem norm_transport {R : Type} [CommRing R] (b i j a v : R) :
    (j*v-3*b*i*a)^2+3*b*(j*a+i*v)^2 =
    (j^2+3*b*i^2)*(v^2+3*b*a^2) := by grobner

theorem inverse_transport {R : Type} [CommRing R] (b i j a v : R) :
    let c := j*a+i*v
    let d := j*v-3*b*i*a
    j*c-i*d=(j^2+3*b*i^2)*a ∧ j*d+3*b*i*c=(j^2+3*b*i^2)*v := by
  dsimp
  constructor <;> grobner

theorem weak_quartic {R : Type} [CommRing R] (b i j a v θ : R) :
    let c := j*a+i*v
    let d := j*v-3*b*i*a
    θ*(v^2-b*a^2)*(v^2+3*b*a^2)*(d^2-b*c^2)*(d^2+3*b*c^2) =
      θ*(j^2+3*b*i^2)*(v^2-b*a^2)*(d^2-b*c^2)*(v^2+3*b*a^2)^2 := by
  dsimp
  grobner

theorem coefficient_test {R : Type} [CommRing R] (b i j : R)
    (h : 8*b^2*i^2 ≠ 0) :
    9*b^2*i^2-b*j^2 ≠ -b*(j^2-b*i^2) := by
  intro e
  apply h
  grobner

theorem norm_point {R : Type} [CommRing R] (b h u j i v : R)
    (hq : h = u^2+3*v^2) (hp : h = j^2+3*b*i^2) :
    (u*j-h)^2-b*(3*i*v)^2=h*(u-j)^2 := by grobner

theorem parametric_norm {R : Type} [CommRing R] (j t b : R)
    (hj : 2*j=12*t^2+1-3*b) :
    j^2+3*b=(j-1)^2+3*(2*t)^2 := by grobner

/-- Splitting a nonzero product into two squareclasses, with the inverses explicit. -/
theorem split_iff {R : Type} [CommRing R] (b f g i j : R)
    (hb : b*i=1) (hf : f*j=1) :
    (∃ y : R, y^2=b*f*g) ↔
    ∃ d s t : R, f=d*s^2 ∧ g=b*d*t^2 := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨f,1,i*j*y,?_,?_⟩ <;> grobner
  · rintro ⟨d,s,t,hs,ht⟩
    exact ⟨b*d*s*t, by grobner⟩

#print axioms norm_transport
#print axioms inverse_transport
#print axioms weak_quartic
#print axioms coefficient_test
#print axioms norm_point
#print axioms parametric_norm
#print axioms split_iff
end WeakFibre
