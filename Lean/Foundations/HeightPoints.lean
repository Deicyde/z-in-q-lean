import Std

namespace HeightPoints

open Lean.Grind

/-- Subtracting two Gaussian norms gives an affine line in the second generator. -/
theorem gaussian_difference {A : Type} [CommRing A] (x y g r s : A) :
    (x+g*r)^2+(y+g*s)^2-(x^2+y^2) =
      2*g*(r*x+s*y)+g^2*(r^2+s^2) := by grobner

/-- Numerators of the two conics after rational parametrization. -/
theorem parameter_factorization {A : Type} [CommRing A] (b k : A) :
    (1-3*b*k^2)^2-b*(2*k)^2 = (1-b*k^2)*(1-9*b*k^2) ∧
    (1+3*b*k^2)^2-(1-3*b*k^2)^2 = 3*b*(2*k)^2 := by
  constructor <;> grobner

/-- The two squareclasses and the second curve equation with denominators cleared. -/
theorem second_twist {A : Type} [CommRing A] (b u w d v : A)
    (hw : w^2=1+3*b*u^2) (hd : d*v^2=1-b*u^2) :
    b*w^2-b*d*v^2=(2*b*u)^2 ∧ b*w^2+3*b*d*v^2=4*b ∧
    (4*b^2*u*w)^2=(b*w^2)*(b*w^2-b*d*v^2)*(b*w^2+3*b*d*v^2) := by
  have hz : b*d*v^2=b*(1-b*u^2) := by
    calc b*d*v^2 = b*(d*v^2) := by grobner
         _ = _ := by rw [hd]
  have h₁ : b*w^2-b*d*v^2=(2*b*u)^2 := by rw [hz, hw]; grobner
  have h₂ : b*w^2+3*b*d*v^2=4*b := by
    calc b*w^2+3*b*d*v^2 = b*w^2+3*(b*d*v^2) := by grobner
         _ = _ := by rw [hz, hw]; grobner
  refine ⟨h₁, h₂, ?_⟩
  rw [h₁, h₂]
  grobner

/-- The two factors at a prepared pole witness. -/
theorem pole_factors {A : Type} [CommRing A] (B U w : A)
    (h : B*w^2 = B+3*U^2) :
    (B*w)^2-B*(B-U^2)=4*B*U^2 ∧
    (B*w)^2+3*B*(B-U^2)=4*B^2 := by
  constructor <;> grobner

#print axioms gaussian_difference
#print axioms parameter_factorization
#print axioms second_twist
#print axioms pole_factors
end HeightPoints
