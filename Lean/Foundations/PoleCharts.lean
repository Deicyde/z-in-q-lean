import Std

namespace PoleCharts
open Lean.Grind

def Old (B : Rat) : Prop := ∃ e s v p q : Rat,
    (1-e)*(1+3*e)=B*p^2 ∧ s*v=(289-B)*e ∧ (s-v)*(s+3*v)=B*q^2

def Short (B : Rat) : Prop := ∃ s v P q : Rat,
    ((289-B)-s*v)*((289-B)+3*s*v)=B*P^2 ∧ (s-v)*(s+3*v)=B*q^2

/-- Exact elimination of the intermediate variable, also at B=289. -/
theorem pole_iff (B : Rat) : Old B ↔ Short B := by
  constructor
  · rintro ⟨e,s,v,p,q,h₁,h₂,h₃⟩
    exact ⟨s,v,(289-B)*p,q,by grobner,h₃⟩
  · rintro ⟨s,v,P,q,h₁,h₂⟩
    by_cases hb : 289-B=0
    · have : B=289 := by grobner
      subst B
      have h17 : (17 : Rat) ≠ 0 := by grind
      have hi := Field.mul_inv_cancel h17
      refine ⟨0,0,0,1/17,0,?_,?_,?_⟩
      · simp only [Field.div_eq_mul_inv]
        grobner
      · grobner
      · grobner
    · have hi := Field.mul_inv_cancel hb
      refine ⟨s*v/(289-B),s,v,P/(289-B),q,?_,?_,h₂⟩ <;>
        simp only [Field.div_eq_mul_inv] <;> grobner

/-- The two like factors of two binary quartics descend to symmetric variables. -/
theorem unordered_factors {R : Type} [CommRing R] (b a c e f : R) :
    let A:=a*e
    let J:=a*f+c*e
    let C:=c*f
    (c^2-b*a^2)*(f^2-b*e^2)=(C+b*A)^2-b*J^2 ∧
    (c^2+3*b*a^2)*(f^2+3*b*e^2)=(C-3*b*A)^2+3*b*J^2 ∧
    J^2-4*A*C=(a*f-c*e)^2 := by dsimp; constructor; grobner; constructor <;> grobner

theorem splitting_discriminant {R : Type} [CommRing R] (b u v t : R) :
    b*((u*t+v*t)^2-4*t^2*(u^2-b)) =
    b*t^2*(4*b-(u-v)*(3*u+v)) := by grobner

theorem raw_point {K : Type} [Field K] (b θ : K) (h : b+289*θ=289) :
    17^2-θ*17^2=b*(1+3*θ*0^2) := by grobner

/-- The second intersection with a line through a chosen norm point. -/
theorem secant {R : Type} [CommRing R] (b θ r s i j : R)
    (h : r^2-θ*s^2=b) :
    let M:=i^2-θ*j^2-3*b*θ
    let N:=2*(θ*s*j-r*i)
    (r*M+i*N)^2-θ*(s*M+j*N)^2=b*(M^2+3*θ*N^2) := by dsimp; grobner

def cubic {R : Type} [CommRing R] (z : R) := z*(z-1)*(z+3)

theorem signed_factors {R : Type} [CommRing R] (z : R) :
    -12*cubic z-(z^2+3)^2=-(z^2+6*z-3)^2 ∧
    -12*cubic z+3*(z^2+3)^2=3*(z^2-2*z-3)^2 := by
  unfold cubic
  constructor <;> grobner

theorem signed_ratio {R : Type} [CommRing R] (z θ : R) (h : (1+3*θ)*z= -(3+θ)) :
    θ*cubic (-3*z)=9*cubic z := by unfold cubic; grobner

end PoleCharts
#print axioms PoleCharts.pole_iff
#print axioms PoleCharts.unordered_factors
#print axioms PoleCharts.splitting_discriminant
#print axioms PoleCharts.raw_point
#print axioms PoleCharts.secant
#print axioms PoleCharts.signed_factors
#print axioms PoleCharts.signed_ratio
