import Std

namespace QuarticScalar
open Lean.Grind Std

theorem interpolation {K : Type} [CommRing K] (t : K) :
    let f := t*(t-1)
    let g := (t-2401)*(32*t+343)*(2*t-1)
    let j := -900000+1723543*t
    let k := 823543-1723543*t
    let h := 810000000000-131776927151*t
    let c : K := -741188700000
    let d : K := 1723543
    let B := -8433723337664*t^2+20206593900036846*t+103236940352615993
    f*B=h*g-c*j ∧ j^2=h+d^2*f ∧ j*k=c-d^2*f := by
  dsimp
  constructor
  · grobner
  · constructor <;> grobner

/-- The product c*h is the exact factor introduced by the quadratic residual. -/
theorem residual_identity {K : Type} [CommRing K] (f g j k h c d B v z : K)
    (vdef : f*v=j) (quotient : f*B=h*g-c*j)
    (square : j^2=h+d^2*f) (mixed : j*k=c-d^2*f) :
    f^2*(c*z*(B+c*v)-(c*v^2-d^2*(k*v+d^2))) = c*h*(z*f*g-1) := by
  have left : f*(B+c*v)=h*g := by grobner
  have right : f^2*(c*v^2-d^2*(k*v+d^2))=c*h := by
    calc
      _ = c*(f*v)^2-d^2*f*((f*v)*k+d^2*f) := by grobner
      _ = c*h := by rw [vdef,square,mixed]; grobner
  calc
    _ = c*z*f*(f*(B+c*v))-f^2*(c*v^2-d^2*(k*v+d^2)) := by grobner
    _ = _ := by rw [left,right]; grobner

theorem exceptional_factor (x : Rat) :
    810000000000-131776927151*(51*x^2+2504)<0 := by
  have nonneg : 0 ≤ x^2 := OrderedRing.sq_nonneg
  grind

theorem normalizer_iff {K : Type} [Field K] (f g j k h c d B v z : K)
    (hf : f ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0)
    (vdef : f*v=j) (quotient : f*B=h*g-c*j)
    (square : j^2=h+d^2*f) (mixed : j*k=c-d^2*f) :
    c*z*(B+c*v)=c*v^2-d^2*(k*v+d^2) ↔ z*f*g=1 := by
  have iden := residual_identity f g j k h c d B v z vdef quotient square mixed
  have ch : c*h ≠ 0 := fun e => (Field.of_mul_eq_zero e).elim hc hh
  have ff : f^2 ≠ 0 := by
    intro e
    have zf : f*f=0 := by grobner
    exact (Field.of_mul_eq_zero zf).elim hf hf
  constructor
  · intro e
    have zero : c*h*(z*f*g-1)=0 := by rw [←iden,e]; grobner
    have right := (Field.of_mul_eq_zero zero).resolve_left ch
    grind
  · intro e
    rw [e] at iden
    have zero : f^2*(c*z*(B+c*v)-(c*v^2-d^2*(k*v+d^2)))=0 := by rw [iden]; grobner
    have right := (Field.of_mul_eq_zero zero).resolve_left ff
    grind

/-- Transport the three norm equations under w = R*W, including zeros of W. -/
theorem norm_equations {K : Type} [CommRing K] (R s a W b z0 z1 f m : K)
    (unit : s*R=1) :
    (a*R^4=z0+R*z1 ∧ W*R^4=a^2+R*f ∧ b=R*(R+m)*W^2) ↔
    (a*R^3=s*z0+z1 ∧ (R*W)*R^3=a^2+R*f ∧ b=(1+m*s)*(R*W)^2) := by
  constructor <;> intro ⟨e1,e2,e3⟩ <;> constructor
  · grobner
  · constructor <;> grobner
  · grobner
  · constructor <;> grobner

end QuarticScalar
#print axioms QuarticScalar.interpolation
#print axioms QuarticScalar.residual_identity
#print axioms QuarticScalar.exceptional_factor
#print axioms QuarticScalar.normalizer_iff
#print axioms QuarticScalar.norm_equations
