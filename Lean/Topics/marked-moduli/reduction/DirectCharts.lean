import IntegralSextic
/-! Divided local equations of the monic rational sextic. -/
namespace ZInQBlueprint.DirectCharts
noncomputable section
open Polynomial ZInQBlueprint.IntegralSextic
variable {R : Type*} [CommRing R]
def monicSextic (t : R) : R[X] := form 1 (C t) X 1

theorem monic_eval (t x : R) : (monicSextic t).eval x = form 1 t x 1 := by
  simp [monicSextic,form,alpha,beta,gamma]

theorem monic_coeffs (t : R) : monicSextic t = X^6+C (9-t)*X^5+C (27-9*t)*X^4+
    C (t^2-32*t+27)*X^3+C (6*t^2-54*t)*X^2+C (12*t^2-36*t)*X+C (8*t^2) := by
  simp [monicSextic,form,alpha,beta,gamma,map_ofNat]; ring

theorem monic_six [Nontrivial R] (t : R) : (monicSextic t).Monic ∧ (monicSextic t).natDegree=6 := by
  rw [monic_coeffs]
  have h : (X ^ 6 + C (9-t)*X^5 + C (27-9*t)*X^4 + C (t^2-32*t+27)*X^3 + C (6*t^2-54*t)*X^2 + C (12*t^2-36*t)*X + C (8*t^2)).natDegree=6 := by compute_degree!
  refine ⟨?_,h⟩
  unfold Monic leadingCoeff
  rw [h]
  compute_degree!

def zeroDivided (a c U Y : R) :=
  let z := a+c*Y
  let v := Y*(2*a+3+c*Y)
  v^3-U*v*beta z 1*gamma z 1+c*U^2*(beta z 1)^3

theorem zero_divided {a : R} (ha : alpha a 1=0) (c U Y : R) :
    form 1 (c^2*U) (a+c*Y) 1 = c^3*zeroDivided a c U Y := by
  have h : alpha (a+c*Y) 1=c*(Y*(2*a+3+c*Y)) := by
    unfold alpha at ha ⊢; linear_combination ha
  unfold form zeroDivided; rw [h]; ring

theorem zero_reduction (U Y : R) :
    zeroDivided 0 0 U Y=27*Y^3-36*U*Y ∧ zeroDivided (-3) 0 U Y= -27*Y^3-9*U*Y := by
  unfold zeroDivided beta gamma; constructor <;> ring

def q (e x : R) := x^2+(3+e)*x+3*(1+e)
def slope (e x : R) := 2*x+3+e
def variation (e x : R) := -alpha x 1*beta x 1*gamma x 1-6*e*(beta x 1)^3
theorem pole_cube {e : R} (he : e^2 = -3) (x : R) : form 1 (-3*e) x 1 = (q e x)^3 := by
  have he3 : e^3 = -3*e := by linear_combination e*he
  unfold form q alpha beta gamma
  ring_nf; simp only [he,he3]; ring

theorem variation_identity (e b x : R) : form 1 (-3*e+b) x 1 =
    form 1 (-3*e) x 1 + b*variation e x+b^2*(beta x 1)^3 := by
  unfold form variation; ring

def poleDivided (a e c U Y : R) :=
  let z := a+c*Y
  (Y*(slope e a+c*Y))^3+U*variation e z+c^3*U^2*(beta z 1)^3

theorem pole_divided {e a : R} (he : e^2= -3) (ha : q e a=0) (c U Y : R) :
    form 1 (-3*e+c^3*U) (a+c*Y) 1 = c^3*poleDivided a e c U Y := by
  rw [variation_identity,pole_cube he]
  have h : q e (a+c*Y)=c*(Y*(slope e a+c*Y)) := by
    unfold q slope at *; linear_combination ha
  rw [h]; unfold poleDivided; ring

theorem pole_reduction (a e U Y : R) : poleDivided a e 0 U Y = (slope e a)^3*Y^3 + U*variation e a := by
  simp [poleDivided]; ring

end
end ZInQBlueprint.DirectCharts
#print axioms ZInQBlueprint.DirectCharts.monic_eval
#print axioms ZInQBlueprint.DirectCharts.monic_coeffs
#print axioms ZInQBlueprint.DirectCharts.monic_six
#print axioms ZInQBlueprint.DirectCharts.zero_divided
#print axioms ZInQBlueprint.DirectCharts.zero_reduction
#print axioms ZInQBlueprint.DirectCharts.pole_cube
#print axioms ZInQBlueprint.DirectCharts.variation_identity
#print axioms ZInQBlueprint.DirectCharts.pole_divided
#print axioms ZInQBlueprint.DirectCharts.pole_reduction
