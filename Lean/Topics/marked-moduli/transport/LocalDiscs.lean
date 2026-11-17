import ClusterCharts
import Mathlib.Algebra.Polynomial.Taylor

/-! Integral equations for the two depth substitutions, valid in any commutative ring.
Taking R to be a polynomial ring gives the coefficientwise residual cubic. -/

namespace ZInQBlueprint.LocalDiscs
open Polynomial ZInQBlueprint.ClusterCharts ZInQBlueprint.SexticCalibration
noncomputable section
variable {R : Type*} [CommRing R]

private def atZero (a U y c : R) :=
  let q := (2*a+16)*y+c*y^2
  let x := a+c*y
  (-4*q^3+3*U*q*(x^2+32)*(x^2-16*x-32))

private def atPole (a U y c : R) :=
  729*(3*((2*a+2)*y+c*y^2)^3+U*firstPole (a+c*y))

/-- If s=c²U and a²+16a−32=0, divide by c³ on the disc x=a+cy.
The congruence includes the constant term at the middle root of the residual cubic. -/
theorem zero_disc {a : R} (ha : q₀ a = 0) (c U y : R) :
    ∃ e : R, (sextic (c^2*U)).eval (a+c*y) =
      c^3*(-4*(2*a+16)^3*y^3+U*slope₀ a*y)+c^4*e := by
  let x := a+c*y
  let S := (sextic (X : R[X])).eval (C x)
  obtain ⟨v,hv⟩ := exists_mul_sq_add_linear_part_eq_eval_add S 0 (c^2*U)
  have ev : S.eval (c^2*U) = (sextic (c^2*U)).eval x := by simp [S,sextic]
  rw [zero_add, ev, (zero_layers x).1, (zero_layers x).2] at hv
  have hq : q₀ x = c*((2*a+16)*y+c*y^2) := by
    unfold q₀ at ha ⊢
    dsimp [x]
    linear_combination ha
  have hd : c ∣ atZero a U y c - atZero a U y 0 := by
    simpa [atZero,mul_comm y c] using sub_dvd_eval_sub c 0 (atZero (C a) (C U) (C y) X)
  obtain ⟨b,hb⟩ := hd
  have he : (sextic (c^2*U)).eval x = c^3*atZero a U y c + c^4*(v*U^2) := by
    rw [← hv]
    simp only [first₀,hq,atZero,x]
    ring
  refine ⟨b+v*U^2, ?_⟩
  rw [he, show atZero a U y c = atZero a U y 0+c*b by linear_combination hb]
  simp [atZero,slope₀]
  ring

/-- If w=c³U and a²+2a−1=0, divide the integral reciprocal chart by c³. -/
theorem pole_disc {a : R} (ha : qPole a = 0) (c U y : R) :
    ∃ e : R, pole (a+c*y) (c^3*U) =
      c^3*(729*(3*(2*a+2)^3*y^3+U*firstPole a))+c^4*e := by
  let x := a+c*y
  let S := pole (C x) X
  obtain ⟨v,hv⟩ := exists_mul_sq_add_linear_part_eq_eval_add S 0 (c^3*U)
  have ev : S.eval (c^3*U) = pole x (c^3*U) := by simp [S,pole]
  rw [zero_add, ev, (pole_layers x).1, (pole_layers x).2] at hv
  have hq : qPole x = c*((2*a+2)*y+c*y^2) := by
    unfold qPole at ha ⊢
    dsimp [x]
    linear_combination ha
  have hd : c ∣ atPole a U y c - atPole a U y 0 := by
    simpa [atPole,firstPole,mul_comm y c] using sub_dvd_eval_sub c 0 (atPole (C a) (C U) (C y) X)
  obtain ⟨b,hb⟩ := hd
  have he : pole x (c^3*U) = c^3*atPole a U y c+c^6*(v*U^2) := by
    rw [← hv,hq]
    dsimp [atPole,x]
    ring
  refine ⟨b+c^2*v*U^2, ?_⟩
  rw [he, show atPole a U y c = atPole a U y 0+c*b by linear_combination hb]
  simp [atPole]
  ring

end
end ZInQBlueprint.LocalDiscs

#print axioms ZInQBlueprint.LocalDiscs.zero_disc
#print axioms ZInQBlueprint.LocalDiscs.pole_disc
