import SexticConjugation
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-! A rational binary sextic for the six-contact family. -/
namespace ZInQBlueprint.RationalModel
open ZInQBlueprint.SexticConjugation
noncomputable section
variable {R : Type*} [CommRing R]

theorem scaled_reversal (s a b l x z : R) (ht : (l*a)*(l*b)=9*s^2-32) :
    a^3*binary (-s) (l*b*z) x = b^3*binary s (l*a*x) z := by
  simp only [binary,neg_sq,← ht]
  ring

def equation (d r h x z : R) :=
  (2-d)^3*binary (d*r) (4*h*(2+d)*(x+d*z)) (x-d*z)

theorem invariant {d r h : R} (hd : d^2=6) (ht : 9*(d*r)^2-32 = -32*h^2) (x z : R) :
    equation (-d) r h x z = equation d r h x z := by
  have hb : (4*h*(2+d))*(4*h*(2-d))=9*(d*r)^2-32 := by
    rw [ht]
    linear_combination -16*h^2*hd
  have e := scaled_reversal (d*r) (2+d) (2-d) (4*h) (x+d*z) (x-d*z) hb
  simpa only [equation,neg_mul,sub_eq_add_neg,neg_neg] using e

theorem constant_norm {d : R} (hd : d^2=6) :
    ((2-d)^3)*((2+d)^3) = -8 := by
  rw [← mul_pow,show (2-d)*(2+d)= -2 by linear_combination -hd]
  norm_num

theorem change_of_variables_det {K : Type*} [Field K] [CharZero K] {a h : K}
    (hd : a^2=6) (hh : h ≠ 0) :
    (4*h*(2+a))*(-a) - (4*h*(2+a)*a)*1 ≠ 0 := by
  have h2 : 2+a ≠ 0 := by
    intro e
    have e' : (2:K) = 0 := by linear_combination (a-2)*e-hd
    exact (by norm_num : (2:K) ≠ 0) e'
  have h6 : a ≠ 0 := by rintro rfl; norm_num at hd
  rw [show (4*h*(2+a))*(-a) - (4*h*(2+a)*a)*1 = (-8)*h*(2+a)*a by ring]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) h2) h6

abbrev Quad (R : Type*) [CommRing R] := QuadraticAlgebra R 6 0
abbrev d (R : Type*) [CommRing R] : Quad R := QuadraticAlgebra.omega

private theorem sq_d : (d R)^2 = 6 := by
  rw [d, QuadraticAlgebra.omega_pow_two_eq_add]
  simp [Algebra.smul_def,map_ofNat]

private theorem star_d : star (d R) = -d R := by
  apply QuadraticAlgebra.ext <;> simp [d]

private theorem conjugate (a r h x z : Quad R) :
    star (equation a r h x z) = equation (star a) (star r) (star h) (star x) (star z) := by
  simp [equation,binary,star_mul',star_pow]

/-- Taking R to be a polynomial ring gives descent of the coefficients. -/
theorem coefficients_descend [IsDomain R] [CharZero R] {r h : R}
    (ht : 54*r^2-32 = -32*h^2) (x z : R) :
    let f := algebraMap R (Quad R)
    let v := equation (d R) (f r) (f h) (f x) (f z)
    f v.re = v := by
  let f := algebraMap R (Quad R)
  let v := equation (d R) (f r) (f h) (f x) (f z)
  change f v.re = v
  have hc : 9*(d R*f r)^2-32 = -32*(f h)^2 := by
    rw [mul_pow,sq_d]
    have hm := congrArg f ht
    simp only [map_sub,map_mul,map_neg,map_pow,map_ofNat] at hm
    linear_combination hm
  have hstar (k : R) : star (f k) = f k := by
    change star (QuadraticAlgebra.mk k 0 : Quad R) = .mk k 0
    rw [QuadraticAlgebra.star_mk]
    simp only [zero_mul,add_zero,neg_zero]
  have fixed : star v = v := by
    dsimp only [v]
    rw [conjugate,star_d,hstar,hstar,hstar,hstar]
    exact invariant sq_d hc (f x) (f z)
  have him : -v.im = v.im := by simpa using congrArg QuadraticAlgebra.im fixed
  have hz : v.im = 0 := by
    apply (mul_eq_zero.mp (show (2:R)*v.im=0 by linear_combination -him)).resolve_left
    exact OfNat.ofNat_ne_zero 2
  exact QuadraticAlgebra.ext rfl hz.symm

/-- The explicit homogeneous polynomial over ℚ. -/
def rationalSextic (u : ℚ) : MvPolynomial (Fin 2) ℚ :=
  let R := MvPolynomial (Fin 2) ℚ
  let f := algebraMap R (Quad R)
  (equation (d R) (f (MvPolynomial.C (CoarseConic.r u))) (f (MvPolynomial.C (CoarseConic.h u)))
    (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1))).re

theorem rationalSextic_eq (u : ℚ) :
    let R := MvPolynomial (Fin 2) ℚ
    let f := algebraMap R (Quad R)
    f (rationalSextic u) =
      equation (d R) (f (MvPolynomial.C (CoarseConic.r u))) (f (MvPolynomial.C (CoarseConic.h u)))
        (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1)) := by
  have hrat : 54*(CoarseConic.r u)^2-32 = -32*(CoarseConic.h u)^2 := by
    linear_combination 2*CoarseConic.second_square u + 54*CoarseConic.first_square u
  apply coefficients_descend
  simpa [map_ofNat] using congrArg (MvPolynomial.C (σ:=Fin 2)) hrat

end
end ZInQBlueprint.RationalModel

#print axioms ZInQBlueprint.RationalModel.scaled_reversal
#print axioms ZInQBlueprint.RationalModel.invariant
#print axioms ZInQBlueprint.RationalModel.constant_norm
#print axioms ZInQBlueprint.RationalModel.change_of_variables_det
#print axioms ZInQBlueprint.RationalModel.coefficients_descend
#print axioms ZInQBlueprint.RationalModel.rationalSextic_eq
