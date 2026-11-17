import DirectCharts
import PrimitiveLifts

/-! The cube in the residual equation of the short monic pole chart. -/
namespace ZInQBlueprint.PrimitivePole
open Polynomial ZInQBlueprint.PrimitiveLifts ZInQBlueprint.DirectCharts ZInQBlueprint.IntegralSextic
variable {R : Type*} [CommRing R]

theorem discriminant {e x : R} (he : e^2= -3) :
    (slope e x)^2-3*(1-e)^2=4*q e x := by
  unfold DirectCharts.slope q; linear_combination -2*he

theorem cube_identity {e x : R} (he : e^2= -3) (hx : q e x=0) :
    e*(6+e*slope e x)^3=18*variation e x := by
  unfold q at hx
  unfold DirectCharts.slope variation alpha beta gamma
  linear_combination
    (4*e^5+12*e^4+54*e^3+180*e+18*x^3+x^2*(108-18*e)+x*(8*e^4+18*e^2+198)+54)*hx
    +(e^5+e^4*(2*x-3)+e^3*(-12*x-6)+e^2*(6*x-54)+e*(36*x+126)-36*x-54)*he

theorem m_congruence (A B : R) :
    m A B+4*(A+30*B)^3=(A+30*B)*ZInQBlueprint.ResidualFactors.poleForm A B := by
  unfold m ZInQBlueprint.ResidualFactors.poleForm; ring

def centre (e d inv : R) : R := (-3-e+d*(1-e))*inv

theorem centre_slope {inv : R} (hi : 2*inv=1) (e d : R) :
    slope e (centre e d inv)=d*(1-e) := by
  unfold DirectCharts.slope centre
  linear_combination (-3-e+d*(1-e))*hi

theorem centre_difference {inv : R} (hi : 2*inv=1) (e d : R) :
    centre e d inv-centre e (-d) inv=d*(1-e) := by
  unfold centre; linear_combination (d*(1-e))*hi

theorem centre_root [IsDomain R] {e d inv : R} (he : e^2= -3) (hd : d^2=3)
    (hi : 2*inv=1) (h4 : (4:R) ≠ 0) : q e (centre e d inv)=0 := by
  have h := discriminant (x:=centre e d inv) he
  rw [centre_slope hi,mul_pow,hd,sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left h4

variable {K : Type*} [Field K]

theorem pole_rows {e a H U V : K} (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (he : e^2= -3) (ha : q e a=0) (hH : H ≠ 0) (hV : V ≠ 0)
    (hU : V^3= -96*e*H^6*U) :
    Nonempty (SimpleTriple (C ((slope e a)^3)*X^3+C (U*variation e a))) := by
  let s := slope e a
  let D := variation e a
  let n := 6+e*s
  have hd : s^2=3*(1-e)^2 := by
    have h := discriminant (x:=a) he
    rw [ha,mul_zero] at h
    exact sub_eq_zero.mp h
  have h4 : (4:K) ≠ 0 := by convert pow_ne_zero 2 h₂ using 1; norm_num
  have he1 : e ≠ 1 := by intro h; apply h4; rw [h] at he; linear_combination he
  have hs : s ≠ 0 := fun z => mul_ne_zero h₃ (pow_ne_zero 2 (sub_ne_zero.mpr he1.symm))
    (by simpa [z] using hd.symm)
  have h18 : (18:K) ≠ 0 := by convert mul_ne_zero h₂ (pow_ne_zero 2 h₃) using 1; norm_num
  have hn : n ≠ 0 := by
    intro h
    have eS : e*s= -6 := by dsimp [n] at h; linear_combination h
    have eq : (e*s)^2=36 := by rw [eS]; norm_num
    rw [mul_pow,he,hd] at eq
    have hprod : (18:K)*(e-1)=0 := by linear_combination eq+9*he
    exact he1 (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left h18))
  have h12 : (12:K) ≠ 0 := by convert mul_ne_zero h4 h₃ using 1; norm_num
  let z := (V*n)/(12*H^2)
  have hz : z ≠ 0 := div_ne_zero (mul_ne_zero hV hn) (mul_ne_zero h12 (pow_ne_zero 2 hH))
  have hc : e*n^3=18*D := cube_identity he ha
  have hnum : (V*n)^3+U*D*(12*H^2)^3=0 := by
    linear_combination n^3*hU-96*H^6*U*hc
  have hcub : z^3 = -(U*D) := by
    dsimp [z]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ (mul_ne_zero h12 (pow_ne_zero _ hH)))).mpr
    linear_combination hnum
  have hw : ((e-1)/2)^2+(e-1)/2+1=0 := by field_simp; linear_combination he
  apply binomial (r:=z/s) (w:=(e-1)/2) (pow_ne_zero _ hs) (div_ne_zero hz hs) h₃ hw
  change U*D= -s^3*(z/s)^3
  rw [div_pow,hcub]
  field_simp [hs]

end ZInQBlueprint.PrimitivePole
#print axioms ZInQBlueprint.PrimitivePole.discriminant
#print axioms ZInQBlueprint.PrimitivePole.cube_identity
#print axioms ZInQBlueprint.PrimitivePole.m_congruence
#print axioms ZInQBlueprint.PrimitivePole.centre_slope
#print axioms ZInQBlueprint.PrimitivePole.centre_difference
#print axioms ZInQBlueprint.PrimitivePole.centre_root
#print axioms ZInQBlueprint.PrimitivePole.pole_rows
