import DirectCharts
import Mathlib.FieldTheory.Separable
/-! A Bézout identity for the smooth locus of the three-term sextic. -/
namespace ZInQBlueprint.RegularSextic
open Polynomial ZInQBlueprint.DirectCharts
noncomputable section
variable {R : Type*} [CommRing R]
private def leftCoeff (t : R) : R[X] :=
  ((((C (-6*(3*t^2-16*t+17))*X+
    C (15*t^3-179*t^2+553*t-477))*X+
    C (6*(13*t^3-82*t^2+143*t-90)))*X+
    C (-3*(3*t^4-60*t^3+202*t^2-204*t+27)))*X+
    C (-2*t*(9*t^3-63*t^2+151*t-153)))
private def rightCoeff (t : R) : R[X] :=
  (((((C (3*t^2-16*t+17)*X+
    C (-(t-3)*(3*t^2-28*t+35)))*X+
    C (-3*(7*t^3-47*t^2+89*t-57)))*X+
    C (3*t^4-70*t^3+262*t^2-254*t+27))*X+
    C (4*t*(3*t^3-27*t^2+67*t-63)))*X+
    C (12*t*(t-2)*(t-1)^2))

theorem bezout (t : R) :
    leftCoeff t * monicSextic t + rightCoeff t * (monicSextic t).derivative =
      C (32*t^2*(t^2+27)) := by
  rw [monic_coeffs]
  simp [leftCoeff,rightCoeff,derivative_add,derivative_mul,
    derivative_pow, map_ofNat]
  ring

theorem separable {k : Type*} [Field k] [NeZero (2:k)] {t : k}
    (ht : t≠0) (hG : t^2+27≠0) : (monicSextic t).Separable := by
  have h32 : (32:k) ≠ 0 := by
    rw [show (32:k)=2^5 by norm_num]; exact pow_ne_zero _ (NeZero.ne _)
  have h := mul_ne_zero (mul_ne_zero h32 (pow_ne_zero 2 ht)) hG
  let d := 32*t^2*(t^2+27)
  refine ⟨C d⁻¹*leftCoeff t,C d⁻¹*rightCoeff t,?_⟩
  calc
    _ = C d⁻¹ * (leftCoeff t * monicSextic t + rightCoeff t * (monicSextic t).derivative) := by ring
    _ = 1 := by rw [bezout, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem good_parameter {k : Type*} [Field k] [NeZero (2:k)] {a b G : k}
    (ha : a≠0) (hb : b≠0) (hG : G≠0) (h : 27*a^2+b^2=G^3) :
    (monicSextic (b/a)).Separable := by
  apply separable (div_ne_zero hb ha)
  intro hz
  have hh : 27*a^2+b^2=0 := by field_simp [ha] at hz; linear_combination hz
  exact pow_ne_zero 3 hG (h.symm.trans hh)
end
end ZInQBlueprint.RegularSextic
#print axioms ZInQBlueprint.RegularSextic.bezout
#print axioms ZInQBlueprint.RegularSextic.separable
#print axioms ZInQBlueprint.RegularSextic.good_parameter
