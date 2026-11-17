import GaussianCentres
import ActualBeta

namespace Sun28.PointPencils
open Height Sun28.ScalarHeight
noncomputable section

/-- The shorter leg and the exact factor coming from reduction of 2x²+3. -/
def gapSize (p c : ℤ) : ℤ := max 2 ((min |p| |c|)^2+1)
def circleCap (x : ℚ) (d : ℕ) (p c : ℤ) : ℝ :=
  (3*(d:ℝ)*(gapSize p c:ℝ)^2)/(4*(reduction x:ℝ))

theorem primitive_gap {p c : ℤ} {w : ℕ} (cop : IsCoprime p c)
    (py : p^2+c^2=(w:ℤ)^2) : 2*(w:ℤ) ≤ gapSize p c := by
  have axis (r : ℤ) (unit : IsUnit r) (eq : r^2=(w:ℤ)^2) : 2*(w:ℤ)≤2 := by
    have one:=Int.isUnit_iff_abs_eq.mp unit
    have sqr:=congrArg (fun z:ℤ=>z^2) one
    simp only [sq_abs,one_pow] at sqr
    have wp : w≤1 := by
      by_contra! bad
      have two : (2:ℤ)≤w := by exact_mod_cast bad
      have four := mul_self_le_mul_self (by decide : (0:ℤ)≤2) two
      nlinarith only [sqr,eq,four]
    exact_mod_cast (show 2*w≤2 by omega)
  by_cases hp : p=0
  · subst p
    have a:=axis c (cop.symm.isUnit_of_dvd (dvd_zero _)) (by simpa only [zero_pow two_ne_zero,zero_add] using py)
    exact a.trans (le_max_left ..)
  by_cases hc : c=0
  · subst c
    have a:=axis p (cop.isUnit_of_dvd (dvd_zero _)) (by simpa only [zero_pow two_ne_zero,add_zero] using py)
    exact a.trans (le_max_left ..)
  unfold gapSize
  refine le_trans ?_ (le_max_right ..)
  rcases le_total |p| |c| with h|h
  · rw [min_eq_left h,sq_abs]
    exact sum_squares_gap (p:=c) (k:=p) (z:=(w:ℤ)) (Int.natCast_nonneg w) hp ((add_comm ..).trans py)
  · rw [min_eq_right h,sq_abs]
    exact sum_squares_gap (p:=p) (k:=c) (z:=(w:ℤ)) (Int.natCast_nonneg w) hc py

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.primitive_gap
