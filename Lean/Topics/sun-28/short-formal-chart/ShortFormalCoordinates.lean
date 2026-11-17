import ShortFormalChart

/-! Evaluating the normalized series U at each actual affine kernel point gives xz². -/
namespace Sun28.ShortFormal
open ZInQ ZInQ.Mult PowerSeries WeierstrassCurve WeierstrassCurve.Affine WithZero
noncomputable section
variable {L : Type*} [Field L] [Valued L ℤᵐ⁰] [CompleteSpace L] [DecidableEq L]

theorem normalized_abscissa {b x y : L} (hb : 0≤vK L b)
    (onCurve : (shortCurve b).toAffine.Nonsingular x y) (hx : vK L x<0) :
    let z := -x/y
    HasSum (fun n => coeff n (shortU b)*z^n) (x*z^2) := by
  let z := -x/y
  have ho := omegaSeries_hasSum hb onCurve hx
  change HasSum (fun n => coeff n (omegaSeries b)*z^n) (-1/y) at ho
  have hy : y≠0 := by
    obtain ⟨_,_,_,_,nz,_,_,_⟩ := formal_val_x_y hb onCurve hx
    exact nz
  have eq := (shortCurve_equation_iff b x y).mp onCurve.1
  have value : x*z^2=1-b*z*(-1/y) := by
    dsimp [z]
    field_simp [hy]
    linear_combination -eq
  have chart : shortU b=1-C b*(X*omegaSeries b) := by
    rw [shortU,←X_mul_uSeries]
    ring
  have shifted : HasSum (fun n => coeff n (C b*(X*omegaSeries b))*z^n) (b*z*(-1/y)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one,Finset.sum_singleton,coeff_C_mul,coeff_succ_X_mul,coeff_zero_eq_constantCoeff_apply,
      map_mul,constantCoeff_X,zero_mul,mul_zero,sub_zero]
    convert ho.mul_left (b*z) using 2 with n
    rw [pow_succ]; ring
  have oneTerm : HasSum (fun n => coeff n (1:PowerSeries L)*z^n) 1 := by
    convert hasSum_single (f:=fun n => coeff n (1:PowerSeries L)*z^n) 0
      (fun n h => by simp [coeff_one,h]) using 1
    simp
  dsimp only
  change HasSum (fun n => coeff n (shortU b)*z^n) (x*z^2)
  rw [value,chart]
  convert oneTerm.sub shifted using 2 with n
  rw [map_sub,sub_mul]

end
#print axioms normalized_abscissa
end Sun28.ShortFormal
