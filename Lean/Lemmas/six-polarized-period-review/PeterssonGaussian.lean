import TenThetaGaussian

/-! The elementary Gaussian estimate fits the fixed modular-height constant. -/
namespace ZInQBlueprint.PeriodGaussian
open ThetaPeriod ThetaQuotient JacobianHeight Real
noncomputable section

def gaussianConstant : ℝ := 2^8 * (7/4)^24 * (13/6)^16 * 22^2

private theorem fifth_moment {t : ℝ} (ht : 0 ≤ t) : t^5 * exp (-t) ≤ 22 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t/5)
  have hh : (t/5 * exp (-(t/5)))^5 ≤ (exp (-1))^5 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) (exp_pos _).le) h _
  have he : (exp (-(t/5)))^5 = exp (-t) := by
    rw [← exp_nat_mul]; congr 1; ring
  rw [mul_pow,he,exp_neg (1 : ℝ)] at hh
  have e : (2.7:ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have inv : (exp 1)⁻¹ ≤ (2.7:ℝ)⁻¹ := inv_anti₀ (by norm_num) e
  have bound : ((exp 1)⁻¹)^5 ≤ ((2.7:ℝ)⁻¹)^5 := pow_le_pow_left₀ (by positivity) inv _
  calc
    _ = 5^5 * ((t/5)^5 * exp (-t)) := by ring
    _ ≤ 5^5 * ((2.7:ℝ)⁻¹)^5 := mul_le_mul_of_nonneg_left (hh.trans bound) (by norm_num)
    _ ≤ _ := by norm_num

theorem petersson_gaussian (Z : SiegelPeriod) (hZ : InStrengDomain Z) :
    peterssonFactor Z ≤ gaussianConstant := by
  let x := Z.z11.im
  let y := Z.z22.im
  have hx : 0 ≤ x := Z.im11.le
  have hy : 0 ≤ y := hx.trans hZ.orderedDiagonal
  have hd : (x*y-Z.z12.im^2)^5 ≤ (x*y)^5 :=
    pow_le_pow_left₀ Z.imdet.le (sub_le_self _ (sq_nonneg _)) 5
  have ht := ten_theta_product Z hZ
  change _ ≤ (7/4:ℝ)^24*(13/6:ℝ)^16*exp (-(π*x))*exp (-(π*y)) at ht
  unfold peterssonFactor
  calc
    _ ≤ 2^8 * π^10 * ((7/4:ℝ)^24*(13/6:ℝ)^16*exp (-(π*x))*exp (-(π*y))) *
        (x*y)^5 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left ht (by positivity)) hd (pow_nonneg Z.imdet.le _) (by positivity)
    _ = (2^8*(7/4:ℝ)^24*(13/6:ℝ)^16) * (((π*x)^5*exp (-(π*x)))*((π*y)^5*exp (-(π*y)))) := by ring
    _ ≤ (2^8*(7/4:ℝ)^24*(13/6:ℝ)^16) * (22*22) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (fifth_moment (mul_nonneg pi_pos.le hx)) (fifth_moment (mul_nonneg pi_pos.le hy))
        (by positivity) (by norm_num)
    _ = _ := by norm_num [gaussianConstant]

theorem log_allowance : 30*log π + 3*log gaussianConstant < 150 := by
  have e : (2.7:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have p : π^5 < exp 6 := calc
    _ < (3.15:ℝ)^5 := pow_lt_pow_left₀ Real.pi_lt_d2 pi_pos.le (by decide)
    _ < (2.7:ℝ)^6 := by norm_num
    _ < (exp 1)^6 := pow_lt_pow_left₀ e (by norm_num) (by decide)
    _ = _ := by rw [← exp_nat_mul]; norm_num
  have c : gaussianConstant < exp 38 := calc
    _ < (2.7:ℝ)^38 := by norm_num [gaussianConstant]
    _ < (exp 1)^38 := pow_lt_pow_left₀ e (by norm_num) (by decide)
    _ = _ := by rw [← exp_nat_mul]; norm_num
  have q := (Real.log_lt_iff_lt_exp (pow_pos pi_pos 5)).mpr p
  rw [log_pow] at q
  norm_num only [Nat.cast_ofNat] at q
  have r := (Real.log_lt_iff_lt_exp (show 0 < gaussianConstant by norm_num [gaussianConstant])).mpr c
  linarith only [q,r]

end
end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.petersson_gaussian
#print axioms ZInQBlueprint.PeriodGaussian.log_allowance
