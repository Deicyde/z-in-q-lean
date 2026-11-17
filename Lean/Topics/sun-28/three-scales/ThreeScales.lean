import GlobalFactors

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult Height NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

private theorem scale_constant : 3/2*Real.log 2+Real.log 676/3+3*Real.log 7 < (10:ℝ) := by
  have small (x : ℝ) (n k : ℕ) (one : (1:ℝ)<x) (h : x^n < (2.718:ℝ)^k) :
      (n:ℝ)*Real.log x < k := by
    have w : (2.718:ℝ)^k ≤ (Real.exp 1)^k :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) k
    have logs := Real.log_lt_log (pow_pos (zero_lt_one.trans one) _) (h.trans_le w)
    rw [Real.log_pow,Real.log_pow,Real.log_exp,mul_one] at logs
    exact logs
  have a := small 2 4 3 (by norm_num) (by norm_num)
  have b := small 676 1 7 (by norm_num) (by norm_num)
  have c := small 7 1 2 (by norm_num) (by norm_num)
  norm_num at a b c
  linarith

/-- Explicit three-scale height inequality for all four odd multiples on Sun's curve. -/
theorem three_scales (m : Fin 4 → ℤ) (odd : ∀ j, Odd (m j)) (η : ℚ) (nonzero : η≠0)
    (H : ℝ) (hH : 1≤H)
    (tests : ∀ j, logHeight₁ ((scaleRoot (coordinateProduct m).re (coordinateProduct m).im j)^2*η) ≤ H) :
    (indexSize m)^2 ≤ (3/2)*H+10 := by
  have get (j : Fin 4) : (m j:ℝ)^2 ≤ (3/2)*H+10 := by
    have ind := quadratic_index_height (m j)
    have prod := abscissa_product_bound m odd j
    have coeff := three_scale_product_height (coordinateProduct m) η nonzero tests
    linarith [scale_constant]
  have bound (j : Fin 4) : |(m j:ℝ)| ≤ Real.sqrt (3/2*H+10) :=
    (Real.le_sqrt (abs_nonneg _) (by linarith)).mpr (by simpa only [sq_abs] using get j)
  have one : (1:ℝ) ≤ Real.sqrt (3/2*H+10) := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hi : indexSize m ≤ Real.sqrt (3/2*H+10) := by
    unfold indexSize
    exact max_le one (max_le (bound 0) (max_le (bound 1) (max_le (bound 2) (bound 3))))
  simpa only [Real.sq_sqrt (show 0≤3/2*H+10 by linarith)] using
    pow_le_pow_left₀ (zero_le_one.trans (one_le_indexSize m)) hi 2

end
end Sun28.Ordinary
#print axioms Sun28.Ordinary.three_scales
