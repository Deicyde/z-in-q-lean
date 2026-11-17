import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
namespace ZInQBlueprint.CMPeriods
open Finset Function
/-- A lower bound for the norm of Euler's product throughout a closed disk. -/
theorem euler_norm_lower {q : ℂ} (hq : ‖q‖ ≤ 1/4) :
    1/2 ≤ ‖∏' n : ℕ, (1-q^(n+1))‖ := by
  have hpartial (n : ℕ) : 1/2 + (1/2 : ℝ)*(1/2)^n ≤
      ∏ i ∈ range n, ‖1-q^(i+1)‖ := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have n0 : 0 ≤ (1/2 : ℝ)^n := by positivity
      have n1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have pw : ‖q‖^n ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
      have loss : ‖q‖^(n+1) ≤ (1/2 : ℝ)^n * (1/4) := by
        rw [pow_succ]; exact mul_le_mul pw hq (norm_nonneg _) n0
      have diff := norm_sub_norm_le (1:ℂ) (q^(n+1))
      rw [norm_one, norm_pow] at diff
      have lower : 1-(1/2 : ℝ)^n*(1/4) ≤ ‖1-q^(n+1)‖ := by linarith
      have step := mul_le_mul ih lower (show 0 ≤ 1-(1/2 : ℝ)^n*(1/4) by linarith)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      rw [Finset.prod_range_succ, pow_succ]
      exact le_trans (by nlinarith only [mul_nonneg n0 (sub_nonneg.mpr n1)]) step
  have ht := (ModularForm.multipliable_one_sub_pow (q:=q) (by linarith)).hasProd.tendsto_prod_nat.norm
  apply ge_of_tendsto' ht
  intro n
  rw [norm_prod]
  exact (le_add_of_nonneg_right (by positivity)).trans (hpartial n)
/-- An elementary estimate for the actual Dedekind eta function at a reduced period. -/
theorem eta_lower {z : ℂ} (hy : 1/2 ≤ z.im) :
    Real.exp (-2*Real.pi*z.im/24) * (1/2) ≤ ‖ModularForm.eta z‖ := by
  have p := Real.pi_gt_three
  have ex := Real.add_one_le_exp Real.pi
  have small : Real.exp (-Real.pi) ≤ 1/4 := by
    rw [Real.exp_neg]
    rw [←one_div]
    exact one_div_le_one_div_of_le (by norm_num) (show (4:ℝ) ≤ Real.exp Real.pi by linarith)
  have prod := euler_norm_lower ((Periodic.norm_qParam_le_of_one_half_le_im hy).trans small)
  rw [ModularForm.eta,norm_mul,Periodic.norm_qParam]
  exact mul_le_mul_of_nonneg_left prod (Real.exp_pos _).le
/-- Silverman's archimedean summand in the original stable height normalization. -/
noncomputable def periodHeight (z : ℂ) : ℝ :=
  -Real.log (2*Real.pi) - 2*Real.log ‖ModularForm.eta z‖ - (1/2)*Real.log z.im
theorem periodHeight_le {z : ℂ} (hy : 1/2 ≤ z.im) : periodHeight z ≤ z.im + 3 := by
  have e := eta_lower hy
  have hpos : 0 < Real.exp (-2*Real.pi*z.im/24) * (1/2) := by positivity
  have logs := Real.log_le_log hpos e
  rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num),Real.log_exp] at logs
  have half : Real.log (1/2) = -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [half] at logs
  have y := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hy
  rw [half] at y
  have pi0 := Real.pi_gt_three
  have pi4 := Real.pi_lt_four
  have c := Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith)
  have two := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  unfold periodHeight
  nlinarith only [logs,y,c,two, mul_nonneg (sub_nonneg.mpr pi4.le)
    (show 0≤z.im by linarith),hy]
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.euler_norm_lower
#print axioms ZInQBlueprint.CMPeriods.eta_lower
#print axioms ZInQBlueprint.CMPeriods.periodHeight_le
