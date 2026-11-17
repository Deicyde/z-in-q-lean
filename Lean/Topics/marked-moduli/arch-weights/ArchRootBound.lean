import DirectCharts
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Explicit complex root bounds on the bounded real parameter chart. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial DirectCharts IntegralSextic
noncomputable section
set_option maxHeartbeats 600000

private theorem scaled_coeff (t : ℝ) (ht : |t| ≤ 6) {i : ℕ} (hi : i < 6) :
    ‖((monicSextic (t : ℂ)).scaleRoots (1/16)).coeff i‖ ≤ 1 := by
  have ht' := abs_le.mp ht
  have ts : t^2 ≤ 36 := by nlinarith [mul_nonneg (by linarith [ht'.1] : 0 ≤ t+6) (by linarith [ht'.2] : 0 ≤ 6-t)]
  rw [coeff_scaleRoots, (monic_six (t:ℂ)).2, monic_coeffs]
  simp only [coeff_add, coeff_C_mul_X_pow,coeff_C_mul_X,coeff_X_pow,coeff_C]
  interval_cases i <;>
    norm_num <;> norm_cast <;> (try simp only [Real.norm_eq_abs, abs, max_def]) <;> (try split_ifs) <;> nlinarith [sq_nonneg t, ht'.1, ht'.2]

/-- Scale by 1/16 before Cauchy's bound: the roots of the scaled monic sextic have norm < 2. -/
theorem small_chart_norm {t : ℝ} (ht : |t| ≤ 6) {x : ℂ}
    (hx : (monicSextic (t:ℂ)).IsRoot x) : ‖x‖ ≤ 32 := by
  let p := (monicSextic (t:ℂ)).scaleRoots (1/16)
  have hm : p.Monic := (monic_scaleRoots_iff _).mpr (monic_six _).1
  have hd : p.natDegree = 6 := (natDegree_scaleRoots ..).trans (monic_six _).2
  have hr : p.IsRoot ((1/16:ℂ)*x) := by
    rw [IsRoot.def, scaleRoots_eval_mul, hx.eq_zero, mul_zero]
  have hb : p.cauchyBound ≤ 2 := by
    rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hd]
    have H : (Finset.range 6).sup (fun i => ‖p.coeff i‖₊) ≤ 1 := by
      apply Finset.sup_le
      intro i hi
      exact_mod_cast scaled_coeff t ht (Finset.mem_range.mp hi)
    calc _ ≤ 1 + 1 := add_le_add_left H _
         _ = _ := by norm_num
  have h := (IsRoot.norm_lt_cauchyBound hm.ne_zero hr).le.trans hb
  have e : ‖(1/16:ℂ)*x‖ ≤ (2:ℝ) := by exact_mod_cast h
  rw [norm_mul] at e
  norm_num at e
  linarith

private theorem cubic_norm {a b g t : ℂ} (h : a^3=t*a*b*g-t^2*b^3) :
    ‖a‖^3 ≤ ‖t‖*‖a‖*‖b‖*‖g‖+‖t‖^2*‖b‖^3 := by
  calc
    ‖a‖^3 = ‖a^3‖ := (norm_pow ..).symm
    _ = _ := congrArg norm h
    _ ≤ _ := (norm_sub_le ..).trans_eq (by simp only [norm_mul,norm_pow])

/-- Each root lies in one of the two discs centred at 0 and −3 of radius 400 √|t|. -/
theorem near_one_center {t : ℝ} (ht : |t| ≤ 6) {x : ℂ}
    (hx : (monicSextic (t:ℂ)).IsRoot x) :
    ‖x‖ ≤ 400 * Real.sqrt |t| ∨ ‖x+3‖ ≤ 400 * Real.sqrt |t| := by
  let a := ‖x*(x+3)‖
  let s := Real.sqrt |t|
  have ha : 0 ≤ a := norm_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=|t| := Real.sq_sqrt (abs_nonneg _)
  have hs3 : s ≤ 3 := by nlinarith
  have hr := small_chart_norm ht hx
  have hb : ‖x+2‖ ≤ 34 := by
    calc ‖x+2‖ ≤ ‖x‖+‖(2:ℂ)‖ := norm_add_le .. 
         _ ≤ _ := by norm_num; linarith
  have hg : ‖x^2+4*x+6‖ ≤ 1158 := by
    calc ‖x^2+4*x+6‖ ≤ (‖x^2‖+‖(4:ℂ)*x‖)+‖(6:ℂ)‖ :=
          (norm_add_le ..).trans (add_le_add_left (norm_add_le ..) _)
         _ ≤ _ := by rw [norm_pow,norm_mul]; norm_num; nlinarith [sq_le_sq' (by linarith [norm_nonneg x] : -(32:ℝ) ≤ ‖x‖) hr]
  have hf := hx.eq_zero
  rw [monic_eval] at hf
  simp only [form,alpha,beta,gamma,one_pow,one_mul,mul_one] at hf
  have ident : (x*(x+3))^3=(t:ℂ)*(x*(x+3))*(x+2)*(x^2+4*x+6)-(t:ℂ)^2*(x+2)^3 := by linear_combination hf
  have key := cubic_norm ident
  rw [Complex.norm_real,Real.norm_eq_abs] at key
  change a^3 ≤ |t| *a*‖x+2‖*‖x^2+4*x+6‖+|t|^2*‖x+2‖^3 at key
  have bg : ‖x+2‖*‖x^2+4*x+6‖ ≤ 34*1158 := mul_le_mul hb hg (norm_nonneg _) (by norm_num)
  have b3 : ‖x+2‖^3 ≤ (34:ℝ)^3 := by gcongr
  have key' : a^3 ≤ |t| *a*(34*1158)+|t|^2*34^3 := calc
    _ ≤ |t| *a*(‖x+2‖*‖x^2+4*x+6‖)+|t|^2*‖x+2‖^3 := by linarith [key]
    _ ≤ _ := by gcongr
  have a_bound : a ≤ 400*s := by
    by_cases h : a ≤ s
    · linarith
    by_contra! bad
    have pos : 0 < a := lt_of_le_of_lt hs (lt_of_not_ge h)
    have t_bound : |t| ≤ 3*a := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs3)]
    have bound2 : |t|^2 ≤ |t| *(3*a) := by nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr t_bound)]
    have scaled : a*a^2 ≤ a*(157284*|t|) := by nlinarith [key',bound2]
    have hsq := le_of_mul_le_mul_left scaled pos
    nlinarith [mul_nonneg (sub_nonneg.mpr bad.le) (by linarith : 0 ≤ a+400*s),sq_pos_of_pos pos]
  have sep : 3 ≤ ‖x‖+‖x+3‖ := by
    have q := norm_sub_le (x+3) x
    simpa [add_comm] using q
  have prod : ‖x‖*‖x+3‖ ≤ 400*s := by simpa [a,norm_mul] using a_bound
  by_cases h : 1 ≤ ‖x+3‖
  · exact Or.inl (le_trans (by nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr h)] : ‖x‖ ≤ ‖x‖*‖x+3‖) prod)
  · exact Or.inr (le_trans (by nlinarith [mul_nonneg (norm_nonneg (x+3)) (by linarith : 0 ≤ ‖x‖-1)] : ‖x+3‖ ≤ ‖x‖*‖x+3‖) prod)

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.small_chart_norm
#print axioms ZInQBlueprint.BranchDepth.near_one_center
