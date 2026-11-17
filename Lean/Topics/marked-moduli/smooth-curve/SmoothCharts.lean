import SquareRootSmooth
import ChartOpen
import SexticThetaHeight

/-! Both affine charts of the unmarked paper curve have the same smooth normal form. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
open IntegralSextic ResidualFactors GlobalTwist CurveChart
open DirectCharts LeadingOrders SexticIgusaChart SexticInvariants
noncomputable section

private def globalScale (u : ℚ) : ℚ := yScale u ^ 2 * (-6*(delta u : ℚ)*homogeneousG u)

private theorem globalScale_ne {u : ℚ} (hu : u ∉ ZInQ.contactSet) : globalScale u ≠ 0 := by
  have hd : 0 < (delta u : ℚ) := by exact_mod_cast delta_pos u
  exact mul_ne_zero (pow_ne_zero _ (yScale_ne hu)) (mul_ne_zero (mul_ne_zero (by norm_num) hd.ne') (rational_parameters u).1)

private theorem chart_eval (u : ℚ) (i : Bool) (x : ℚ) :
    (paper ℚ u i).eval x = globalScale u * form (left u) (right u)
      (if i then 1 else x) (if i then x else 1) := by
  have eval_form (d a b : ℚ) (v w : ℚ[X]) :
      (integralEquation (C d) (C a) (C b) v w).eval x =
        integralEquation d a b (v.eval x) (w.eval x) := by
    simp only [integralEquation,form,m,n,alpha,beta,gamma,poleForm,
      eval_add,eval_mul,eval_sub,eval_pow,eval_neg,eval_ofNat,eval_C]
  rw [paper_eq,eval_mul,eval_pow,eval_C,fixed,eval_form]
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true,eval_one,eval_X]
  all_goals
    unfold globalScale integralEquation homogeneousG left right
    simp only [Rat.cast_id, mul_assoc]

private def six : ℚˣ := Units.mk0 6 (by norm_num)

private theorem eval_dilate (p : ℚ[X]) (x : ℚ) :
    (dilate six p).eval x = p.eval (6*x) := by
  change aeval x (aeval (C (six:ℚ)*X) p) = _
  rw [← aeval_algHom_apply (aeval x) (C (six:ℚ)*X) p]
  simp [six]

/-- Both charts reduce to a nonzero scalar multiple of the monic family,
with t=n/m on the first chart and t=27m/n on the chart at infinity. -/
theorem chart_normal_form {u : ℚ} (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    ∃ (s t : ℚ) (e : ℚ[X] ≃ₐ[ℚ] ℚ[X]), s ≠ 0 ∧ t ≠ 0 ∧
      e (C s * monicSextic t) = paper ℚ u i := by
  obtain ⟨ha,hb,_,_⟩ := parameters hu
  have hS := globalScale_ne hu
  let a := left u
  let b := right u
  cases i
  · refine ⟨globalScale u*a^2, b/a, AlgEquiv.refl, mul_ne_zero hS (pow_ne_zero _ ha),
        div_ne_zero hb ha, ?_⟩
    apply Polynomial.funext
    intro x
    rw [chart_eval]
    change (C (globalScale u*a^2) * monicSextic (b/a)).eval x = globalScale u * form a b x 1
    rw [eval_mul,eval_C,monic_eval]
    have he : a*(b/a) = b := mul_div_cancel₀ b ha
    have ident := affine a (b/a) x 1
    rw [he] at ident
    rw [ident]
    ring
  · let t := 27*a/b
    have ht : 27*a=b*t := (mul_div_cancel₀ _ hb).symm
    refine ⟨globalScale u*(8*b^2)/6^6,t,dilate six,
      div_ne_zero (mul_ne_zero hS (mul_ne_zero (by norm_num) (pow_ne_zero _ hb))) (by norm_num),
      div_ne_zero (mul_ne_zero (by norm_num) ha) hb, ?_⟩
    apply Polynomial.funext
    intro x
    rw [eval_dilate, eval_mul,eval_C,monic_eval,chart_eval]
    change _ = globalScale u * form a b 1 x
    have e := reciprocal_chart ht (6*x) 1
    have h := form_homogeneous a b 6 1 x
    simp only [mul_one] at e h
    rw [h] at e
    linear_combination -(globalScale u/6^6)*e

theorem separable_normal_form {s t : ℚ} (hs : s ≠ 0) (ht : t ≠ 0) :
    IsCoprime (C s * monicSextic t) (C s * monicSextic t).derivative := by
  have d : (C s * monicSextic t).natDegree = 6 := (natDegree_C_mul hs).trans (monic_six t).2
  have rn : 0 < (C s * monicSextic t).natDegree := by omega
  have fne : C s * monicSextic t ≠ 0 := fun h => by simp [h] at rn
  have hD : t^2+27 ≠ 0 := by nlinarith [sq_nonneg t]
  have hd : (C s * monicSextic t).discr ≠ 0 := by
    rw [discr_family _ _ hs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hs))
      (pow_ne_zero _ ht)) (pow_ne_zero _ hD)
  have hr : (C s * monicSextic t).resultant (C s * monicSextic t).derivative ≠ 0 := by
    rw [natDegree_derivative,resultant_deriv (natDegree_pos_iff_degree_pos.mp rn)]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr fne)) hd
  by_contra h
  exact hr (resultant_eq_zero_iff.mpr ⟨Or.inl fne,h⟩)

theorem smooth_chart_algebra {u : ℚ} (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    Algebra.Smooth ℚ (Cover (paper ℚ u i)) := by
  obtain ⟨s,t,e,hs,ht,h⟩ := chart_normal_form hu i
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  let := smooth_cover _ (separable_normal_form hs ht)
  apply Algebra.Smooth.of_equiv (A := Cover (C s * monicSextic t))
  exact squareEquiv (f := C s * monicSextic t) (g := paper ℚ u i) e (1:ℚ[X]ˣ) (by simpa only [Units.val_one,one_pow,one_mul] using h)

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.chart_normal_form
#print axioms ZInQBlueprint.BinaryCover.separable_normal_form
#print axioms ZInQBlueprint.BinaryCover.smooth_chart_algebra
