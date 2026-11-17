import GenusTwoThetaSeries
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Absolute convergence of the genus-two theta series. -/
namespace ZInQBlueprint.ThetaPeriod
noncomputable section

private def imForm (Z : SiegelPeriod) (p q : ℝ) :=
  Z.z11.im*p^2 + 2*Z.z12.im*p*q + Z.z22.im*q^2

/-- det(Im Z)/tr(Im Z) is an explicit lower bound for the least eigenvalue. -/
theorem gaussian_lower (Z : SiegelPeriod) :
    ∃ t : ℝ, 0 < t ∧ ∀ p q : ℝ, t*(p^2+q^2) ≤ imForm Z p q := by
  let a := Z.z11.im
  let b := Z.z12.im
  let d := Z.z22.im
  have ha : 0 < a := Z.im11
  have hdet : 0 < a*d-b^2 := Z.imdet
  have had : 0 < a*d := by linarith [sq_nonneg b]
  have hd := pos_of_mul_pos_right had ha.le
  have htrace := add_pos ha hd
  refine ⟨(a*d-b^2)/(a+d),div_pos hdet htrace,?_⟩
  intro p q
  change (a*d-b^2)/(a+d)*(p^2+q^2) ≤ a*p^2+2*b*p*q+d*q^2
  rw [div_mul_eq_mul_div,div_le_iff₀ htrace]
  nlinarith [sq_nonneg (a*p+b*q),sq_nonneg (b*p+d*q)]

private def shift (j : Fin 16) (k : ℕ) : ℝ := ((j.val / 2^k % 2 : ℕ):ℝ)/2

private theorem halfBit_real (j : Fin 16) (k : ℕ) : halfBit j k = (shift j k : ℂ) := by
  simp only [halfBit,shift,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat]

private theorem norm_exp_form (Z : SiegelPeriod) (p q a b : ℝ) :
    ‖Complex.exp (2*(Real.pi:ℂ)*Complex.I *
      (((p:ℂ)^2*Z.z11 + 2*p*q*Z.z12 + (q:ℂ)^2*Z.z22)/2 + p*a + q*b))‖ =
    Real.exp (-Real.pi * imForm Z p q) := by
  rw [Complex.norm_exp]
  congr 1
  simp [imForm,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    div_eq_mul_inv,pow_two]
  ring

private theorem norm_term (Z : SiegelPeriod) (j : Fin 16) (n : ℤ × ℤ) :
    ‖term Z j n‖ = Real.exp (-Real.pi * imForm Z ((n.1:ℝ)+shift j 2) ((n.2:ℝ)+shift j 3)) := by
  simpa only [term,halfBit_real,Complex.ofReal_add,Complex.ofReal_intCast] using
    norm_exp_form Z ((n.1:ℝ)+shift j 2) ((n.2:ℝ)+shift j 3) (shift j 0) (shift j 1)

theorem summable_norm_terms (Z : SiegelPeriod) (j : Fin 16) :
    Summable (fun n : ℤ × ℤ => ‖term Z j n‖) := by
  obtain ⟨t,ht,hq⟩ := gaussian_lower Z
  let f (a : ℝ) (n : ℤ) := Real.exp (-Real.pi*((n:ℝ)+a)^2*t)
  have hs (a : ℝ) : Summable (f a) := by
    have he : f a = HurwitzKernelBounds.f_int 0 a t := by
      funext n
      simp [HurwitzKernelBounds.f_int,f]
    rw [he]
    exact HurwitzKernelBounds.summable_f_int 0 a ht
  have hn (a : ℝ) : 0 ≤ f a := fun _ => (Real.exp_pos _).le
  apply (hs (shift j 2) |>.mul_of_nonneg (hs (shift j 3)) (hn _) (hn _)).of_nonneg_of_le
    (fun n => norm_nonneg (term Z j n))
  intro n
  rw [norm_term Z j n]
  change _ ≤ Real.exp _ * Real.exp _
  rw [← Real.exp_add,Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left (hq ((n.1:ℝ)+shift j 2) ((n.2:ℝ)+shift j 3)) Real.pi_pos.le
  linarith

theorem summable_terms (Z : SiegelPeriod) (j : Fin 16) : Summable (term Z j) :=
  (summable_norm_terms Z j).of_norm

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.gaussian_lower
#print axioms ZInQBlueprint.ThetaPeriod.summable_norm_terms
#print axioms ZInQBlueprint.ThetaPeriod.summable_terms
