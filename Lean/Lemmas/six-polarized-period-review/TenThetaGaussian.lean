import ThetaGaussianLine
import ReducedPeriods

/-! A Petersson estimate directly from the ten literal series. -/
namespace ZInQBlueprint.PeriodGaussian
open ThetaPeriod ThetaQuotient JacobianHeight Real
noncomputable section

def bit (j : Fin 16) (k : ℕ) : Bool := decide (j.val / 2^k % 2 = 1)

private theorem halfBit_eq (j : Fin 16) (k : ℕ) : halfBit j k = (offset (bit j k) : ℂ) := by
  have h : j.val / 2^k % 2 = 0 ∨ j.val / 2^k % 2 = 1 := by omega
  rcases h with h|h <;> simp [halfBit,offset,bit,h]

private def imForm (Z : SiegelPeriod) (p q : ℝ) :=
  Z.z11.im*p^2 + 2*Z.z12.im*p*q + Z.z22.im*q^2

private theorem norm_exp_form (Z : SiegelPeriod) (p q a b : ℝ) :
    ‖Complex.exp (2*(π:ℂ)*Complex.I *
      (((p:ℂ)^2*Z.z11 + 2*p*q*Z.z12 + (q:ℂ)^2*Z.z22)/2 + p*a + q*b))‖ =
    exp (-π * imForm Z p q) := by
  rw [Complex.norm_exp]
  congr 1
  simp [imForm,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,div_eq_mul_inv,pow_two]
  ring

private theorem term_bound (Z : SiegelPeriod) (hZ : InStrengDomain Z) (j : Fin 16) (n : ℤ × ℤ) :
    ‖term Z j n‖ ≤ envelope (bit j 2) (π*Z.z11.im/2) n.1 *
      envelope (bit j 3) (π*Z.z22.im/2) n.2 := by
  let p : ℝ := n.1 + offset (bit j 2)
  let q : ℝ := n.2 + offset (bit j 3)
  have ht : ‖term Z j n‖ = exp (-π * imForm Z p q) := by
    simpa only [term,halfBit_eq,p,q,Complex.ofReal_add,Complex.ofReal_intCast] using
      norm_exp_form Z p q (offset (bit j 0)) (offset (bit j 1))
  have cross : 0 ≤ Z.z12.im := by linarith only [hZ.cross]
  have hform : (Z.z11.im*p^2 + Z.z22.im*q^2)/2 ≤ imForm Z p q := by
    unfold imForm
    nlinarith [mul_nonneg (sub_nonneg.mpr hZ.orderedCross) (sq_nonneg p),
      mul_nonneg (sub_nonneg.mpr (hZ.orderedCross.trans hZ.orderedDiagonal)) (sq_nonneg q),
      mul_nonneg cross (sq_nonneg (p+q))]
  rw [ht]
  calc
    _ ≤ exp (-(π*Z.z11.im/2)*p^2) * exp (-(π*Z.z22.im/2)*q^2) := by
      rw [← exp_add,exp_le_exp]
      nlinarith only [mul_le_mul_of_nonneg_left hform Real.pi_pos.le]
    _ ≤ _ := mul_le_mul
      (gaussian_le_envelope _ (width_of_reduced hZ.lower) n.1)
      (gaussian_le_envelope _ (width_of_reduced (hZ.lower.trans hZ.orderedDiagonal)) n.2)
      (exp_pos _).le (envelope_nonneg _ _ _)

theorem theta_series_bound (Z : SiegelPeriod) (hZ : InStrengDomain Z) (j : Fin 16) :
    ‖thetaNull Z j‖ ≤ mass (bit j 2) (π*Z.z11.im/2) * mass (bit j 3) (π*Z.z22.im/2) := by
  have hf := envelope_hasSum (bit j 2) (π*Z.z11.im/2)
  have hg := envelope_hasSum (bit j 3) (π*Z.z22.im/2)
  have hfg := hf.summable.mul_of_nonneg hg.summable (envelope_nonneg _ _) (envelope_nonneg _ _)
  have hn := hfg.of_nonneg_of_le (fun n => norm_nonneg (term Z j n)) (term_bound Z hZ j)
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum (term_bound Z hZ j) hfg).trans_eq (hf.mul hg hfg).tsum_eq)

private theorem exp_eight (x : ℝ) : exp (-(x/2)/4)^8 = exp (-x) := by
  rw [← exp_nat_mul]; congr 1; ring

private theorem mass_product (x y : ℝ) :
    (∏ i, (mass (bit (evenIndices i) 2) (x/2) * mass (bit (evenIndices i) 3) (y/2))^2)
      = (7/4:ℝ)^24 * (13/6:ℝ)^16 * exp (-x) * exp (-y) := by
  rw [← exp_eight x, ← exp_eight y]
  norm_num [Fin.prod_univ_succ, evenIndices, bit, mass]
  ring

theorem ten_theta_product (Z : SiegelPeriod) (hZ : InStrengDomain Z) :
    (∏ i, ‖thetaNull Z (evenIndices i)‖^2) ≤
      (7/4:ℝ)^24 * (13/6:ℝ)^16 * exp (-(π*Z.z11.im)) * exp (-(π*Z.z22.im)) := by
  rw [← mass_product]
  gcongr with i _
  exact theta_series_bound Z hZ _

end
end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.theta_series_bound
#print axioms ZInQBlueprint.PeriodGaussian.ten_theta_product
