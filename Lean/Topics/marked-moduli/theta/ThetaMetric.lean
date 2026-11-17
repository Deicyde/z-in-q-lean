import HeightBudget
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The numerical specialization of Pazuki, Corollary 1.3(2), at g = r = 2.
The two barred heights in that statement are truncated below at one. -/
namespace ZInQBlueprint.ThetaMetric
open ZInQ ZInQBlueprint.HeightBudget
noncomputable section

def pazukiConstant : ℝ := 1000 * (2:ℝ)^4 * (Real.log ((2:ℝ)^4))^5

/-- Pazuki's Deligne metric divides the original norm by π in dimension two.
The finite degree contribution is unchanged and each complex embedding occurs
once in the normalized sum. -/
theorem change_metric {ι : Type*} [Fintype ι] [Nonempty ι]
    (finitePart : ℝ) (norm : ι → ℝ) (hpos : ∀ i, 0 < norm i) :
    (finitePart - ∑ i, Real.log (norm i / Real.pi)) / (Fintype.card ι : ℝ) =
      (finitePart - ∑ i, Real.log (norm i)) / (Fintype.card ι : ℝ) + Real.log Real.pi := by
  simp_rw [Real.log_div (hpos _).ne' Real.pi_pos.ne']
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  ring

private theorem log_four_le : Real.log 4 ≤ 7/5 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

theorem pazukiConstant_bounds : 0 ≤ pazukiConstant ∧ pazukiConstant ≤ 2760000 := by
  have h : Real.log ((2:ℝ)^4) ≤ 14/5 := by
    rw [Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hn : 0 ≤ Real.log ((2:ℝ)^4) := Real.log_nonneg (by norm_num)
  constructor
  · unfold pazukiConstant
    positivity
  · unfold pazukiConstant
    calc
      _ ≤ 1000 * (2:ℝ)^4 * (14/5)^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn h _) (by norm_num)
      _ ≤ _ := by norm_num

private theorem log_shift_bound {y : ℝ} (hy : 1 ≤ y) :
    Real.log (y+2) ≤ (23/20)*y := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (y+2)/4 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  linarith [log_four_le]

/-- A single application of the published two-sided inequality suffices.
Here θ is the Euclidean height and h is in von Känel's normalization. -/
theorem theta_le (θ h : ℝ)
    (hp : |max 1 θ - max 1 (h + Real.log Real.pi)/2| ≤
      pazukiConstant * Real.log (min (max 1 θ) (max 1 (h + Real.log Real.pi)) + 2)) :
    θ ≤ (2:ℝ)^23 * max 1 h := by
  let y := max 1 (h + Real.log Real.pi)
  have hy : 1 ≤ y := le_max_left _ _
  have hlogpi : Real.log Real.pi ≤ 7/5 :=
    (Real.log_le_log Real.pi_pos Real.pi_lt_four.le).trans log_four_le
  have hshift : y ≤ (12/5) * max 1 h := by
    apply max_le <;> linarith [le_max_left (1:ℝ) h, le_max_right (1:ℝ) h]
  have hmin : Real.log (min (max 1 θ) y + 2) ≤ Real.log (y+2) := by
    have hpos : (1:ℝ) ≤ min (max 1 θ) y := le_min (le_max_left _ _) hy
    exact Real.log_le_log (by linarith) (by linarith [min_le_right (max 1 θ) y])
  obtain ⟨hc,hC⟩ := pazukiConstant_bounds
  have hupper : max 1 θ - y/2 ≤ pazukiConstant * ((23/20)*y) :=
    (le_abs_self _).trans (hp.trans (mul_le_mul_of_nonneg_left
      (hmin.trans (log_shift_bound hy)) hc))
  have hproduct := mul_le_mul_of_nonneg_right hC (show 0 ≤ (23/20:ℝ)*y by linarith)
  norm_num at hproduct ⊢
  linarith [le_max_right (1:ℝ) θ, le_max_left (1:ℝ) h]

end
end ZInQBlueprint.ThetaMetric

#print axioms ZInQBlueprint.ThetaMetric.change_metric
#print axioms ZInQBlueprint.ThetaMetric.pazukiConstant_bounds
#print axioms ZInQBlueprint.ThetaMetric.theta_le
