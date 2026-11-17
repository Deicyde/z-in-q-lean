import RowWeight
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Sun28.ConeReal
open MeasureTheory Set Metric Real
open scoped ENNReal NNReal
noncomputable section

private theorem rad_complex (z : ℂ) :
    rad (Complex.measurableEquivRealProd z) = ‖z‖^2 := by
  rw [←Complex.normSq_eq_norm_sq]
  simp [rad,Complex.normSq_apply,pow_two]

private theorem area_formula {t:ℝ} (h:0≤t) :
    ENNReal.ofReal (√t)^2 * (NNReal.pi:ℝ≥0∞) = ENNReal.ofReal (π*t) := by
  rw [←ENNReal.ofReal_pow (Real.sqrt_nonneg _),Real.sq_sqrt h]
  rw [mul_comm π,ENNReal.ofReal_mul h]
  rw [←NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem area_closed (t:ℝ) : volume {z : ℝ×ℝ | rad z ≤ t} = ENNReal.ofReal (π*t) := by
  rw [←Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  by_cases h : 0≤t
  · have e : Complex.measurableEquivRealProd ⁻¹' {z : ℝ×ℝ | rad z≤t} = closedBall (0:ℂ) (√t) := by
      ext z
      change rad (Complex.measurableEquivRealProd z) ≤ t ↔ dist z 0 ≤ √t
      rw [rad_complex,dist_zero_right,Real.le_sqrt (norm_nonneg _) h]
    rw [e,Complex.volume_closedBall,area_formula h]
  · have e : Complex.measurableEquivRealProd ⁻¹' {z : ℝ×ℝ | rad z≤t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      change rad (Complex.measurableEquivRealProd z)≤t at hz
      rw [rad_complex] at hz
      nlinarith [sq_nonneg ‖z‖]
    rw [e,measure_empty,ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (le_of_not_ge h))]

theorem area_open (t:ℝ) : volume {z : ℝ×ℝ | rad z < t} = ENNReal.ofReal (π*t) := by
  rw [←Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  by_cases h : 0≤t
  · have e : Complex.measurableEquivRealProd ⁻¹' {z : ℝ×ℝ | rad z<t} = ball (0:ℂ) (√t) := by
      ext z
      change rad (Complex.measurableEquivRealProd z) < t ↔ dist z 0 < √t
      rw [rad_complex,dist_zero_right,Real.lt_sqrt (norm_nonneg _)]
    rw [e,Complex.volume_ball,area_formula h]
  · have e : Complex.measurableEquivRealProd ⁻¹' {z : ℝ×ℝ | rad z<t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      change rad (Complex.measurableEquivRealProd z)<t at hz
      rw [rad_complex] at hz
      nlinarith [sq_nonneg ‖z‖]
    rw [e,measure_empty,ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (le_of_not_ge h))]

/-- A slice crossing radius zero only decreases its area. This estimate uses ordinary
two-dimensional Lebesgue measure on the ordered pair of real coordinates. -/
theorem shell_area (t : ℝ) {ε : ℝ} (he : 0≤ε) :
    volume {z : ℝ×ℝ | |rad z-t|≤ε} ≤ ENNReal.ofReal (π*(2*ε)) := by
  have eq : {z : ℝ×ℝ | |rad z-t|≤ε} =
      {z | rad z≤t+ε} \ {z | rad z<t-ε} := by
    ext z; change |rad z-t|≤ε ↔ rad z≤t+ε ∧ ¬rad z<t-ε
    rw [abs_le]; constructor <;> intro h
    · exact ⟨by linarith [h.2],by linarith [h.1]⟩
    · exact ⟨by linarith [le_of_not_gt h.2],by linarith [h.1]⟩
  have sub : {z : ℝ×ℝ | rad z<t-ε} ⊆ {z | rad z≤t+ε} := by
    intro z hz; change rad z<t-ε at hz; change rad z≤t+ε; linarith
  have meas : MeasurableSet {z : ℝ×ℝ | rad z<t-ε} := by
    change MeasurableSet (rad ⁻¹' Iio _)
    exact measurableSet_Iio.preimage (by unfold rad; fun_prop)
  rw [eq,measure_sdiff sub meas.nullMeasurableSet (by rw [area_open]; exact ENNReal.ofReal_ne_top),
       area_closed,area_open,tsub_le_iff_right]
  calc
    _ = ENNReal.ofReal (π*(2*ε)+π*(t-ε)) := by congr 1;ring
    _ ≤ _ := ENNReal.ofReal_add_le
end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.area_closed
#print axioms Sun28.ConeReal.area_open
#print axioms Sun28.ConeReal.shell_area
