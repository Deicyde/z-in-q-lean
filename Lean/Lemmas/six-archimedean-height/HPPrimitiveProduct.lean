import PeterssonGaussian

/-! The three conventions for the weight-ten form and the archimedean height
in the normalized metric used by von Känel. -/
namespace ZInQBlueprint.ArchimedeanHeight
open ThetaPeriod ThetaQuotient JacobianHeight PeriodGaussian Real
noncomputable section

def rawChi (Z : SiegelPeriod) : ℂ := ∏ i, thetaNull Z (evenIndices i)^2

def primitiveChi (Z : SiegelPeriod) : ℂ := rawChi Z / 2^12

def imDet (Z : SiegelPeriod) : ℝ := Z.z11.im * Z.z22.im - Z.z12.im^2

theorem raw_petersson (Z : SiegelPeriod) :
    peterssonFactor Z = 2^8 * π^10 * ‖rawChi Z‖ * (imDet Z)^5 := by
  simp only [peterssonFactor,rawChi,imDet,norm_prod,norm_pow]

theorem primitive_petersson (Z : SiegelPeriod) :
    peterssonFactor Z = 2^20 * π^10 * ‖primitiveChi Z‖ * (imDet Z)^5 := by
  rw [raw_petersson,primitiveChi,norm_div,norm_pow,Complex.norm_two]
  ring

/-- The archimedean factor after absorbing the genus-two change of metric. -/
def lockhart (Z : SiegelPeriod) : ℝ := π^10 * peterssonFactor Z

theorem lockhart_eq (Z : SiegelPeriod) :
    lockhart Z = 2^8 * π^20 * ‖rawChi Z‖ * (imDet Z)^5 := by
  rw [lockhart,raw_petersson]
  ring

theorem metric_log {Z : SiegelPeriod} (nz : rawChi Z ≠ 0) :
    log (lockhart Z) = 10*log π + log (peterssonFactor Z) := by
  have hp : 0 < peterssonFactor Z := by
    rw [raw_petersson]
    have hn := norm_pos_iff.mpr nz
    have hid : 0 < imDet Z := Z.imdet
    positivity
  rw [lockhart,log_mul (pow_ne_zero 10 pi_ne_zero) hp.ne',log_pow]
  norm_num

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.raw_petersson
#print axioms ZInQBlueprint.ArchimedeanHeight.primitive_petersson
#print axioms ZInQBlueprint.ArchimedeanHeight.lockhart_eq
#print axioms ZInQBlueprint.ArchimedeanHeight.metric_log
