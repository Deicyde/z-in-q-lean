import GenusTwoThetaSeries
import HPArchScalar

/-! The infinite factor of the genus-two discriminant formula, in Streng's numbering. -/
namespace ZInQBlueprint.JacobianHeight
open ThetaPeriod ThetaQuotient SixContactHP
noncomputable section

/-- Streng's domain B, defined by inequalities (S1), (S2) and (B) in §7.2. -/
structure InStrengDomain (Z : SiegelPeriod) : Prop where
  realPart : ∀ z ∈ [Z.z11,Z.z12,Z.z22], -(1:ℝ)/2 ≤ z.re ∧ z.re < 1/2
  cross : 0 ≤ 2*Z.z12.im
  orderedCross : 2*Z.z12.im ≤ Z.z11.im
  orderedDiagonal : Z.z11.im ≤ Z.z22.im
  lower : Real.sqrt (3/4) ≤ Z.z11.im

def boundedIndex : Fin 6 → Fin 16 := ![0,1,2,3,12,15]
def firstIndex : Fin 2 → Fin 16 := ![4,6]
def secondIndex : Fin 2 → Fin 16 := ![8,9]

/-- The common leading factor in the second and third lines of Streng's Proposition 7.6. -/
def thetaLead (z : ℂ) := (2:ℂ) * Complex.exp (Complex.I*((Real.pi:ℂ)*z)/4)

/-- Only the six uniform upper bounds of Corollary 7.7 and two lines of Proposition 7.6
are used. The printed uniform bounds 1.41 and 1.56 both imply the first inequality. -/
def StrengEstimates : Prop := ∀ (Z : SiegelPeriod), InStrengDomain Z →
  (∀ i, ‖thetaNull Z (boundedIndex i)‖ < 1.56) ∧
  (∀ i, ‖thetaNull Z (firstIndex i) / thetaLead Z.z11 - 1‖ < 0.348) ∧
  (∀ i, ‖thetaNull Z (secondIndex i) / thetaLead Z.z22 - 1‖ < 0.348)

def peterssonFactor (Z : SiegelPeriod) : ℝ :=
  2^8 * Real.pi^10 * (∏ i, ‖thetaNull Z (evenIndices i)‖^2) *
    (Z.z11.im * Z.z22.im - Z.z12.im^2)^5

private theorem product_blocks (a : Fin 16 → ℂ) :
    (∏ i, ‖a (evenIndices i)‖^2) =
      chiNorm (a ∘ boundedIndex) (a ∘ firstIndex) (a ∘ secondIndex) := by
  simp [chiNorm, evenIndices, boundedIndex, firstIndex, secondIndex, Fin.prod_univ_succ]
  ring

private theorem lead_norm (z : ℂ) :
    ‖thetaLead z‖ = 2*Real.exp (-(Real.pi*z.im)/4) := by
  rw [thetaLead, norm_mul, Complex.norm_exp]
  have hr : (Complex.I*((Real.pi:ℂ)*z)/4).re = -(Real.pi*z.im)/4 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hr]
  norm_num

private theorem bound_from_lead (w z : ℂ) (hw : ‖w / thetaLead z - 1‖ < 0.348) :
    ‖w‖ ≤ 3*Real.exp (-(Real.pi*z.im)/4) := by
  have ht : ‖w / thetaLead z‖ ≤ ‖w / thetaLead z - 1‖ + 1 := by
    simpa using norm_add_le (w / thetaLead z - 1) 1
  rw [norm_div, lead_norm] at ht
  have hp := Real.exp_pos (-(Real.pi*z.im)/4)
  have hq : ‖w‖ / (2*Real.exp (-(Real.pi*z.im)/4)) ≤ 1.5 := by linarith
  have h := (div_le_iff₀ (by positivity)).mp hq
  linarith only [h]

/-- Every reduced period of the actual series satisfies the uniform Petersson bound
under Streng's two published estimates. No branch partition is used in this formula. -/
theorem petersson_bound (streng : StrengEstimates) (Z : SiegelPeriod) (hZ : InStrengDomain Z) :
    peterssonFactor Z ≤ archConstant := by
  obtain ⟨hs,hx,hy⟩ := streng Z hZ
  rw [peterssonFactor, product_blocks]
  apply hp_arch_bound _ _ _ Z.im11.le (Z.im11.le.trans hZ.orderedDiagonal) Z.imdet.le
  · intro i
    exact (hs i).le.trans (by norm_num)
  · exact fun i => bound_from_lead _ _ (hx i)
  · exact fun i => bound_from_lead _ _ (hy i)

theorem petersson_positive {Z : SiegelPeriod} (h : ∀ i, thetaNull Z (evenIndices i) ≠ 0) :
    0 < peterssonFactor Z := by
  have hprod : 0 < ∏ i, ‖thetaNull Z (evenIndices i)‖^2 :=
    Finset.prod_pos (fun i _ => pow_pos (norm_pos_iff.mpr (h i)) _)
  unfold peterssonFactor
  exact mul_pos (mul_pos (by positivity) hprod) (pow_pos Z.imdet _)

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.petersson_bound
#print axioms ZInQBlueprint.JacobianHeight.petersson_positive
