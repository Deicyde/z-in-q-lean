import OptimizedPazuki
import IntrinsicMetricBounds
import PaperHeight

/-! Period-free algebraic estimate on the six-contact locus. -/
namespace ZInQBlueprint.SixMetric
open ThetaPeriod ThetaQuotient BranchHeight BranchFormula BranchDepth
noncomputable section

theorem algebraic_correction_bounds {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0) :
    letI := weight_numberField hu hd hz
    0≤branchCorrection (weights r) ∧ branchCorrection (weights r)≤Real.log 10/2 := by
  let := weight_numberField hu hd hz
  apply correction_bounds
  intro i he
  have c := congrArg (fun v : weightField r => (v:ℂ)) he
  change branchRatio r i=0 at c
  have non (k : Fin 10) := branchValue_nonzero _ (finiteBranches_injective hr) (pairs k)
  exact div_ne_zero (non i) (non 0) c

/-- The exact intrinsic formula always satisfies this bound, without an analytic period. -/
theorem paper_intrinsic_budget {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0) :
    letI := weight_numberField hu hd hz
    intrinsicThetaHeight (weights r) < (115+12*ZInQ.ratHeight u)/8+Real.log 10/2 := by
  let := weight_numberField hu hd hz
  have h := paper_branch_height_input hu hd hr hz
  have c := (algebraic_correction_bounds hu hd r hr hz).2
  unfold intrinsicThetaHeight
  linarith only [h,c]

/-- The same direct bound using the sextic's explicit pole norm. -/
theorem paper_intrinsic_pole {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0) :
    letI := weight_numberField hu hd hz
    intrinsicThetaHeight (weights r) <
      (49+Real.log 8503056+6*Real.log (poleNorm u))/8+Real.log 10/2 := by
  let := weight_numberField hu hd hz
  have h := paper_branch_height hu hd hr hz
  have c := (algebraic_correction_bounds hu hd r hr hz).2
  unfold intrinsicThetaHeight
  linarith only [h,c]

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.algebraic_correction_bounds
#print axioms ZInQBlueprint.SixMetric.paper_intrinsic_budget
#print axioms ZInQBlueprint.SixMetric.paper_intrinsic_pole
