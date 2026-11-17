import IntrinsicThetaMetric

/-! Pullback of the published Euclidean metric and its comparison with the stable height. -/
namespace ZInQBlueprint.SixMetric
open ThetaQuotient ThetaPeriod BranchHeight OriginalTheta ZInQ.LeafPush2
noncomputable section

/-- This number is defined using branch ratios over their own field, without a period. -/
def intrinsicThetaHeight {K : Type*} [Field K] [NumberField K] (w : Fin 10 → K) : ℝ :=
  normalizedHeight w/8 + branchCorrection w

/-- At Eilers's marked period this is the exact Euclidean height of Pazuki Definition 2.6.
The local coordinate choices, absolute scale, and auxiliary number field have disappeared. -/
theorem exact_pazuki_height {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    {detA : ℂ} (hn : detA≠0) (h : FirstThomae Ω (finiteBranches r) detA) :
    letI := weight_numberField hu hd hz
    (∃ (L : Type) (_ : Field L) (_ : NumberField L) (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ),
      c≠0 ∧ (∀ m, emb (z m)=c*thetaConst Ω m) ∧ z pivot=1 ∧
      euclideanHeight z=intrinsicThetaHeight (weights r)) ∧
    0 ≤ branchCorrection (weights r) ∧ branchCorrection (weights r) ≤ Real.log 10 / 2 := by
  let := weight_numberField hu hd hz
  obtain ⟨L,fL,nL,emb,z,c,hc,he,hp⟩ := representative_of_first hu hd Ω hΩ r hr hz hn h
  have eq := euclidean_of_branches hu hd Ω hΩ r hr hz hn h emb z c hc he
  obtain ⟨sup,low,high⟩ := sup_and_euclidean_of_first hu hd Ω hΩ r hr hz hn h emb z c hc he
  refine ⟨⟨L,fL,nL,emb,z,c,hc,he,hp,eq⟩,?_,?_⟩ <;> linarith

/-- The consequence of Cor. 1.3(2) expressed wholly in the algebraic branch data. -/
theorem branch_budget_of_printed_comparison {K : Type*} [Field K] [NumberField K] (w : Fin 10 → K)
    (F H : ℝ) (hb : F≤H) (corr : 0≤branchCorrection w)
    (comparison :
      |max 1 (intrinsicThetaHeight w) - max 1 (F+Real.log Real.pi)/2| ≤
      ThetaMetric.pazukiConstant * Real.log (min (max 1 (intrinsicThetaHeight w))
        (max 1 (F+Real.log Real.pi)) + 2)) :
    normalizedHeight w ≤ 2^26 * max 1 H := by
  have b := ThetaMetric.theta_le _ _ comparison
  change normalizedHeight w/8+branchCorrection w ≤ 2^23 * max 1 F at b
  have upper := max_le_max_left (1:ℝ) hb
  linarith only [b,corr,upper]

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.exact_pazuki_height
#print axioms ZInQBlueprint.SixMetric.branch_budget_of_printed_comparison
