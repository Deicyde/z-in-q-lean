import ArchRootMetric
import BranchSupMetric
import ProjectiveThetaHeight

/-! Exact Fubini–Study height using only the ten intrinsic algebraic branch ratios. -/
namespace ZInQBlueprint.SixMetric
open OriginalTheta ThetaPeriod ThetaQuotient BranchHeight BranchFormula ZInQ.LeafPush2
noncomputable section

set_option maxHeartbeats 460000 in
theorem euclidean_of_branches {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    {detA : ℂ} (hn : detA≠0) (h : FirstThomae Ω (finiteBranches r) detA)
    {L : Type} [Field L] [NumberField L] (emb : L →+* ℂ) (z : Char2 → L)
    (c : ℂ) (hc : c≠0) (hzθ : ∀ m, emb (z m)=c*thetaConst Ω m) :
    letI := weight_numberField hu hd hz
    euclideanHeight z = normalizedHeight (weights r)/8 + branchCorrection (weights r) := by
  let := weight_numberField hu hd hz
  let y := z ∘ pairChar
  have off (m : Char2) (hm : ¬ ∃ i, pairChar i=m) : z m=0 := by
    have no : dotParity m≠0 := fun e => hm ((even_unique m).mp e).exists
    have odd : dotParity m=1 := by have b := (dotParity m).isLt; omega
    apply emb.injective
    rw [hzθ,thetaConst_odd Ω hΩ m odd,map_zero,mul_zero]
  have hs := sparse_heights pairChar pairChar_injective z off
  let common := c^8*(scaleOf detA hn:ℂ)
  have ac : common≠0 := mul_ne_zero (pow_ne_zero _ hc) (scaleOf detA hn).ne_zero
  have E (i : Fin 10) : emb ((y i)^8)=common*branchValue (finiteBranches r) (pairs i) := by
    change emb ((z (pairChar i))^8)=_
    rw [map_pow,hzθ,mul_pow,pairChar_eq,eighth_of_first hn h]
    simp [eilersLabel,common]
    ring
  have b0 := branchValue_nonzero _ (finiteBranches_injective hr) (pairs 0)
  have y0 : y 0≠0 := by
    intro hf
    have eq := E 0
    rw [hf,zero_pow (by decide),map_zero] at eq
    exact mul_ne_zero ac b0 eq.symm
  let t := (y 0)⁻¹ • y
  have genuine : t≠0 := by
    intro ht
    have zero := congrFun ht 0
    change (y 0)⁻¹*y 0=0 at zero
    rw [inv_mul_cancel₀ y0] at zero
    exact one_ne_zero zero
  have lift (i : Fin 10) : emb ((t i)^8)=branchRatio r i := by
    change emb (((y 0)⁻¹ * y i)^8)=_
    rw [mul_pow,inv_pow,map_mul,map_inv₀,E,E,branchRatio,←div_eq_inv_mul,mul_div_mul_left _ _ ac]
  obtain ⟨e,he⟩ := ratio_field_embedding r emb (fun i => (t i)^8) lift
  have hcor : branchCorrection (fun i => (t i)^8)=branchCorrection (weights r) := by
    have eq := correction_map e (weights r)
    simpa only [he] using eq
  have hc2 := correction_of_coordinates t genuine
  change euclideanHeight t=normalizedHeight t+branchCorrection (fun i => (t i)^8) at hc2
  have nsm : normalizedHeight t=normalizedHeight y := by
    unfold normalizedHeight
    rw [show t=(y 0)⁻¹ • y from rfl,Height.logHeight_smul_eq_logHeight _ (inv_ne_zero y0)]
  have esm : euclideanHeight t=euclideanHeight y := euclideanHeight_smul y (inv_ne_zero y0)
  have hweight := (sup_and_euclidean_of_first hu hd Ω hΩ r hr hz hn h emb z c hc hzθ).1
  rw [esm,nsm,hcor] at hc2
  rw [show euclideanHeight y=euclideanHeight z from hs.2,show normalizedHeight y=absLogHeight z from hs.1] at hc2
  rw [hc2,hweight]
  ring

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.euclidean_of_branches
