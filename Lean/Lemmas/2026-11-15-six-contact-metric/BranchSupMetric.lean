import EilersPowers
import SparseMetric
import BranchHeightDescent

/-! Exact projective sup height of the theta tuple in the two different coordinate fields. -/
namespace ZInQBlueprint.SixMetric
open OriginalTheta ThetaPeriod ThetaQuotient BranchFormula BranchHeight ZInQ.LeafPush2
noncomputable section

set_option maxHeartbeats 500000 in
theorem sup_and_euclidean_of_first {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    {detA : ℂ} (hn : detA≠0) (h : FirstThomae Ω (finiteBranches r) detA)
    {L : Type} [Field L] [NumberField L] (emb : L →+* ℂ) (z : Char2 → L)
    (c : ℂ) (hc : c≠0) (hzθ : ∀ m, emb (z m)=c*thetaConst Ω m) :
    letI := weight_numberField hu hd hz
    normalizedHeight (weights r)=8*absLogHeight z ∧
    absLogHeight z ≤ euclideanHeight z ∧ euclideanHeight z ≤ absLogHeight z + Real.log 10/2 := by
  let := weight_numberField hu hd hz
  let y := z ∘ pairChar
  have off (m : Char2) (hm : ¬ ∃ i, pairChar i=m) : z m=0 := by
    have hn₀ : dotParity m ≠ 0 := fun e => hm ((even_unique m).mp e).exists
    have ho : dotParity m=1 := by have b := (dotParity m).isLt; omega
    apply emb.injective
    rw [hzθ,thetaConst_odd Ω hΩ m ho,map_zero,mul_zero]
  have hs := sparse_heights pairChar pairChar_injective z off
  let a := y ^ 8
  have E (i : Fin 10) : emb (a i) = (c^8 * (scaleOf detA hn:ℂ)) * branchValue (finiteBranches r) (pairs i) := by
    change emb ((z (pairChar i))^8)=_
    rw [map_pow,hzθ,mul_pow,pairChar_eq,eighth_of_first hn h]
    simp [eilersLabel]
    ring
  have non (i : Fin 10) : branchValue (finiteBranches r) (pairs i)≠0 :=
    branchValue_nonzero _ (finiteBranches_injective hr) _
  have common : c^8*(scaleOf detA hn:ℂ)≠0 := mul_ne_zero (pow_ne_zero _ hc) (scaleOf detA hn).ne_zero
  have a0 : a 0≠0 := by
    intro h₀
    have e := E 0
    rw [h₀,map_zero] at e
    exact (mul_ne_zero common (non 0)) e.symm
  let b := (a 0)⁻¹ • a
  have hb (i : Fin 10) : emb (b i)=branchRatio r i := by
    change emb ((a 0)⁻¹*a i)=_
    rw [map_mul,map_inv₀]
    rw [E 0,E i,branchRatio,←div_eq_inv_mul,mul_div_mul_left _ _ common]
  have hi := intrinsic_height_eq hu hd hz emb b hb
  have he : normalizedHeight b=8*normalizedHeight y := by
    unfold normalizedHeight
    change Height.logHeight ((a 0)⁻¹ • a)/_ = _
    rw [Height.logHeight_smul_eq_logHeight _ (inv_ne_zero a0),show a=y^8 from rfl,Height.logHeight_pow]
    push_cast
    ring
  refine ⟨hi.trans (he.trans (by rw [show normalizedHeight y = absLogHeight z from hs.1])),normalizedHeight_le_euclideanHeight z,?_⟩
  have hupp := euclidean_upper y
  rw [show euclideanHeight y=euclideanHeight z from hs.2,
      show normalizedHeight y=absLogHeight z from hs.1] at hupp
  simpa using hupp

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.sup_and_euclidean_of_first
