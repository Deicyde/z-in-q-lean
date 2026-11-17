import BranchSupMetric

/-! Specialization of Glazer's R22 at the period of the marked sextic. -/
namespace ZInQBlueprint.SixMetric
open ThetaQuotient ThetaPeriod BranchHeight OriginalTheta ZInQ.LeafPush2 ZInQ.DefFaltings PkgI3
noncomputable section

/-- One application to one surface. The common-scale theta witnesses are themselves constructed. -/
theorem branch_le_of_R22 {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    (hR : R22_Pazuki) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : A.dim = (2 : WithBot ℕ∞)) (F X : ℝ) (hF : stableFaltingsHeight A=F)
    (hX : max 1 (F+Real.log Real.pi)≤X) (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φ : (Fin 2 → ℂ) → CPts A σ) (hΦ : IsUniformization σ Λ Φ)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω) (hP : IsPeriodMatrix Λ Ω)
    (detA : ℂ) (hn : detA≠0) (hT : FirstThomae Ω (finiteBranches r) detA) :
    letI := weight_numberField hu hd hz
    normalizedHeight (weights r) ≤ 8*(X/2 + pazukiC2*Real.log (X+2)) := by
  let := weight_numberField hu hd hz
  obtain ⟨L,fL,nL,emb,z,c,hc,he,_⟩ := representative_of_first hu hd Ω hΩ r hr hz hn hT
  have eq := (sup_and_euclidean_of_first hu hd Ω hΩ r hr hz hn hT emb z c hc he).1
  rw [eq]
  exact mul_le_mul_of_nonneg_left (hR K A hA F hF X hX σ Λ Φ hΦ Ω hΩ hP L emb z c hc he) (by norm_num)

private theorem budget_log_bound {y : ℝ} (hy : 1≤y) : Real.log (y+2)≤(23/20)*y := by
  have h := Real.log_le_sub_one_of_pos (show 0<(y+2)/4 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have h4 : Real.log 4 ≤ 7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  linarith

theorem branch_budget_of_R22 {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    (hR : R22_Pazuki) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : A.dim = (2 : WithBot ℕ∞)) (F : ℝ) (hF : stableFaltingsHeight A=F)
    (hrd : F ≤ HeightBudget.vonKaenelBudget u) (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φ : (Fin 2 → ℂ) → CPts A σ) (hΦ : IsUniformization σ Λ Φ)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω) (hP : IsPeriodMatrix Λ Ω)
    (detA : ℂ) (hn : detA≠0) (hT : FirstThomae Ω (finiteBranches r) detA) :
    letI := weight_numberField hu hd hz
    normalizedHeight (weights r) ≤ 2^26 * max 1 (HeightBudget.vonKaenelBudget u) := by
  let := weight_numberField hu hd hz
  let X := max 1 (F+Real.log Real.pi)
  have b := branch_le_of_R22 hu hd r hr hz hR K A hA F X hF le_rfl σ Λ Φ hΦ Ω hΩ hP detA hn hT
  have hX : 1≤X := le_max_left _ _
  have hlogpi : Real.log Real.pi ≤ 7/5 := by
    have b := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at b
    push_cast at b
    linarith [Real.log_two_lt_d9]
  have upper : X ≤ (12/5)*max 1 (HeightBudget.vonKaenelBudget u) := by
    apply max_le <;> linarith [le_max_left (1:ℝ) (HeightBudget.vonKaenelBudget u),
      le_max_right (1:ℝ) (HeightBudget.vonKaenelBudget u)]
  obtain ⟨hc,hC⟩ := ThetaMetric.pazukiConstant_bounds
  change 0≤pazukiC2 at hc
  change pazukiC2≤2760000 at hC
  have m := mul_le_mul_of_nonneg_left (budget_log_bound hX) hc
  have n := mul_le_mul_of_nonneg_right hC (show 0≤(23/20:ℝ)*X by linarith)
  linarith only [b,m,n,upper,le_max_left (1:ℝ) (HeightBudget.vonKaenelBudget u)]

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.branch_le_of_R22
#print axioms ZInQBlueprint.SixMetric.branch_budget_of_R22
