import RationalBranchHeight

/-! A number-field formulation of the height hypothesis for the paper's branch points. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod ThetaQuotient BranchFormula SexticThetaHeight HeightBudget
noncomputable section
attribute [local instance] Classical.decEq

/-- The weights may be computed over any number field in which their projective ratios lie. -/
theorem height_of_branch_coordinates {K : Type} [Field K] [NumberField K]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0)
    (φ : K →+* ℂ) (v : Fin 10 → K) (hv : ∀ i, φ (v i) = branchRatio r i) :
    ZInQ.ratHeight (SixContact.J u) ≤ 5 * normalizedHeight v + Real.log 3779136 := by
  obtain ⟨hs,he⟩ := paper_pair hu hδ hr hz
  have hsum : φ (∑ i, v i) = (weightField r).val (∑ i, weights r i) := by
    simp only [map_sum,hv]
    rfl
  have hprod : φ (∏ i, v i) = (weightField r).val (∏ i, weights r i) := by
    simp only [map_prod,hv]
    rfl
  apply rational_height
  · intro h
    apply hs
    apply (weightField r).val.injective
    change (weightField r).val (∑ i, weights r i) = (weightField r).val 0
    rw [← hsum,h,map_zero,map_zero]
  · apply φ.injective
    have h := congrArg (weightField r).val he
    simp only [map_div₀,map_mul,map_pow,map_ratCast,map_ofNat] at h ⊢
    rw [hsum,hprod]
    exact h

/-- For a labelled fixed period, projective branch ratios can be represented
by the eighth powers of its normalized even theta coordinates. -/
theorem period_branch_height {u δ : ℚ} {hu : u ∉ ZInQ.contactSet} {hδ : δ ≠ 0}
    (f : LabelledPeriod u δ hu hδ) :
    let e := eighthData f.toThomae
    letI := numberField (chart (thetaNull f.matrix)) (eighth_ratios_algebraic e)
    ∃ v : Fin 10 → fieldOf (chart (thetaNull f.matrix)),
      (∀ i, (v i : ℂ) = branchRatio f.roots i) ∧
      normalizedHeight v ≤ 8 * chartHeight (thetaNull f.matrix) (eighth_ratios_algebraic e) := by
  classical
  let e := eighthData f.toThomae
  let z := thetaNull f.matrix
  let ha := eighth_ratios_algebraic e
  let := numberField (chart z) ha
  let K := fieldOf (chart z)
  let x := coordinates (chart z)
  let pick := fun i => evenIndices (f.label.symm (pairs i))
  let a := (x ∘ pick)^8
  have hx (i : Fin 10) : (a i : ℂ) = z (pick i)^8 / z (evenIndices 0)^8 := by
    change (z (pick i) / z (evenIndices 0))^8 = _
    rw [div_pow]
  have h0 : z (evenIndices 0) ≠ 0 := chart_pivot (eighth_even_nonzero e)
  have hbranch (i : Fin 10) : (a i : ℂ) =
      (f.scale:ℂ) * branchValue (finiteBranches f.roots) (pairs i) / z (evenIndices 0)^8 := by
    rw [hx]
    change thetaNull f.matrix (evenIndices (f.label.symm (pairs i)))^8 / _ = _
    rw [f.thomae, f.label.apply_symm_apply]
  have hp (i : Fin 10) := branchValue_nonzero _ (finiteBranches_injective f.distinct) (pairs i)
  have hnon : a 0 ≠ 0 := by
    intro h
    have hcomp : ((a 0 : K) : ℂ) = 0 := by rw [h]; rfl
    exact div_ne_zero (mul_ne_zero f.scale.ne_zero (hp 0)) (pow_ne_zero 8 h0) ((hbranch 0).symm.trans hcomp)
  let v : Fin 10 → K := (a 0)⁻¹ • a
  refine ⟨v, ?_, ?_⟩
  · intro i
    change (((a 0 : K) : ℂ)⁻¹ * ((a i : K) : ℂ)) = branchRatio f.roots i
    rw [hbranch 0,hbranch i]
    unfold branchRatio
    field_simp [f.scale.ne_zero,hp 0,h0]
  · have h := Height.logHeight_smul_eq_logHeight a (inv_ne_zero hnon)
    have ht : normalizedHeight v = 8 * normalizedHeight (x ∘ pick) := by
      unfold normalizedHeight
      change Height.logHeight ((a 0)⁻¹ • a) / _ = _
      rw [h, show a = (x ∘ pick)^8 from rfl, Height.logHeight_pow]
      push_cast
      ring
    rw [ht]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right
      (Height.logHeight_comp_le pick x) (Nat.cast_nonneg _)).trans
      (normalizedHeight_le_euclideanHeight x)) (by norm_num)

/-- A single arithmetic bound on the projective branch weights of the chosen twist. -/
def BoundedBranchHeight : Prop :=
  ∀ (u : ℚ), u ∉ ZInQ.contactSet → ∃ r : Fin 6 → ℂ, Function.Injective r ∧
    (∀ i, aeval (r i) (sextic u (GlobalTwist.delta u : ℚ)) = 0) ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : K →+* ℂ) (v : Fin 10 → K),
      (∀ i, φ (v i) = branchRatio r i) ∧
      normalizedHeight v ≤ 2^26 * max 1 (vonKaenelBudget u)

theorem boundedBranchHeight_of_fixedPeriods (hp : HasFixedPeriods) : BoundedBranchHeight := by
  intro u hu
  obtain ⟨p⟩ := hp u hu
  let e := eighthData p.toThomae
  let := numberField (chart (thetaNull p.matrix)) (eighth_ratios_algebraic e)
  obtain ⟨v,hv,hb⟩ := period_branch_height p
  refine ⟨p.roots,p.distinct,p.root,_,inferInstance,inferInstance, (fieldOf (chart (thetaNull p.matrix))).val.toRingHom,v,hv,?_⟩
  have ht := ThetaMetric.theta_le _ _ p.comparison
  have hre := max_le_max_left 1 p.reduction
  change normalizedHeight v ≤ _
  change normalizedHeight v ≤ 8 * chartHeight (thetaNull p.matrix) (eighth_ratios_algebraic e) at hb
  change chartHeight (thetaNull p.matrix) (eighth_ratios_algebraic e) ≤ 2^23 * max 1 p.stable at ht
  linarith only [hb,ht,hre]

theorem remaining_of_branchHeight (hp : BoundedBranchHeight) : RemainingComparisons := by
  intro u hu
  obtain ⟨r,hr,hz,K,_,_,φ,v,hv,hb⟩ := hp u hu
  have hδ : (GlobalTwist.delta u : ℚ) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  have h := height_of_branch_coordinates hu hδ hr hz φ v hv
  refine ⟨normalizedHeight v / 8, ?_, ?_⟩
  · linarith only [h,log_coefficient_le]
  · linarith only [hb,le_max_left (1:ℝ) (vonKaenelBudget u)]

theorem sixContactMin_of_branchHeight (h : BoundedBranchHeight) : ZInQ.SixContactMin :=
  sixContactMin_of_remaining (remaining_of_branchHeight h)

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.height_of_branch_coordinates
#print axioms ZInQBlueprint.BranchHeight.period_branch_height
#print axioms ZInQBlueprint.BranchHeight.boundedBranchHeight_of_fixedPeriods
#print axioms ZInQBlueprint.BranchHeight.remaining_of_branchHeight
#print axioms ZInQBlueprint.BranchHeight.sixContactMin_of_branchHeight
