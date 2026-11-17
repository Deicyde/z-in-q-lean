import ProjectiveHeightDescent
import CanonicalBranch

/-! Descent of a fixed period's projective branch height to the intrinsic coordinate field. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod ThetaQuotient SexticThetaHeight
noncomputable section

/-- The field of the normalized ratios embeds into every field realizing those ratios. -/
theorem ratio_field_embedding {K : Type*} [Field K] [CharZero K]
    (r : Fin 6 → ℂ) (f : K →+* ℂ) (x : Fin 10 → K) (hx : ∀ i, f (x i)=branchRatio r i) :
    ∃ e : weightField r →+* K, ∀ i, e (weights r i) = x i := by
  let g := f.toRatAlgHom
  have hle : weightField r ≤ g.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨x i,hx i⟩
  let j := IntermediateField.inclusion hle
  let e := g.equivFieldRange.symm.toAlgHom.comp j
  refine ⟨e.toRingHom,?_⟩
  intro i
  apply g.equivFieldRange.injective
  change g.equivFieldRange (g.equivFieldRange.symm (j (weights r i))) = _
  rw [g.equivFieldRange.apply_symm_apply]
  apply Subtype.ext
  exact (hx i).symm

/-- Every realization of the normalized branch ratios has exactly their intrinsic height. -/
theorem intrinsic_height_eq {K : Type*} [Field K] [NumberField K]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) {r : Fin 6 → ℂ}
    (hz : ∀ i, aeval (r i) (sextic u δ) = 0) (f : K →+* ℂ)
    (x : Fin 10 → K) (hx : ∀ i, f (x i) = branchRatio r i) :
    letI := weight_numberField hu hδ hz
    normalizedHeight (weights r) = normalizedHeight x := by
  let := weight_numberField hu hδ hz
  obtain ⟨e,he⟩ := ratio_field_embedding r f x hx
  have hd := HeightDescent.normalizedHeight_map e (weights r)
  rw [show (fun i => e (weights r i))=x from funext he] at hd
  exact hd.symm

theorem canonical_of_untwisted (h : UntwistedBranchHeight) : CanonicalBranchBound := by
  intro u hu
  obtain ⟨r,hr,hz,K,hK,hN,f,x,hx,hb⟩ := h u hu
  refine ⟨r,hr,hz,?_⟩
  exact (intrinsic_height_eq hu one_ne_zero hz f x hx).le.trans hb

/-- The existential coordinate-field and intrinsic coordinate-field formulations are equivalent. -/
theorem canonical_iff_bounded : CanonicalBranchBound ↔ BoundedBranchHeight :=
  ⟨fun h => untwisted_iff.mp (untwisted_of_canonical h),fun h => canonical_of_untwisted (untwisted_iff.mpr h)⟩

/-- The fixed labelled periods bound the branch heights in their own intrinsic fields. -/
theorem canonical_of_fixedPeriods (h : HasFixedPeriods) : CanonicalBranchBound :=
  canonical_iff_bounded.mpr (boundedBranchHeight_of_fixedPeriods h)

/-- Thomae's eighth powers give a pointwise, lossless transfer to the intrinsic coordinate field. -/
theorem period_intrinsic_height {u δ : ℚ} {hu : u ∉ ZInQ.contactSet} {hδ : δ ≠ 0}
    (p : LabelledPeriod u δ hu hδ) :
    let e := eighthData p.toThomae
    letI := weight_numberField hu hδ p.root
    normalizedHeight (weights p.roots) ≤
      8 * chartHeight (thetaNull p.matrix) (eighth_ratios_algebraic e) := by
  let e := eighthData p.toThomae
  let := numberField (chart (thetaNull p.matrix)) (eighth_ratios_algebraic e)
  obtain ⟨x,hx,hb⟩ := period_branch_height p
  exact (intrinsic_height_eq hu hδ p.root (fieldOf (chart (thetaNull p.matrix))).val.toRingHom x hx).le.trans hb

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.ratio_field_embedding
#print axioms ZInQBlueprint.BranchHeight.intrinsic_height_eq
#print axioms ZInQBlueprint.BranchHeight.canonical_of_untwisted
#print axioms ZInQBlueprint.BranchHeight.canonical_iff_bounded
#print axioms ZInQBlueprint.BranchHeight.canonical_of_fixedPeriods
#print axioms ZInQBlueprint.BranchHeight.period_intrinsic_height
