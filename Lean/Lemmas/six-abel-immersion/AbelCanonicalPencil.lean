import SignedAbelSeparation
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.GenusOneDivisors

/-! In positive genus, L(P) consists of constants and every point imposes one
linear condition on the canonical system. For the signed fibre the two dimensions are 2 and 1. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open JacobianVarieties.Picard.Unpointed GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent KaehlerDifferential
namespace ZInQBlueprint.SixAbelMap
noncomputable section
open BinaryCover GeometricMarking NormalDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- A simple pole at just one specified place is impossible on a positive-genus curve. -/
theorem lSpace_point_eq_constants (hg : 0 < genusFF K F) (P : Place K F) :
    LSpace (Finsupp.single P 1) = LSpace (0 : Divisor K F) := by
  classical
  apply le_antisymm
  · intro f hf
    by_cases hf0 : f = 0
    · rw [hf0]; exact Submodule.zero_mem _
    have ord := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
    let := IsCurveOver.hasPrincipalDivisors (K := K) (F := F)
    obtain ⟨D, hd, deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    let S : Divisor K F := Finsupp.single P 1
    have eff (v : Place K F) : 0 ≤ (S + D) v := by
      rw [Finsupp.add_apply, hd]
      have h := ord v
      change -S v ≤ _ at h
      omega
    have hdeg : (S + D).degree = 1 := by
      change Divisor.degree ((Finsupp.single P 1 : Divisor K F) + D) = 1
      rw [map_add, deg, add_zero, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
      norm_num
    obtain ⟨Q, hQ⟩ := Divisor.exists_single_of_effective_degree_one (S + D) eff hdeg
    have hD : Finsupp.single Q 1 - S = D := by rw [← hQ]; abel
    have hQP := eq_of_single_sub_single_principal_of_genus_pos hg Q P
      (by change Divisor.IsPrincipal (Finsupp.single Q 1 - S); rw [hD]; exact ⟨f, hf0, hd⟩)
    have hzero : D = 0 := by rw [←hD,hQP]; exact sub_self _
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    rw [←hd v, hzero]
    simp
  · apply lSpace_mono
    intro v
    simp only [Finsupp.zero_apply, Finsupp.single_apply]
    split_ifs <;> norm_num

/-- The canonical system loses exactly one dimension on imposing vanishing at a place. -/
theorem canonical_point_dimensions (hg : 0 < genusFF K F) (P : Place K F)
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    ell (canonicalDivisorOf hω) = genusFF K F ∧
      ell (canonicalDivisorOf hω - Finsupp.single P 1) + 1 = genusFF K F := by
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRR : FunctionFieldRiemannRoch K F := functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht hfin
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hWA : WeilDualityAdelic K F := weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR
    (stichtenothGenusExists_of_isCurveOver hC)
  have hg' := genus_eq_genusFF hRR hWA hC
  have h0 := ell_zero_eq_one_of_constantsAreBase hC
  have hp : ell (Finsupp.single P 1) = 1 := by
    change Module.finrank K (LSpace (Finsupp.single P 1)) = 1
    rw [lSpace_point_eq_constants hg P]
    exact h0
  have hzero := hRR hω 0
  rw [sub_zero, map_zero, h0, hg'] at hzero
  have hpoint := hRR hω (Finsupp.single P 1)
  rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, hp, hg'] at hpoint
  norm_num at hzero hpoint
  constructor <;> omega

theorem paper_essentially_finite {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    Algebra.EssFiniteType Qbar (paperCurve u).left.functionField := by
  let := sourceIntegral hu
  have := paper_proper ℚ u
  let : IsProper (paperCurve u).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  exact essFiniteType_functionField (paperCurve u).hom

/-- For each geometric place of the signed curve the full canonical pencil has
dimension two, and the subspace vanishing at the place has dimension one. -/
theorem paper_canonical_pencil {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    letI := (signedModel hu).curve
    letI := paper_essentially_finite hu
    let F : Type := (paperCurve u).left.functionField
    letI : HasCanonicalDivisor (K := Qbar) (F := F) := hasCanonicalDivisor_of_isCurveOver
    ∀ (P : Place Qbar F) (ω : Ω[F⁄Qbar]) (hω : ω ≠ 0),
      ell (canonicalDivisorOf hω) = 2 ∧ ell (canonicalDivisorOf hω - Finsupp.single P 1) = 1 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let := paper_essentially_finite hu
  let F : Type := (paperCurve u).left.functionField
  let : HasCanonicalDivisor (K:=Qbar) (F:=F) := hasCanonicalDivisor_of_isCurveOver
  let : ∀ v : Place Qbar F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  change ∀ (P : Place Qbar F) (ω : Ω[F⁄Qbar]) (hω : ω ≠ 0), _
  intro P ω hω
  have hgen : genusFF Qbar F = 2 := paper_functionField_genus hu
  obtain ⟨h1,h2⟩ := canonical_point_dimensions (by omega : 0 < genusFF Qbar F) P hω
  omega

end
end ZInQBlueprint.SixAbelMap

#print axioms ZInQBlueprint.SixAbelMap.lSpace_point_eq_constants
#print axioms ZInQBlueprint.SixAbelMap.canonical_point_dimensions
#print axioms ZInQBlueprint.SixAbelMap.paper_canonical_pencil
