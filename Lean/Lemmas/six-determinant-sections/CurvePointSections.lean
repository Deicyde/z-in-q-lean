import SignedDifferenceMap
import Nyll.AlgebraicCurves.Models.FinrankH0SectionsOfInvModuleProdKerTensorModuleProdKerEqEll
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverLinearEquivSectionsOfH0

/-! One point of the signed curve has just one independent section.
The divisor sheaf is the inverse point ideal, tensor the module of the unit ideal. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve MonoidalCategory
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap BinaryCover GeometricMarking NormalDescent CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
variable {u : ℚ}

/-- NYLL's divisor-line convention with positive part [p] and empty negative part. -/
abbrev pointLine (p : CurvePoints u) : (paperCurve u).left.Modules :=
  p.left.ker.invModule ⊗ (⊤ : (paperCurve u).left.IdealSheafData).module

theorem pointLine_rank (hu : u ∉ ZInQ.contactSet) (p : CurvePoints u) :
    ThetaLinearSystem.rankH0 (paperCurve u).hom (pointLine p)=1 := by
  let c := (paperCurve u).hom
  let I := sourceIntegral hu
  let := (baseToFunctionField c).toAlgebra
  let M := signedModel hu
  let := M.curve
  let := paper_essentially_finite hu
  let : IsProper c := by
    let := paper_proper ℚ u
    exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : GeometricallyIntegral c := by
    let := geometricallyIntegral_paperModel hu
    exact inferInstanceAs (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : SmoothOfRelativeDimension 1 c := by
    let s := (paperModel ℚ u).hom
    let : Smooth s := smooth_paperModel hu
    let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
    let : SmoothOfRelativeDimension 1 s := SixJacobian.relative_dimension_one s (paper_dimension ℚ u)
    exact inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd s (scalarMap ℚ Qbar)))
  obtain ⟨𝒱,-,-⟩ := SmoothProperCurve.exists_twoAffineOpenCover_of_section Qbar c (schemePoint p)
  let P : Fin 1 → {p : Spec (.of Qbar) ⟶ (paperCurve u).left // p ≫ c = 𝟙 _} := fun _ => ⟨p.left,p.w⟩
  let Q : Fin 0 → {p : Spec (.of Qbar) ⟶ (paperCurve u).left // p ≫ c = 𝟙 _} := Fin.elim0
  have h := (CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
    c M.model M.iso M.hbase P Q 𝒱).2.2
  have ℓ (v : Place Qbar (paperCurve u).left.functionField) :
      ell (Finsupp.single v 1) = 1 := by
    obtain ⟨t,ht,hfin,-⟩ := IsCurveOver.exists_separating_transcendental (K:=Qbar) (F:=(paperCurve u).left.functionField)
    have hC := constantsAreBase_of_isAlgClosed_of_transcendental t ht
    change Module.finrank Qbar (LSpace (Finsupp.single v 1)) = 1
    have pos : 0 < genusFF Qbar (paperCurve u).left.functionField := by rw [paper_functionField_genus hu]; decide
    rw [lSpace_point_eq_constants pos v]
    exact ell_zero_eq_one_of_constantsAreBase hC
  have product : (∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module = pointLine p := by
    simp only [Fin.prod_univ_one,Finset.univ_eq_empty,Finset.prod_empty,Scheme.IdealSheafData.one_eq_top]
    rfl
  rw [product] at h
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c (pointLine p) ⊤
  obtain ⟨e,-⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 c (pointLine p)
  apply e.finrank_eq.trans
  simpa only [Fin.prod_univ_one,Finset.univ_eq_empty,Finset.prod_empty,Finset.sum_empty,sub_zero,
    Fin.sum_univ_one,ℓ] using h

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.pointLine_rank
