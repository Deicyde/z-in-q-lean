import RationalJacobian
import PaperCohomology

/-! The two charts and the two surviving odd Laurent coefficients compute the dimension
of the rational Jacobian defined by unpointed descent. -/
open CategoryTheory AlgebraicGeometry Opposite
open ZInQBlueprint.BinaryCover ZInQBlueprint.BinaryCover.Cech
namespace ZInQBlueprint.SixJacobian
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

def twoCharts (u : ℚ) : (paperModel ℚ u).left.TwoAffineOpenCover where
  U0 := atlasOpen ℚ _ _ (paper_overlap ℚ u) (some false)
  U1 := atlasOpen ℚ _ _ (paper_overlap ℚ u) (some true)
  isAffineOpen_U0 := @isAffineOpen_opensRange _ _
    (inferInstanceAs (IsAffine (Spec (.of (Cover (paper ℚ u false)))))) _ inferInstance
  isAffineOpen_U1 := @isAffineOpen_opensRange _ _
    (inferInstanceAs (IsAffine (Spec (.of (Cover (paper ℚ u true)))))) _ inferInstance
  sup_eq_top := atlas_union _ _ _ _
  isAffineOpen_inf := (atlas_intersection ℚ _ _ (paper_overlap ℚ u)) ▸
    @isAffineOpen_opensRange _ _ (inferInstanceAs (IsAffine (Spec (.of (Punctured ℚ (paper ℚ u false))))))
      (atlasMap ℚ _ _ (paper_overlap ℚ u) none) inferInstance

private def difference {X : Scheme.{0}} (U V W : X.Opens) (i : W ≤ U) (j : W ≤ V) :
    Γ(X,U) × Γ(X,V) →+ Γ(X,W) :=
  (((X.presheaf.map (homOfLE i).op).hom.toAddMonoidHom).comp (AddMonoidHom.fst _ _)) -
  (((X.presheaf.map (homOfLE j).op).hom.toAddMonoidHom).comp (AddMonoidHom.snd _ _))

/-- Reversing the sign convention for the two restrictions preserves their range.
This comparison also transports the chosen geometric overlap along its precise equality. -/
private def signedCokernel {X : Scheme.{0}} (c : X ⟶ Spec (.of ℚ)) (v : X.TwoAffineOpenCover)
    (W : X.Opens) (h : W=v.U0 ⊓ v.U1) :
    (v.structureSheafSections c).H1 ≃+
      Γ(X,W) ⧸ (difference v.U0 v.U1 W (h ▸ inf_le_left) (h ▸ inf_le_right)).range := by
  subst W
  let D := difference v.U0 v.U1 (v.U0 ⊓ v.U1) inf_le_left inf_le_right
  let S := v.structureSheafSections c
  have rev (a : Γ(X,v.U0)) (b : Γ(X,v.U1)) : S.cechDiff (a,b) = -D (a,b) := by
    rw [TwoChartCech.Sections.cechDiff_apply]
    change (1 : Γ(X,v.U0 ⊓ v.U1)) * _ - _ = -(_ - _)
    rw [one_mul, neg_sub]
    rfl
  apply QuotientAddGroup.congr _ _ (AddEquiv.refl Γ(X,v.U0 ⊓ v.U1))
  ext z
  constructor
  · rintro ⟨_,⟨⟨a,b⟩,rfl⟩,rfl⟩
    exact ⟨-(a,b), (map_neg D (a,b)).trans (rev a b).symm⟩
  · rintro ⟨⟨a,b⟩,rfl⟩
    refine ⟨_,⟨-(a,b),rfl⟩,?_⟩
    change S.cechDiff (-(a,b)) = D (a,b)
    rw [map_neg,rev,neg_neg]

/-- This comparison is with the first Čech group that appears in the external
geometric genus theorem; its two coordinates are actual Laurent coefficients. -/
def paperGenusCoordinates (u : ℚ) :
    ((twoCharts u).structureSheafSections (paperModel ℚ u).hom).H1 ≃ₗ[ℚ] ℚ × ℚ := by
  let e := signedCokernel (paperModel ℚ u).hom (twoCharts u) _
    (atlas_intersection ℚ _ _ (paper_overlap ℚ u))
  let f := (coordinateQuotient ℚ (paper_overlap ℚ u)).trans
    (quotientEquiv ℚ (paper_overlap ℚ u)).toAddEquiv
  let E := e.trans f
  exact { E with map_smul' := map_rat_smul E }

theorem geometricGenus_two {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := geometricallyIntegral_paperModel hu
    SmoothProperCurve.geometricGenus ℚ (paperModel ℚ u).hom = 2 := by
  let M := paperModel ℚ u
  let : IsProper M.hom := paper_proper ℚ u
  let : Smooth M.hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral M.left := paper_reglued_integral ℚ hu
  let : GeometricallyIntegral M.hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 M.hom := relative_dimension_one _ (paper_dimension ℚ u)
  rw [← SmoothProperCurve.finrank_H1_eq_geometricGenus ℚ M.hom (twoCharts u),
    (paperGenusCoordinates u).finrank_eq]
  simp

/-- The commutative abelian variety constructed from the paper curve is a surface. -/
theorem jacobian_dimension_two {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SmoothOfRelativeDimension 2 (jacobian hu).X.hom := by
  let M := paperModel ℚ u
  let : IsProper M.hom := paper_proper ℚ u
  let : Smooth M.hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral M.left := paper_reglued_integral ℚ hu
  let : GeometricallyIntegral M.hom := geometricallyIntegral_paperModel hu
  let : SmoothOfRelativeDimension 1 M.hom := relative_dimension_one _ (paper_dimension ℚ u)
  rw [← geometricGenus_two hu]
  exact JacobianVarieties.Picard.Unpointed.smoothOfRelativeDimension ℚ M.hom

end
end ZInQBlueprint.SixJacobian
#print axioms ZInQBlueprint.SixJacobian.paperGenusCoordinates
#print axioms ZInQBlueprint.SixJacobian.geometricGenus_two
#print axioms ZInQBlueprint.SixJacobian.jacobian_dimension_two
