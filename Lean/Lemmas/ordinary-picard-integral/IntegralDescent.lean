import OrdinarySection
import OrdinaryRelativeDimension
import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedDescent
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence

/-! Effective descent of the relative Picard scheme of a sectionless curve
along a finite faithfully flat local algebra. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.IntegralPicard
noncomputable section

/-- The descent comparison identifies an actual pointed Picard representative
after the displayed scalar extension and intertwines its canonical descent action. -/
structure Presentation (R : Type) [CommRing R] {C : Scheme.{0}} (c : C ⟶ Spec (.of R))
    (A : Type) [CommRing A] [Algebra R A] where
  localSection : SchemeHomOver (𝟙 (Spec (.of A))) (baseChange R c A)
  picard : RelativePic0Designation A (baseChange R c A)
  represents : RepresentsRelSubPic (baseChange R c A) localSection
    (algEquivZeroCut (baseChange R c A) localSection) picard
  carrier : Scheme
  toBase : carrier ⟶ Spec (.of R)
  smooth : Smooth toBase
  proper : IsProper toBase
  connected : GeometricallyConnected toBase
  comparison : pullback toBase (specMap R A) ≅ picard.P
  comparison_over : comparison.hom ≫ picard.toBase = pullback.snd toBase (specMap R A)
  descent : DescentAction.eRel (specMap R A) picard.toBase toBase comparison comparison_over ≫
    (descentAction c A localSection represents).act =
    (DescentAction.canonical (specMap R A) toBase).act ≫ comparison.hom

/-- Over any reduced noetherian local splitting algebra, existence of a section
is enough to carry out effective projective descent over the original ring. -/
theorem exists_presentation (R : Type) [CommRing R] {C : Scheme} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (A : Type) [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsReduced A]
    [Module.Finite R A] [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (ε : SchemeHomOver (𝟙 (Spec (.of A))) (baseChange R c A)) : Nonempty (Presentation R c A) := by
  let d := baseChange R c A
  have hF (m : ℕ) : ∃ F : FiniteMapData d ε, m ≤ F.m ∧ F.LevelSetsGenericallyEtale := by
    obtain ⟨F,hm,hu⟩ := exists_finiteMapData_le_isUnit A d ε m
    exact ⟨F,hm,exists_polynomial_isUnit_aeval_imp_etale_levelSet A d ε
      F.U F.isAffineOpen_U F.mem_U_iff F.f F.m hu F.levelSet_free⟩
  obtain ⟨D,⟨h⟩,hsm,hpr,hgc⟩ := exists_representsRelSubPic_of_local_finiteMapData A d ε hF
  have haff := exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
    A d ε (fun m => (hF m).imp fun F hF => hF.1) D h hsm hpr hgc
  obtain ⟨P,p,e,he,hc⟩ := descentAction_effective c A ε h haff
  obtain ⟨hs,hp,hg⟩ := smooth_isProper_geometricallyConnected_of_faithfullyFlat_baseChange
    R A p D.toBase hsm hpr hgc e he
  exact ⟨⟨ε,D,h,P,p,hs,hp,hg,e,he,hc⟩⟩

end
end ZInQBlueprint.IntegralPicard
#print axioms ZInQBlueprint.IntegralPicard.exists_presentation
