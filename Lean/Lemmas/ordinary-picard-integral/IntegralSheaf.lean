import IntegralDescent
import Nyll.JacobianVarieties.Generalized.ExistingJacobianSheafRepresentation

/-! The integral carrier represents the unpointed fppf Picard-zero sheaf.
The sheaf carries the tensor-product group law, including over bases without a section. -/
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.GeneralizedJacobian NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.IntegralPicard
noncomputable section

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
  {C : Scheme} {c : C ⟶ Spec (.of R)} (P : Presentation R c A)

def Presentation.sheafRepresentation :
    (ordinaryRelativePicardZeroSheaf c).obj.RepresentableBy (Over.mk P.toBase) := by
  have : Flat (specMap R A) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (specMap R A) := ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : LocallyOfFinitePresentation (specMap R A) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let F := Unrigidified.zeroPresheaf c
  let eRaw := representableByRestrict c A P.localSection P.represents
  let eSheaf := DescentAction.sheafifiedLocalRepresentation (specMap R A) F P.picard.toBase eRaw
  have hc : DescentAction.eRel (specMap R A) P.picard.toBase P.toBase P.comparison
      P.comparison_over ≫ DescentAction.repAct (specMap R A) (ordinaryRelativePicardZeroSheaf c).obj
      P.picard.toBase eSheaf = (DescentAction.canonical (specMap R A) P.toBase).act ≫ P.comparison.hom :=
    (congrArg (fun a => DescentAction.eRel (specMap R A) P.picard.toBase P.toBase P.comparison
      P.comparison_over ≫ a)
      (DescentAction.repAct_sheafifiedLocalRepresentation (specMap R A) F P.picard.toBase eRaw)).trans P.descent
  exact DescentAction.globalRepresentation (specMap R A) (ordinaryRelativePicardZeroSheaf c).obj
    P.picard.toBase eSheaf P.toBase P.comparison P.comparison_over
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap R A) (ordinaryRelativePicardZeroSheaf c).obj
      (ordinaryRelativePicardZeroSheaf c).property) hc

def Presentation.groupRepresentation :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙ forget CommGrpCat.{1}).RepresentableBy
      (Over.mk P.toBase) :=
  P.sheafRepresentation.ofIso (ordinaryRelativePicardZeroGroupSheafForgetIso c).symm

def Presentation.group : AbelianModel.GroupScheme R :=
  SchemeTheory.RepresentedGroups.groupObject (ordinaryRelativePicardZeroGroupSheaf c).obj
    P.groupRepresentation

theorem Presentation.isAbelian : AbelianModel.IsAbelianScheme P.group :=
  ⟨P.proper,P.smooth,P.connected⟩

end
end ZInQBlueprint.IntegralPicard
#print axioms ZInQBlueprint.IntegralPicard.Presentation.sheafRepresentation
#print axioms ZInQBlueprint.IntegralPicard.Presentation.groupRepresentation
#print axioms ZInQBlueprint.IntegralPicard.Presentation.group
#print axioms ZInQBlueprint.IntegralPicard.Presentation.isAbelian
