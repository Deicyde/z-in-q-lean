import PicardCurveMap
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedGroupBaseChange
import Nyll.JacobianVarieties.Generalized.ExistingJacobianGroupScheme
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupPullbackIso
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! Scalar extension of represented Picard-zero group sheaves for unpointed curves.
No chosen section is transported through the isomorphism of generic curves. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.GeneralizedJacobian GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed SchemeTheory.RepresentedGroups
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.IntegralPicard
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def scalarSheafIso {R : Type} [CommRing R] {C : Scheme} (c : C ⟶ Spec (.of R))
    (L : Type) [CommRing L] [Algebra R L] :
    ordinaryRelativePicardZeroGroupSheaf (baseChange R c L) ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{1} (specMap R L)).obj
        (ordinaryRelativePicardZeroGroupSheaf c) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of L))) CommGrpCat.{1}).mapIso
    (Unrigidified.zeroCommGrpBaseChangeIso c L) ≪≫
      ((Over.map (specMap R L)).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{1} (Scheme.fppfTopology.over (Spec (.of L)))
        (Scheme.fppfTopology.over (Spec (.of R)))).app (Unrigidified.zeroCommGrpPresheaf c)

private def curveSheafIso {R : Type} [CommRing R] {C D : Over (Spec (.of R))} (e : C ≅ D) :
    ordinaryRelativePicardZeroGroupSheaf C.hom ≅ ordinaryRelativePicardZeroGroupSheaf D.hom :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of R))) CommGrpCat.{1}).mapIso
    (CurveMap.pullIso e.symm)

abbrev Representative {R : Type} [CommRing R] (C X : Over (Spec (.of R))) :=
  ((ordinaryRelativePicardZeroGroupSheaf C.hom).obj ⋙ forget CommGrpCat.{1}).RepresentableBy X

/-- Compare the literal scalar extension of a representing group to a second representation
over the extension ring, given an isomorphism of the actual curves. -/
def baseChangeToRepresentative {R L : Type} [CommRing R] [CommRing L] [Algebra R L]
    {C X : Over (Spec (.of R))} {D Y : Over (Spec (.of L))}
    (hC : Representative C X) (hD : Representative D Y)
    (e : (Over.pullback (specMap R L)).obj C ≅ D) :
    (AbelianModel.baseChange (algebraMap R L)).obj
        (groupObject (ordinaryRelativePicardZeroGroupSheaf C.hom).obj hC) ≅
      groupObject (ordinaryRelativePicardZeroGroupSheaf D.hom).obj hD :=
  groupObjectPullbackIso (specMap R L) _ hC ≪≫ SchemeTheory.RepresentedGroups.iso
    ((Over.map (specMap R L)).op ⋙ (ordinaryRelativePicardZeroGroupSheaf C.hom).obj)
    (ordinaryRelativePicardZeroGroupSheaf D.hom).obj
    (SchemeTheory.WeilRestriction.representableByBaseChange (specMap R L) hC) hD
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of L))) CommGrpCat.{1}).mapIso
      ((scalarSheafIso C.hom L).symm ≪≫ curveSheafIso (C := (Over.pullback (specMap R L)).obj C) (D := D) e))

/-- Over any field extension the genuine group scheme of the unpointed Jacobian commutes
with scalar extension and with any displayed isomorphism of the curve. -/
def unpointed_baseChangeIso {K L : Type} [Field K] [Field L] [Algebra K L]
    (C : Over (Spec (.of K))) (D : Over (Spec (.of L)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper D.hom] [SmoothOfRelativeDimension 1 D.hom] [GeometricallyIrreducible D.hom]
    (e : (Over.pullback (specMap K L)).obj C ≅ D) :
    (AbelianModel.baseChange (algebraMap K L)).obj (groupScheme K C.hom) ≅ groupScheme L D.hom :=
  (AbelianModel.baseChange (algebraMap K L)).mapIso (sheafGroupSchemeIso K C.hom).symm ≪≫
    baseChangeToRepresentative (C:=C) (D:=D) (groupSheafRepresentation K C.hom)
      (groupSheafRepresentation L D.hom) e ≪≫ sheafGroupSchemeIso L D.hom

end
end ZInQBlueprint.IntegralPicard
#print axioms ZInQBlueprint.IntegralPicard.baseChangeToRepresentative
#print axioms ZInQBlueprint.IntegralPicard.unpointed_baseChangeIso
