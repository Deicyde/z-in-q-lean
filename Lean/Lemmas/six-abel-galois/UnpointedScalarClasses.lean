import CoefficientSections
import UnpointedBaseChange

/-! Pointwise description of the very base-change isomorphism retained by the rational model. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra Opposite GoodReductionJacobian JacobianVarieties.Picard.Unpointed
open SchemeTheory.RepresentedGroups
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K L : Type} [Field K] [Field L] [Algebra K L] (C : Over (Spec (.of K)))
local notation "s" => specMap K L
set_option quotPrecheck false
local notation "Cₗ" => (Over.pullback s).obj C
local notation "j₁" => Scheme.fppfTopology.over (Spec (.of K))
local notation "j₂" => Scheme.fppfTopology.over (Spec (.of L))

abbrev scalarClasses :
    ordinaryRelativePicardZeroGroupSheaf (Cₗ).hom ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{1} s).obj (ordinaryRelativePicardZeroGroupSheaf C.hom) :=
  (presheafToSheaf j₂ CommGrpCat.{1}).mapIso (Unrigidified.zeroCommGrpBaseChangeIso C.hom L) ≪≫
    ((Over.map s).pushforwardContinuousSheafificationCompatibility CommGrpCat.{1} j₂ j₁).app
      (Unrigidified.zeroCommGrpPresheaf C.hom)

theorem scalarClasses_unit (T : Over (Spec (.of L))) (v : (Unrigidified.zeroCommGrpPresheaf (Cₗ).hom).obj (op T)) :
    (scalarClasses C).hom.hom.app (op T)
      ((toSheafify j₂ (Unrigidified.zeroCommGrpPresheaf (Cₗ).hom)).app (op T) v) =
    (toSheafify j₁ (Unrigidified.zeroCommGrpPresheaf C.hom)).app (op ((Over.map s).obj T))
      ((Unrigidified.zeroCommGrpBaseChangeIso C.hom L).hom.app (op T) v) := by
  let F := Unrigidified.zeroCommGrpPresheaf C.hom
  let a := (Unrigidified.zeroCommGrpBaseChangeIso C.hom L).hom
  let e := (Over.map s).pushforwardContinuousSheafificationCompatibility CommGrpCat.{1} j₂ j₁
  let q := a.app (op T) v
  change (e.hom.app F).hom.app (op T) ((sheafifyMap j₂ a).app (op T) _) = _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality j₂ a) (op T)) v
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app
    ((Over.map s).toSheafify_pullbackSheafificationCompatibility CommGrpCat.{1} j₂ j₁ F) (op T)) q
  exact (congrArg ((e.hom.app F).hom.app (op T)) h.symm).trans h'

private theorem pull_identity (X : Over (Spec (.of L))) :
    (IntegralPicard.CurveMap.pullIso (Iso.refl X)).hom = 𝟙 _ := by
  ext T x
  obtain ⟨x,hx⟩ := x
  apply Subtype.ext
  induction x using Quot.ind with
  | _ M =>
    apply Quot.sound
    apply Unrigidified.baseTwist_of_iso
    exact (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left ((Over.pullback T.unop.hom).map_id X))).app M.1 ≪≫
      (Scheme.Modules.pullbackId _).app M.1

private theorem selfComparison {S : Scheme} {G : (Over S)ᵒᵖ ⥤ Type 1} {X : Over S}
    (h : G.RepresentableBy X) : (h.uniqueUpToIso h).inv = 𝟙 _ := h.homEquiv.symm_apply_apply _

open IntegralPicard
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]
theorem carrier_scalar_class (T : Over (Spec (.of L))) (w : T ⟶ (Over.pullback s).obj (groupScheme K C.hom).X) :
    let _ : IsProper (Cₗ).hom := inferInstanceAs (IsProper (pullback.snd C.hom s))
    let _ : SmoothOfRelativeDimension 1 (Cₗ).hom := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd C.hom s))
    let _ : GeometricallyIntegral (Cₗ).hom := inferInstanceAs (GeometricallyIntegral (pullback.snd C.hom s))
    (groupSheafRepresentation L (Cₗ).hom).homEquiv (w ≫ (unpointed_baseChangeIso C Cₗ (Iso.refl _)).hom.hom.hom.hom) =
      (scalarClasses C).inv.hom.app (op T)
        ((groupSheafRepresentation K C.hom).homEquiv (((Over.mapPullbackAdj s).homEquiv T _).symm w)) := by
  intro _ _ _
  change T ⟶ (Over.pullback s).obj (Over.mk (toBase K C.hom)) at w
  let F := (Over.map s).op ⋙ (ordinaryRelativePicardZeroGroupSheaf C.hom).obj
  let G := (ordinaryRelativePicardZeroGroupSheaf (Cₗ).hom).obj
  let hF := SchemeTheory.WeilRestriction.representableByBaseChange s (groupSheafRepresentation K C.hom)
  let hG := groupSheafRepresentation L (Cₗ).hom
  let a := (scalarClasses (L:=L) C).inv.hom
  let b := sheafifyMap j₂ (IntegralPicard.CurveMap.pullIso (Iso.refl Cₗ)).hom
  change hG.homEquiv (w ≫ (Over.pullback s).map (𝟙 (Over.mk (toBase K C.hom))) ≫
    ((hF.uniqueUpToIso hF).inv ≫ mapMorphism F G hF hG (a ≫ b)) ≫ 𝟙 _) =
    (a.app (op T)).hom (hF.homEquiv w)
  rw [(Over.pullback s).map_id (Over.mk (toBase K C.hom)),Category.id_comp,selfComparison,Category.id_comp,Category.comp_id,
    mapMorphism_homEquiv]
  have hb : b = 𝟙 G := by
    dsimp only [b]
    rw [pull_identity,sheafifyMap_id]
    rfl
  rw [hb,Category.comp_id]
  rfl

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.scalarClasses_unit
#print axioms ZInQBlueprint.AbelGalois.carrier_scalar_class
