import RepresentedPointDifferences
import RigidifiedAbel

/-! The raw Picard classification of a pointed curve and its fppf classification
on the unpointed descent carrier give the same universal class. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.GeneralizedJacobian
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Picard.Unpointed Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem descended_unit {S S' : Scheme} (s : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ Type 1)
    {X' : Scheme} (x' : X' ⟶ S')
    (eG : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))
    {X : Scheme} (f : X ⟶ S) (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s)
    (hG : ∀ T, Presieve.IsSheafFor G (Presieve.singleton (DescentAction.coverT s T)))
    (hc : DescentAction.eRel s x' f e he ≫ DescentAction.repAct s G x' eG =
      (DescentAction.canonical s f).act ≫ e.hom)
    (hH : ∀ T, Presieve.IsSheafFor (sheafify (Scheme.fppfTopology.over S) G)
      (Presieve.singleton (DescentAction.coverT s T)))
    (hc' : DescentAction.eRel s x' f e he ≫ DescentAction.repAct s
      (sheafify (Scheme.fppfTopology.over S) G) x'
      (DescentAction.sheafifiedLocalRepresentation s G x' eG) =
      (DescentAction.canonical s f).act ≫ e.hom)
    [∀ T : Over S, EffectiveEpi (pullback.fst T.hom s)] {T : Over S} (m : T ⟶ Over.mk f) :
    (DescentAction.globalRepresentation s (sheafify (Scheme.fppfTopology.over S) G)
      x' (DescentAction.sheafifiedLocalRepresentation s G x' eG) f e he hH hc').homEquiv m =
      (toSheafify (Scheme.fppfTopology.over S) G).app (op T)
        ((DescentAction.globalRepresentation s G x' eG f e he hG hc).homEquiv m) := by
  apply Presieve.isSeparatedFor_singleton.1 (hH T).isSeparatedFor
  rw [DescentAction.globalRepresentation_localPoint]
  rw [←NatTrans.naturality_apply,DescentAction.globalRepresentation_localPoint]
  rfl

variable {K : Type} [Field K] {C : Scheme} {c : C ⟶ Spec (.of K)}
  (M : Presentation K c) (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
  {D : RelativePic0Designation K c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

theorem pointed_to_sheaf {T : Over (Spec (.of K))} (m : T ⟶ Over.mk M.toBase) :
    M.sheafRepresentation.homEquiv m =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of K))) (Unrigidified.zeroPresheaf c)).app (op T)
        ((M.pointedRepresentation ε h).homEquiv m) := by
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  exact descended_unit (specMap K M.extension) (Unrigidified.zeroPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over _ _ _ _ m

theorem pointed_to_group {T : Over (Spec (.of K))} (m : T ⟶ Over.mk M.toBase) :
    M.groupSheafRepresentation.homEquiv m =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of K))) (Unrigidified.zeroCommGrpPresheaf c)).app (op T)
        ((M.pointedRepresentation ε h).homEquiv m) := by
  let F := Unrigidified.zeroCommGrpPresheaf c
  let j := Scheme.fppfTopology.over (Spec (.of K))
  let z := (M.pointedRepresentation ε h).homEquiv m
  change (sheafifyComposeIso j (forget CommGrpCat.{1}) F).hom.app (op T)
    (M.sheafRepresentation.homEquiv m) = _
  rw [pointed_to_sheaf M ε h]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (sheafComposeIso_hom_fac j (forget CommGrpCat.{1}) F) (op T)) z

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.pointed_to_sheaf
#print axioms ZInQBlueprint.AbelGalois.pointed_to_group
