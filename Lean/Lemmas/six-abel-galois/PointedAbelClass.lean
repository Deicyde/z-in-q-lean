import PointedClassDictionary

/-! A Poincaré-normalized Abel map really is the represented unpointed point class. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian NeronModelInfra Opposite
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.AbelGalois
open SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] (C : Over (Spec (.of K)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]

theorem pointed_abel_class (b : base K ⟶ C) (m : C ⟶ (groupScheme K C.hom).X)
    (h : RepresentsPointDivisors C b m) (p : base K ⟶ C) :
    Additive.ofMul (p ≫ m) = pointDifference C.hom p b := by
  obtain ⟨D,H,aj,hp,hm⟩ := h
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom := ⟨b.left,b.w⟩
  let M := presentation K C.hom
  have comp : ((M.pointedRepresentation ε H).homEquiv (p ≫ m)) =
      (pointedUnrigidifiedRepresentation ε H).homEquiv (p ≫ Over.homMk aj.1 aj.2) := by
    rw [←pointedComparison_classes,Category.assoc,hm]
  have hear : ((M.pointedRepresentation ε H).homEquiv (p ≫ m)) = rawDifference C.hom p b := by
    rw [comp]
    obtain ⟨i⟩ := hp.2 K (𝟙 (Spec (.of K))) ⟨p.left,p.w⟩
    apply Subtype.ext
    apply Quot.sound
    apply Unrigidified.baseTwist_of_iso
    change (H.poincare.pullbackAlong ⟨p.left ≫ aj.1,(Category.assoc _ _ _).trans ((congrArg (p.left ≫ ·) aj.2).trans p.w)⟩).L ≅
      (RelEffCartierDiv.ofPoint C.hom p.left p.w).lineBundle ⊗ (RelEffCartierDiv.ofPoint C.hom b.left b.w).idealModule
    simpa only [Category.id_comp] using i
  apply (groupSheafRepresentation K C.hom).homEquiv.injective
  change M.groupSheafRepresentation.homEquiv (p ≫ m) =
    M.groupSheafRepresentation.homEquiv (M.groupSheafRepresentation.homEquiv.symm _)
  rw [Equiv.apply_symm_apply,pointed_to_group M ε H,hear]

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.pointed_abel_class
