import RelativePointDifferences
import IntegralSheaf

/-! The represented Jacobian classifies the literal point differences. Functoriality is in
the test scheme, so it includes an automorphism of the constant field of a geometric point. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian
open NeronModelInfra Opposite JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
attribute [local instance] filteredCommGrpHasColimitsOfShape
namespace ZInQBlueprint.AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] {C : Scheme} (c : C ⟶ Spec (.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
variable {T T' : Over (Spec (.of K))}

def rawDifference (p q : T ⟶ Over.mk c) :
    (Unrigidified.zeroCommGrpPresheaf c).obj (op T) :=
  ⟨Quot.mk _ (differenceBundle c ⟨p.left,p.w⟩ ⟨q.left,q.w⟩),
    difference_fibrewise c _ _⟩

theorem raw_pull (f : T' ⟶ T) (p q : T ⟶ Over.mk c) :
    (Unrigidified.zeroCommGrpPresheaf c).map f.op (rawDifference c p q) =
      rawDifference c (f ≫ p) (f ≫ q) := by
  apply Subtype.ext
  exact difference_class_pull c ⟨f.left,f.w⟩ ⟨p.left,p.w⟩ ⟨q.left,q.w⟩

/-- Tensor product cancels the intermediate point on any test scheme. -/
theorem raw_chain (p q r : T ⟶ Over.mk c) :
    rawDifference c p q * rawDifference c q r = rawDifference c p r := by
  let pos (x : T ⟶ Over.mk c) := (RelEffCartierDiv.ofPoint c x.left x.w).lineBundle
  let neg (x : T ⟶ Over.mk c) := (RelEffCartierDiv.ofPoint c x.left x.w).idealModule
  have hi := RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c q.left q.w)
  obtain ⟨el⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hi
  let unit : neg q ⊗ pos q ≅ 𝟙_ _ := β_ _ _ ≪≫ el
  apply Subtype.ext
  apply Quot.sound
  apply Unrigidified.baseTwist_of_iso
  exact (α_ (pos p) (neg q) (pos q ⊗ neg r)) ≪≫
    (Iso.refl _ ⊗ᵢ ((α_ (neg q) (pos q) (neg r)).symm ≪≫ (unit ⊗ᵢ Iso.refl _) ≪≫ λ_ _))

private abbrev eta := toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
  (Unrigidified.zeroCommGrpPresheaf c)

def pointDifference (p q : T ⟶ Over.mk c) : Additive (T ⟶ (groupScheme K c).X) :=
  Additive.ofMul ((groupSheafRepresentation K c).homEquiv.symm
    ((eta c).app (op T) (rawDifference c p q)))

theorem point_pull (f : T' ⟶ T) (p q : T ⟶ Over.mk c) :
    f ≫ (pointDifference c p q).toMul = (pointDifference c (f ≫ p) (f ≫ q)).toMul := by
  apply (groupSheafRepresentation K c).homEquiv.injective
  rw [Functor.RepresentableBy.homEquiv_comp]
  change (ordinaryRelativePicardZeroGroupSheaf c).obj.map f.op
    ((groupSheafRepresentation K c).homEquiv ((groupSheafRepresentation K c).homEquiv.symm _)) =
    (groupSheafRepresentation K c).homEquiv ((groupSheafRepresentation K c).homEquiv.symm _)
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact ((eta c).naturality_apply f.op (rawDifference c p q)).symm.trans
    (congrArg ((eta c).app (op T')) (raw_pull c f p q))

theorem point_chain (p q r : T ⟶ Over.mk c) :
    pointDifference c p q + pointDifference c q r = pointDifference c p r := by
  change (pointDifference c p q).toMul * (pointDifference c q r).toMul =
    (pointDifference c p r).toMul
  apply (groupSheafRepresentation K c).homEquiv.injective
  rw [groupSheafRepresentation_over_mul]
  change (groupSheafRepresentation K c).homEquiv ((groupSheafRepresentation K c).homEquiv.symm _) *
    (groupSheafRepresentation K c).homEquiv ((groupSheafRepresentation K c).homEquiv.symm _) =
    (groupSheafRepresentation K c).homEquiv ((groupSheafRepresentation K c).homEquiv.symm _)
  simp only [Equiv.apply_symm_apply]
  exact (map_mul ((eta c).app (op T)).hom (rawDifference c p q) (rawDifference c q r)).symm.trans (congrArg ((eta c).app (op T)).hom (raw_chain c p q r))

theorem change_basepoint (p b b' : T ⟶ Over.mk c) :
    pointDifference c p b' = pointDifference c p b - pointDifference c b' b := by
  rw [eq_sub_iff_add_eq,point_chain]

end
end ZInQBlueprint.AbelGalois
#print axioms ZInQBlueprint.AbelGalois.raw_pull
#print axioms ZInQBlueprint.AbelGalois.raw_chain
#print axioms ZInQBlueprint.AbelGalois.point_pull
#print axioms ZInQBlueprint.AbelGalois.point_chain
#print axioms ZInQBlueprint.AbelGalois.change_basepoint
