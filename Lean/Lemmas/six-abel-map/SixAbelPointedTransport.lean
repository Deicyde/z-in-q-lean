import OrdinaryGoodReduction
import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedComparisonHom

/-! The chosen pointed and unpointed Picard schemes have the same tensor-product
law on their actual scheme-valued points. -/
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] (C : Over (Spec (.of K)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
abbrev base (K : Type) [Field K] := Over.mk (𝟙 (Spec (.of K)))

/-- Postcomposition with a group-scheme isomorphism acts additively on geometric points. -/
def pointsIso {V W : AbelianModel.GroupScheme K} (e : V ≅ W) :
    Additive (base K ⟶ V.X) ≃+ Additive (base K ⟶ W.X) where
  toFun a := Additive.ofMul (a.toMul ≫ e.hom.hom.hom.hom)
  invFun a := Additive.ofMul (a.toMul ≫ e.inv.hom.hom.hom)
  left_inv a := by
    have q : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 V.X :=
      congrArg (fun m : V ⟶ V => m.hom.hom.hom) e.hom_inv_id
    exact (Category.assoc _ _ _).trans ((congrArg (a.toMul ≫ ·) q).trans (Category.comp_id _))
  right_inv a := by
    have q : e.inv.hom.hom.hom ≫ e.hom.hom.hom.hom = 𝟙 W.X :=
      congrArg (fun m : W ⟶ W => m.hom.hom.hom) e.inv_hom_id
    exact (Category.assoc _ _ _).trans ((congrArg (a.toMul ≫ ·) q).trans (Category.comp_id _))
  map_add' a b := MonObj.mul_comp a.toMul b.toMul _

variable (ε : SchemeHomOver (𝟙 (Spec (.of K))) C.hom) {D : RelativePic0Designation K C.hom}
  (h : RepresentsRelSubPic C.hom ε (algEquivZeroCut C.hom ε) D)

abbrev PGroup := h.grpObj (P := algEquivZeroGroupCut C.hom ε)

/-- The unpointed comparison on points uses the specific tensor-product group laws on both sides. -/
def pointedPoints :
    letI := PGroup C ε h
    Additive (base K ⟶ (groupScheme K C.hom).X) ≃+ Additive (base K ⟶ Over.mk D.toBase) := by
  letI := PGroup C ε h
  let e : (groupScheme K C.hom).X ≅ Over.mk D.toBase := (presentation K C.hom).pointedComparisonOver ε h
  refine { toFun := fun a => Additive.ofMul (a.toMul ≫ e.hom)
           invFun := fun a => Additive.ofMul (a.toMul ≫ e.inv)
           left_inv := fun a => show (a.toMul ≫ e.hom) ≫ e.inv = a.toMul by simp
           right_inv := fun a => show (a.toMul ≫ e.inv) ≫ e.hom = a.toMul by simp
           map_add' := ?_ }
  intro a b
  apply (overHomEquivSchemeHomOver (base K) D.toBase).injective
  have hm := pointedComparison_mul C.hom ε h (𝟙 (Spec (.of K)))
    (overHomEquivSchemeHomOver (base K) _ a.toMul) (overHomEquivSchemeHomOver (base K) _ b.toMul)
  have hi := (groupLaw K C.hom).overHomEquivSchemeHomOver_mul (base K) a.toMul b.toMul
  exact (congrArg (pointedComparisonPoint C.hom ε h (𝟙 (Spec (.of K)))) hi).trans hm

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.pointsIso
#print axioms ZInQBlueprint.SixAbelMap.pointedPoints
