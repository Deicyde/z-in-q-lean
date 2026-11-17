import SixAbelGeneration
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoFunctionFieldGermEq

/-! The literal function field of a proper smooth integral curve and its normalized place model. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.SixAbelMap
noncomputable section
variable {K : Type} [Field K] [IsAlgClosed K] (C : Over (Spec (.of K)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]

def curvePoint : base K ⟶ C := Classical.choice (by
  let : AlgebraicGeometry.IsIntegral C.left := GeometricallyIntegral.isIntegral_of_subsingleton C.hom
  let : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  obtain ⟨x,_,hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α:=C.left)) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint C.hom x hx) (pointOfClosedPoint_comp C.hom x hx)⟩)

variable [AlgebraicGeometry.IsIntegral C.left]
local instance : Algebra K C.left.functionField := (baseToFunctionField C.hom).toAlgebra

/-- The comparison with the literal function field records how regular functions map
to generic germs. This fixes the function-field identification used for the Abel map. -/
structure PlaceModel where
  curve : IsCurveOver K C.left.functionField
  model : CurveModel K C.left.functionField
  iso : model.C ≅ C.left
  hbase : iso.hom ≫ C.hom = model.toBase
  germs : ∀ (U : C.left.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme (iso.hom ⁻¹ᵁ U))] (t : Γ(C.left,U)),
      model.ffEquiv.symm (model.C.germToFunctionField (iso.hom ⁻¹ᵁ U) ((iso.hom.app U).hom t)) =
        C.left.germToFunctionField U t

def placeModel : PlaceModel C := Classical.choice (by
  obtain ⟨h,_,M,e,w,hg⟩ := SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K C.left C.hom
  exact ⟨⟨h,M,e,w,hg⟩⟩)

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.curvePoint
#print axioms ZInQBlueprint.SixAbelMap.placeModel
