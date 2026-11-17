import SignedPoincare
import AbelImmersionCriterion

/-! The rigidified morphism separates points. To prove that it is a closed
immersion it suffices to prove that it is formally unramified. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve GoodReductionJacobian
namespace ZInQBlueprint.SixAbelMap
open BinaryCover GeometricMarking NormalDescent
open scoped CategoryTheory.MonObj NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

theorem rigid_point_injective :
    Function.Injective (fun p : CurvePoints u => p ≫ rigidMorphism hu) := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let := paper_proper ℚ u
  let : IsProper (paperCurve u).hom := inferInstanceAs
    (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : Algebra.EssFiniteType Qbar (paperCurve u).left.functionField :=
    AlgebraicCurve.essFiniteType_functionField (paperCurve u).hom
  exact (rigidPresentation hu).injective_of_positive_genus (by rw [paper_functionField_genus hu]; decide)

theorem rigid_closed_of_unramified (h : FormallyUnramified (rigidMorphism hu).left) :
    IsClosedImmersion (rigidMorphism hu).left := by
  let C := paperCurve u
  let J := (geometricJacobian hu).X
  let a := rigidMorphism hu
  have := paper_proper ℚ u
  let : IsProper C.hom := inferInstanceAs
    (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : IsProper (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).proper
  let : IsProper J.hom := inferInstanceAs
    (IsProper (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let : IsProper (a.left ≫ J.hom) := by rw [Over.w]; infer_instance
  let : IsProper a.left := IsProper.of_comp a.left J.hom
  apply closed_of_point_separation C.hom J.hom a.left (Over.w a)
  intro p q hp hq hpq
  let P : CurvePoints u := Over.homMk p hp
  let Q : CurvePoints u := Over.homMk q hq
  have same : P ≫ a = Q ≫ a := Over.OverMorphism.ext hpq
  exact congrArg (fun t : CurvePoints u => t.left) (rigid_point_injective hu same)

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.rigid_point_injective
#print axioms ZInQBlueprint.SixAbelMap.rigid_closed_of_unramified
