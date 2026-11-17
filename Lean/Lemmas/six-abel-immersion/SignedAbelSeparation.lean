import SignedSixAbel
import JacobianDimension
import Nyll.JacobianVarieties.Picard.AbelJacobi.PositiveGenusPointSeparation

/-! Point separation for the Abel morphism on the original scalar-extended sextic. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open JacobianVarieties.Picard.Unpointed GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
noncomputable section
open BinaryCover GeometricMarking NormalDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Milne's point-separation argument for a represented Abel morphism. -/
theorem AbelPresentation.injective_of_positive_genus
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F] {C : Over (Spec (.of K))} {M : CurveModel K F}
    {i : M.C ≅ C.left} {hbase : i.hom ≫ C.hom = M.toBase}
    {V : AbelianModel.GroupScheme K} {b : base K ⟶ C}
    (A : AbelPresentation C M i hbase V b) (hg : 0 < genusFF K F) :
    Function.Injective A.abel := by
  intro p q hpq
  let e := pointPlace C M i hbase
  have hclass : Pic0.mk (difference (e p) (e q)) = 0 := by
    apply A.divisorEquiv.injective
    rw [map_zero, ← A.difference_class p q, hpq, sub_self]
  exact e.injective (eq_of_single_sub_single_principal_of_genus_pos hg _ _
    ((Pic0.mk_eq_zero_iff _).mp hclass))

/-- The genus of the very function field on which the Abel divisor correspondence is defined. -/
theorem paper_functionField_genus {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    let := sourceIntegral hu
    let := (baseToFunctionField (paperCurve u).hom).toAlgebra
    genusFF Qbar (paperCurve u).left.functionField = 2 := by
  let := geometricallyIntegral_paperModel hu
  exact SixJacobian.geometricGenus_two hu

/-- Geometric points of every smooth signed fibre have distinct Abel images. -/
theorem abel_injective {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    Function.Injective (abel hu) := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let : Algebra.EssFiniteType Qbar (paperCurve u).left.functionField := by
    have := paper_proper ℚ u
    let : IsProper (paperCurve u).hom :=
      inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd
        (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
    exact AlgebraicCurve.essFiniteType_functionField (paperCurve u).hom
  exact (realization hu).injective_of_positive_genus (by rw [paper_functionField_genus hu]; decide)

/-- The same separation on the normalized weighted coordinates, including the points at infinity. -/
theorem weightedAbel_injective {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    Function.Injective (weightedAbel hu) :=
  (abel_injective hu).comp (WeightedCurvePoints.weightedEquiv_pullback hu).injective

end
end ZInQBlueprint.SixAbelMap

#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.injective_of_positive_genus
#print axioms ZInQBlueprint.SixAbelMap.paper_functionField_genus
#print axioms ZInQBlueprint.SixAbelMap.abel_injective
#print axioms ZInQBlueprint.SixAbelMap.weightedAbel_injective
