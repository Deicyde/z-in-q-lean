import SixAbelField
import WeightedPointEndpoint

/-! Divisor classes, the Abel morphism, and generation for the original signed sextic. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open JacobianVarieties.Picard.Unpointed GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open BinaryCover GeometricMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

abbrev paperCurve (u : ℚ) := paperPullback Qbar u
abbrev CurvePoints (u : ℚ) := basePoint ⟶ paperCurve u

private theorem curve_proper (u : ℚ) : IsProper (paperCurve u).hom := by
  let := paper_proper ℚ u
  exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem curve_integral {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    GeometricallyIntegral (paperCurve u).hom := by
  let := geometricallyIntegral_paperModel hu
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem curve_dimension {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SmoothOfRelativeDimension 1 (paperCurve u).hom := by
  let c := (paperModel ℚ u).hom
  let : Smooth c := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 c := SixJacobian.relative_dimension_one c (paper_dimension ℚ u)
  exact inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c (scalarMap ℚ Qbar)))

theorem sourceIntegral {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    AlgebraicGeometry.IsIntegral (paperCurve u).left := by
  let := curve_integral hu
  exact GeometricallyIntegral.isIntegral_of_subsingleton (paperCurve u).hom

/-- The normalized place model of the literal scalar extension, with its specified germs. -/
def signedModel {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    PlaceModel (paperCurve u) := by
  let := sourceIntegral hu
  let := curve_proper u
  let := curve_integral hu
  let := curve_dimension hu
  exact placeModel (paperCurve u)

def basepoint {u : ℚ} (hu : u ∉ ZInQ.contactSet) : CurvePoints u := by
  let := curve_proper u
  let := curve_integral hu
  let := curve_dimension hu
  exact curvePoint (paperCurve u)

/-- The literal morphism and divisor-class equivalence for the scalar-extended rational Jacobian. -/
def realization {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let N := signedModel hu
    letI := N.curve
    AbelPresentation (paperCurve u) N.model N.iso N.hbase (geometricJacobian hu) (basepoint hu) := by
  let := sourceIntegral hu
  let := curve_proper u
  let := curve_integral hu
  let := curve_dimension hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  letI := N.curve
  let A := (exists_abelPresentation (paperCurve u) N.model N.iso N.hbase (basepoint hu)).some
  let e := IntegralPicard.paperJacobian_baseChangeIso Qbar hu (paperCurve u) (Iso.refl _)
  exact A.transport e.symm

def abel {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p : CurvePoints u) : JacobianPoints hu :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  letI := (signedModel hu).curve
  (realization hu).abel p

def weightedAbel {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p : FibrePoints u) : JacobianPoints hu :=
  abel hu (WeightedCurvePoints.weightedEquiv_pullback hu p)

theorem abel_basepoint {u : ℚ} (hu : u ∉ ZInQ.contactSet) : abel hu (basepoint hu) = 0 := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  exact (realization hu).abel_basepoint

theorem classes_of_difference {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p q : CurvePoints u) :
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let N := signedModel hu
    letI := N.curve
    abel hu p - abel hu q = (realization hu).divisorEquiv
      (Pic0.mk (difference (pointPlace (paperCurve u) N.model N.iso N.hbase p)
        (pointPlace (paperCurve u) N.model N.iso N.hbase q))) := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  exact (realization hu).difference_class p q

theorem generate {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    AddSubgroup.closure (Set.range (fun r : CurvePoints u × CurvePoints u =>
        abel hu r.1 - abel hu r.2)) = ⊤ := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  exact (realization hu).generate

theorem weighted_generate {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    AddSubgroup.closure (Set.range (fun r : FibrePoints u × FibrePoints u =>
      weightedAbel hu r.1-weightedAbel hu r.2)) = ⊤ := by
  apply top_unique
  rw [←generate hu]
  apply AddSubgroup.closure_mono
  rintro _ ⟨⟨p,q⟩,rfl⟩
  obtain ⟨p',rfl⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective p
  obtain ⟨q',rfl⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective q
  exact ⟨(p',q'),rfl⟩

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.realization
#print axioms ZInQBlueprint.SixAbelMap.abel
#print axioms ZInQBlueprint.SixAbelMap.weightedAbel
#print axioms ZInQBlueprint.SixAbelMap.abel_basepoint
#print axioms ZInQBlueprint.SixAbelMap.classes_of_difference
#print axioms ZInQBlueprint.SixAbelMap.generate
#print axioms ZInQBlueprint.SixAbelMap.weighted_generate
