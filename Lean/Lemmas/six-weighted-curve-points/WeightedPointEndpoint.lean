import PaperWeightedPoints
import CanonicalJacobianPoints
import ProperCompletion

/-! Geometric points of both the reglued paper curve and the literal scalar extension. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover GeometricMarking NormalDescent
noncomputable section

def weightedEquiv_reglued {u : ℚ} (hu : u∉ZInQ.contactSet) :
    FibrePoints u ≃ (basePoint ⟶ paperModel Qbar u) := weightedSections Qbar hu

def baseChangeIso {u : ℚ} (hu : u∉ZInQ.contactSet) :
    paperModel Qbar u ≅ paperPullback Qbar u := (unique_reglued_baseChange Qbar hu).exists.choose

theorem baseChangeIso_finiteChart {u : ℚ} (hu : u∉ZInQ.contactSet) :
    chartInclusion Qbar _ _ (paper_overlap Qbar u) false ≫ (baseChangeIso hu).hom =
      baseChangedFiniteChart Qbar u := (unique_reglued_baseChange Qbar hu).exists.choose_spec

def weightedEquiv_pullback {u : ℚ} (hu : u∉ZInQ.contactSet) :
    FibrePoints u ≃ (basePoint ⟶ paperPullback Qbar u) :=
  (weightedEquiv_reglued hu).trans ((Iso.refl basePoint).homCongr (baseChangeIso hu))

theorem weightedEquiv_pullback_apply {u : ℚ} (hu : u∉ZInQ.contactSet) (p : FibrePoints u) :
    weightedEquiv_pullback hu p = weightedEquiv_reglued hu p ≫ (baseChangeIso hu).hom := by
  change (𝟙 basePoint) ≫ _ ≫ _ = _
  rw [Category.id_comp]
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedEquiv_reglued
#print axioms ZInQBlueprint.WeightedCurvePoints.baseChangeIso_finiteChart
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedEquiv_pullback
#print axioms ZInQBlueprint.WeightedCurvePoints.weightedEquiv_pullback_apply
