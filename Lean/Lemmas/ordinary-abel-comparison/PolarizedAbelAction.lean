import AbelDifferenceSign
import SignedCoordinateLifts
import OrdinaryFibreBridge

/-! Scalarity of the polarized automorphisms of the signed Jacobian from
the pointed Torelli theorem and the change of Weierstrass coordinates. -/

open CategoryTheory AlgebraicGeometry Polynomial
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent

namespace ZInQBlueprint.AbelComparison
open BinaryCover AbelianModel NormalDescent CMRepair GeometricMarking
open QuaternionMarking ThetaClass SixAbelMap WeightedCurvePoints CanonicalTheta
open RosatiSigns ShimuraAtlas WeierstrassCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Milne, Jacobian Varieties, Theorem 12.1(a), using the pointed Picard
determinant for the canonical polarization. This identification of the
polarization is part of the input. The sign and translation are arbitrary. -/
def PointedDeterminantTorelli : Prop :=
  ∀ (f : Qbar[X]), f.natDegree = 6 → f.Separable →
    ∀ (C : Over (Spec (.of Qbar))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
      [GeometricallyIntegral C.hom],
    (∃ i : SpecOver (R := Qbar) (Cover f) ⟶ C, IsOpenImmersion i.left) →
    ∀ (b : base Qbar ⟶ C) (A : GroupScheme Qbar) (e : A ≅ groupScheme Qbar C.hom)
      (m : C ⟶ A.X) (P : Pointed b e m) (a : A ≅ A),
    Compatible a P.determinantLine P.determinantLine → AbelComparisonUpToSign m a

theorem signed_differences_of_polarized (torelli : PointedDeterminantTorelli) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (a : geometricJacobian hu ≅ geometricJacobian hu)
    (ha : Compatible a (signedThetaLine hu) (signedThetaLine hu)) :
    OnAbelDifferences (rigidMorphism hu) a := by
  let C := paperModel ℚ u
  let D := paperCurve u
  let : IsProper C.hom := paper_proper ℚ u
  let : GeometricallyIntegral C.hom := geometricallyIntegral_paperModel hu
  let : Smooth C.hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral C.left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 C.hom := SixJacobian.relative_dimension_one _ (paper_dimension ℚ u)
  let : IsProper D.hom := inferInstanceAs (IsProper (Limits.pullback.snd C.hom (scalarMap ℚ Qbar)))
  let : GeometricallyIntegral D.hom := inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd C.hom (scalarMap ℚ Qbar)))
  let : SmoothOfRelativeDimension 1 D.hom := inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd C.hom (scalarMap ℚ Qbar)))
  apply signed_differences hu a
  exact torelli (paper Qbar u false) (finite_degree Qbar hu) (paper_chart_regular Qbar hu false).2 D
    ⟨baseChangedFiniteChart Qbar u, inferInstance⟩ (basepoint hu) (geometricJacobian hu) _ _
    (signedPointed hu) a ha

/-- A comparison on divisor differences forces the Jacobian endomorphism to be a scalar. -/
theorem scalar_of_curve_differences {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (coordinates : CurveCoordinateLifts hu) (a : geometricJacobian hu ≅ geometricJacobian hu)
    (ha : OnAbelDifferences (rigidMorphism hu) a) : End.of a.hom = 1 ∨ End.of a.hom = -1 := by
  let preserves := OnAbelDifferences (rigidMorphism hu)
  have lifts : PolarizedTorelli (rigidDivisors hu) preserves := by
    intro b hb
    obtain ⟨c, h⟩ := hb
    obtain ⟨l, hl⟩ := coordinates c
    refine ⟨l, fun p q => ?_⟩
    rw [map_sub, rigid_on_points, rigid_on_points, rigid_on_points, rigid_on_points, hl, hl]
    exact h (weightedEquiv_pullback hu p) (weightedEquiv_pullback hu q)
  have h := polarized_signs (rigidDivisors hu).comparison
    (torelli_on_points (rigidDivisors hu) lifts) (groupMap a) ⟨a, ha, rfl⟩
  rcases h with h | h
  · left
    apply End.homEquiv.injective
    apply CommGrp.hom_ext
    exact Over.OverMorphism.ext h
  · right
    apply End.homEquiv.injective
    apply CommGrp.hom_ext
    apply Over.OverMorphism.ext
    change groupMap a = ((𝟙 _ : (geometricJacobian hu).X ⟶ _) ≫ GrpObj.inv).left
    simpa only [Category.id_comp] using h

/-- Every geometric polarized automorphism of the signed Jacobian is scalar. -/
theorem signed_polarized_scalar (torelli : PointedDeterminantTorelli)
    (coordinates : VoightCoordinateFormula) : SignedPolarizedSigns :=
  fun _ hu a ha => scalar_of_curve_differences hu (curveCoordinateLifts_of_voight coordinates hu)
    a (signed_differences_of_polarized torelli hu a ha)

end
end ZInQBlueprint.AbelComparison

#print axioms ZInQBlueprint.AbelComparison.signed_differences_of_polarized
#print axioms ZInQBlueprint.AbelComparison.scalar_of_curve_differences
#print axioms ZInQBlueprint.AbelComparison.signed_polarized_scalar
