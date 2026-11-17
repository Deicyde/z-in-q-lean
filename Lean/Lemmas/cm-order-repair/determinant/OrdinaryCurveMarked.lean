import CurveMarkedDescent
import SixPolarizedIgusa

/-! A curve-level marked-field statement on rational sextics, and the
specialization to the original polynomial without a theta-divisor input. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField Real
open JacobianVarieties.Picard.Unpointed
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CMRepair
open BinaryCover AbelianModel NormalDescent QuaternionMarking GeometricMarking SixAbelMap
open WeightedCurvePoints ThetaClass JacobianHeight TorsionHeight MinimalDiscriminant
open QuaternionLift ShimuraAtlas CanonicalTheta JacobianConductor LocalJacobians ArchimedeanHeight ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

/-- The rational Jacobian and its canonical base-change identification are
fixed by the rational curve. This prevents arbitrary rational forms or
unrelated Picard identifications from entering the correction. -/
def OrdinaryRationalCurveMarking : Prop :=
  ∀ (f : ℚ[X]), f.natDegree = 6 → f.Separable →
    ∀ (C : Over (Spec (.of ℚ))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
      [GeometricallyIntegral C.hom], (∃ i : SpecOver (R := ℚ) (Cover f) ⟶ C, IsOpenImmersion i.left) →
    ∀ (D : Over (Spec (.of Qbar))) [IsProper D.hom] [SmoothOfRelativeDimension 1 D.hom]
      [GeometricallyIntegral D.hom] (e : (Over.pullback (specExtension ℚ Qbar)).obj C ≅ D)
      (b : base Qbar ⟶ D) (m : D ⟶ ((baseChange (algebraMap ℚ Qbar)).obj (groupScheme ℚ C.hom)).X),
      Pointed b (IntegralPicard.unpointed_baseChangeIso C D e) m → ∀ j w : ℚ, w ≠ 0 →
      IgusaCoordinates.ofSextic f = (bgCoordinates j).scale w →
      j*(64*j-81)*(27*j+16) ≠ 0 → OutsideCM j →
        ∃ z : Qbar, z^2 = ((-(27*j+16)/j : ℚ) : Qbar) ∧ RationalAbelMarking (groupScheme ℚ C.hom) m z

theorem signed_actions_of_ordinary_curve_marking (field : OrdinaryRationalCurveMarking)
    {u : ℚ} (hu : u ∉ contactSet) (coordinates : CurveCoordinateLifts hu) :
    QuaternionOrderOn (SixJacobian.jacobian hu) ∧ RationalRM (SixJacobian.jacobian hu) := by
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
  let i : SpecOver (R:=ℚ) (Cover (paper ℚ u false)) ⟶ C := chartInclusion ℚ _ _ (paper_overlap ℚ u) false
  obtain ⟨w,hw,eq⟩ := signed_coordinates hu
  obtain ⟨z,hz,marked⟩ := field _ (OddModel.paper_degree hu) (paper_chart_regular ℚ hu false).2 C
    ⟨i,chartInclusion_open ..⟩ D (Iso.refl _) (basepoint hu) (rigidMorphism hu) (signedPointed hu)
    _ w hw eq (CoarseConic.mestre_factors hu) (fun _ ha => avoids_cm_table hu ha)
  exact actions_of_rational_abel_marking hu coordinates hz marked

/-- The lower height estimate uses a faithful geometric quaternion action.
Neither its rationality nor a choice of marked theta divisor is required. -/
theorem signed_height_of_quaternion_order {hF : GroupScheme ℚ → ℝ} (hp : GlobalHeightFormula hF)
    (pqm : QuaternionPotentialReduction) (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    {u : ℚ} (hu : u ∉ contactSet) (order : QuaternionOrderOn (SixJacobian.jacobian hu)) :
    ratHeight (SixContact.J u) < 30*hF (SixJacobian.jacobian hu)+150 := by
  let C := paperModel ℚ u
  let f := paper ℚ u false
  let : IsProper C.hom := paper_proper ℚ u
  let : GeometricallyIntegral C.hom := geometricallyIntegral_paperModel hu
  let : AlgebraicGeometry.IsIntegral C.left := paper_reglued_integral ℚ hu
  let : Smooth C.hom := smooth_paperModel hu
  let : SmoothOfRelativeDimension 1 C.hom := SixJacobian.relative_dimension_one _ (paper_dimension ℚ u)
  let i : SpecOver (R:=ℚ) (Cover f) ⟶ C := chartInclusion ℚ _ _ (paper_overlap ℚ u) false
  have hi : IsOpenImmersion i.left := chartInclusion_open ..
  obtain ⟨K,kf,kn,level,_,_,_,odd⟩ := signed_height_field hu
  let := kf
  let := kn
  have pot := pqm _ (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu) order K
  have good := good_everywhere_of_full_twelve _ (st _ (SixJacobian.isAbelian hu)) pot level
  obtain ⟨I,hI,attained,Z,red,eq⟩ := hp C (SixJacobian.geometricGenus_two hu) f (finite_degree ℚ hu)
    (signed_disc_ne hu) i hi K odd good
  exact height_of_ideal_floor hu I hI (denominator_dvd hu I hI attained)
    (floor_of_embeddings _ _ Z red eq.ge)

/-- Polynomial endpoint using the geometric quaternion action for the
height lower bound and the descended real generator for its upper bound. -/
theorem original_of_ordinary_rational_curve_marking (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (field : OrdinaryRationalCurveMarking) (coordinates : ∀ {u : ℚ} (hu : u ∉ contactSet), CurveCoordinateLifts hu)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  obtain ⟨order,real⟩ := signed_actions_of_ordinary_curve_marking field hu (coordinates hu)
  have lower := signed_height_of_quaternion_order hp pqm st hu order
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p h
    exact (Finset.mem_union.mp h).elim (fun v => Mult.prime_of_mem_S_mul v) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    real (good_outside ddmm hu)
  change hF (SixJacobian.jacobian hu) ≤ HeightBudget.vonKaenelBudget u at upper
  linarith only [lower,upper]

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.signed_actions_of_ordinary_curve_marking
#print axioms ZInQBlueprint.CMRepair.signed_height_of_quaternion_order
#print axioms ZInQBlueprint.CMRepair.original_of_ordinary_rational_curve_marking
