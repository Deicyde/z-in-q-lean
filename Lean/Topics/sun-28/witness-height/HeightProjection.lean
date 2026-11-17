import CertificateHeights
import MomentProjection

/-! The rational inputs at which a height proof is actually needed by the fixed polynomial. -/
namespace Sun28.WitnessHeight
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.FixedPreparation Sun28.MinimalConductors Sun28.FiveMarkUnits Sun28.HeightExtension
open Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.HeightFibres.Sharp
open Sun28.HeightCubics Sun28.HeightCubics.Refinement
open Sun28.PreparedPoles Sun28.PairedClasses Sun28.RealProjection Sun28.RealCharts Sun28.CyclicOrbit
open scoped Sun28.RealCharts
open Height
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The complement of the seven established sufficient tests at a single slope. -/
structure Uncovered (A B : ℤ) : Prop where
  repeated : ∀ i, ¬SparseRepeated i A B
  units : glazerConstant24*(oddProduct A B:ℝ)^24 < vonKanelBound (best A B)
  square : ∀ i b c, ¬HeightRefinement.Sharp.Test i A B b c
  four : ¬HeightBalance.Covered A B
  three : ¬HeightBalance.PairCovered A B
  ordinate : ¬Ordinate.Covered A B
  conductor : ¬Pooled.ChartTest A B

theorem uncovered_of_failure (units : PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (elliptic : PublishedElliptic) {A B:ℤ} (cop : Int.gcd A B=1) (off : ∀ i, oldForm i A B≠0)
    (failed : ¬target A B) : Uncovered A B := by
  refine ⟨fun i s => failed (repeated_height (finite_of_all pell) classes characters cop off i s),?_,
    fun i b c s => failed (HeightRefinement.Sharp.height_of_square pell classes characters cop off i s),
    fun s => failed (HeightBalance.five_height_of_balance units cop off s),
    fun s => failed (HeightBalance.five_height_of_pair units cop off s),
    fun s => failed (Ordinate.five_height_of_ordinate (supported_coordinates elliptic) cop off s),
    fun s => failed (Pooled.five_height_of_chart elliptic cop off s)⟩
  apply lt_of_not_ge
  intro good
  apply failed
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using
    (attained_height units cop off).trans good

/-- Each accepted certificate with a nonintegral input calls the height lemma only
at the scalar input and at a slope of greatest ordinary height. Any maximizing index is permitted. -/
def CertificateResidual : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    (Uncovered (beta x).num (beta x).den → target (beta x).num (beta x).den) ∧
    ∃ j : Fin 3, (∀ i, logHeight₁ (slope (nineAffine A).doubles η i)≤
      logHeight₁ (slope (nineAffine A).doubles η j)) ∧
      (let t:=slope (nineAffine A).doubles η; let s:=sourcePair (t j);
        Uncovered s.1 s.2 → ¬conductorHeight t j → unionHeight t j)

theorem of_uniform (uniform : Pooled.Logarithmic.Remaining) : CertificateResidual := by
  have pointwise (A B : ℤ) (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (u : Uncovered A B) :=
    uniform A B cop off u.repeated u.units u.square u.four u.three u.ordinate u.conductor
  intro A x η _ accepted
  obtain ⟨j,largest⟩ := maximum_exists (slope (nineAffine A).doubles η)
  exact ⟨pointwise _ _ (beta_primitive x) (beta_off_forms x),j,largest,
    fun u _ => ordinary_to_union _ j
      (pointwise _ _ (source_primitive _) (source_off _ (accepted.scale_guard j).1) u)⟩

theorem integral_of_certificate_residual (units : PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (elliptic : PublishedElliptic) (height : CertificateResidual) (x : ℚ)
    (zero : ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) : ∃ z : ℤ, x=(z:ℚ) := by
  classical
  by_contra nonintegral
  obtain ⟨A,η,accepted⟩ := (Concrete.polynomial_iff_certificate _).1 zero
  obtain ⟨sc,j,largest,ord⟩ := height A x η nonintegral accepted
  have applyTests {a b : ℤ} (cop : Int.gcd a b=1) (off : ∀ i, oldForm i a b≠0)
      (remaining : Uncovered a b → target a b) : target a b := by
    by_contra bad
    exact bad (remaining (uncovered_of_failure units pell classes characters elliptic cop off bad))
  let t := slope (nineAffine A).doubles η
  have off := (accepted.scale_guard j).1
  have ordinaryBound : unionHeight t j := by
    by_cases cond : conductorHeight t j
    · exact union_of_conductor units t j off cond
    by_cases u : Uncovered (sourcePair (t j)).1 (sourcePair (t j)).2
    · exact ord u cond
    · apply ordinary_to_union
      by_contra failure
      exact u (uncovered_of_failure units pell classes characters elliptic
        (source_primitive _) (source_off _ off) failure)
  exact nonintegral (integral_of_union_height A x η accepted j largest ordinaryBound
    (applyTests (beta_primitive x) (beta_off_forms x) sc))

section
local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

/-- An integer has a rational zero using the two existence hypotheses alone. -/
theorem fibre_of_hybrid (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (primes : PrimeMass.HybridInputs)
    (points : GlobalSections.SectionResidual) (k : ℤ) :
    ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial (k:ℚ) w=0 := by
  have regular := GlobalSections.residual_iff_sections.mpr points
  have loc := PointLifts.residual_iff_regular.mpr regular
  have norm := PointFibres.norm_residual_iff_pencil.mpr (PointLifts.pencil_residual_iff_local_ratios.mpr loc)
  have rest := PrescribedPoints.core_iff_residual.mp (PointDescent.core_of_norm_residual norm)
  have sieve := PrimeMass.hybrid_surplus primes
    (ConeSieve.row_of_congruences (ConeCount.upper_sieve quadric))
  let component := RealComponents.openComponent_of_published realCurves
  let orbit := of_open_component diagonalGenerator component
  let model := parameterModel_on_subgroup DiagonalClosure orbit (generator_value diagonalGenerator component)
  have prep := TwistRank.selected_preparation orbit model
    (TwistRank.ray_selection (NormSieve.pattern_iff.mpr (WeightedSelection.prime_values_iff_surplus.mpr sieve)))
  obtain ⟨a,η,h⟩ := prep k
  exact (Concrete.polynomial_iff_certificate _).2 ⟨a,η,TwistExtension.certificate rest h⟩

theorem fibre_of_integer (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (moments : PrimeValues.FirstMomentInputs)
    (points : GlobalSections.SectionResidual) (k : ℤ) :
    ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial (k:ℚ) w=0 :=
  fibre_of_hybrid realCurves quadric (PrimeValues.hybrid_inputs_of_moments moments) points k

end

theorem certificate_projection (realCurves : RealComponents.PublishedProposition72)
    (units : PublishedCorollary72) (pell : PublishedAllPell) (classes : PublishedClassRegulator)
    (characters : QuadraticCharacterDiscriminants) (quadric : ConeCount.PublishedQuadricCount)
    (elliptic : PublishedElliptic) (height : CertificateResidual)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalSections.SectionResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  refine ⟨integral_of_certificate_residual units pell classes characters elliptic height x,?_⟩
  rintro ⟨k,rfl⟩
  exact fibre_of_integer realCurves quadric moments points k

end
end Sun28.WitnessHeight

#print axioms Sun28.WitnessHeight.uncovered_of_failure
#print axioms Sun28.WitnessHeight.of_uniform
#print axioms Sun28.WitnessHeight.integral_of_certificate_residual
#print axioms Sun28.WitnessHeight.fibre_of_integer
#print axioms Sun28.WitnessHeight.certificate_projection
#print axioms Sun28.WitnessHeight.fibre_of_hybrid
