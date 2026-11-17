import MinimalIdeal
import QuaternionGoodHeight
import HPEmbeddingHeight
import SixShimuraEndpoint
import DeterminantEndpoint

/-! The global stable-height formula for a rational genus-two Jacobian and
its application to the original bounded polynomial. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField Real
namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight ArchimedeanHeight ZInQ
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Habegger--Pazuki, Corollary 4.6, for a rational genus-two curve with a
specified affine sextic equation and the stable height in the effective bound.
The naive minimal discriminant supplies I and local minimizing equations.
Only attainment is used, so no converse from completed models to local models
is needed. Each complex embedding may choose its own reduced period. -/
def GlobalHeightFormula (hF : GroupScheme ℚ → ℝ) : Prop :=
  ∀ (C : Over (Spec (.of ℚ))) [IsProper C.hom] [GeometricallyIntegral C.hom]
    [SmoothOfRelativeDimension 1 C.hom], SmoothProperCurve.geometricGenus ℚ C.hom = 2 →
    ∀ (f : ℚ[X]) (_hd : f.natDegree = 6) (_nz : f.discr ≠ 0)
      (i : SpecOver (R:=ℚ) (Cover f) ⟶ C), IsOpenImmersion i.left →
    ∀ (K : Type) [Field K] [NumberField K], OddPointChart f K →
      (∀ v : FinitePlace K, GoodAt (jacobian C) v) →
      ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ RepresentedAtPlaces f I ∧
        ∃ Z : (K →ₐ[ℚ] ℂ) → ThetaPeriod.SiegelPeriod, (∀ σ, InStrengDomain (Z σ)) ∧
          (Module.finrank ℚ K:ℝ)*(hF (jacobian C)+log π) =
            log (I.absNorm:ℝ)/60 - (∑ σ, log (peterssonFactor (Z σ)))/10

/-- No local reduction formula, comparison of periods, torsion field, minimal
discriminant, or quaternionic descent datum is supplied as a fibrewise hypothesis. -/
theorem signed_height {hF : GroupScheme ℚ → ℝ} (hp : GlobalHeightFormula hF)
    (pqm : QuaternionPotentialReduction) (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    {u : ℚ} (hu : u ∉ contactSet) (marked : PrintedField hu) :
    ratHeight (SixContact.J u) < 30*hF (SixJacobian.jacobian hu)+150 := by
  let M := paperModel ℚ u
  let f := paper ℚ u false
  let : IsProper M.hom := paper_proper ℚ u
  let : GeometricallyIntegral M.hom := geometricallyIntegral_paperModel hu
  let : AlgebraicGeometry.IsIntegral M.left := paper_reglued_integral ℚ hu
  let : Smooth M.hom := smooth_paperModel hu
  let : SmoothOfRelativeDimension 1 M.hom := SixJacobian.relative_dimension_one _ (paper_dimension ℚ u)
  let i : SpecOver (R:=ℚ) (Cover f) ⟶ M := chartInclusion ℚ _ _ (paper_overlap ℚ u) false
  have hi : IsOpenImmersion i.left := chartInclusion_open ..
  obtain ⟨K,kf,kn,_,good,_,_,_,odd⟩ := signed_height_field_good hu marked pqm (st _ (SixJacobian.isAbelian hu))
  let := kf
  let := kn
  obtain ⟨I,hI,attained,Z,red,eq⟩ := hp M (SixJacobian.geometricGenus_two hu) f (WeightedCurvePoints.finite_degree ℚ hu)
    (signed_disc_ne hu) i hi K odd good
  exact height_of_ideal_floor hu I hI (denominator_dvd hu I hI attained)
    (floor_of_embeddings _ _ Z red eq.ge)

/-- Glazer's original bound, with a general height theorem and the explicit
remaining comparison on the printed Baba--Granath model. -/
theorem original_of_shimura_and_height (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (image : EffectivePolarizationImage) (degree : EffectivePolarizationDegree) (factor : CartierPrimeFactorization)
    (U : ShimuraClassMap) (model : PrintedComparison U)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  have field := printedField_of_shimura U model hu
  have lower := signed_height hp pqm st hu field
  have theta := signed_determinant_of_standard_facts hu image degree factor
  have marked := marked_signed_jacobian hu (embedding u hu) (coords u hu) theta field
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p hm
    exact (Finset.mem_union.mp hm).elim (fun h => Mult.prime_of_mem_S_mul h) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    (marked.elim rationalRM_of_marked) (good_outside ddmm hu)
  change hF (SixJacobian.jacobian hu) ≤ HeightBudget.vonKaenelBudget u at upper
  linarith only [lower,upper]

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.GlobalHeightFormula
#print axioms ZInQBlueprint.MinimalDiscriminant.signed_height
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_shimura_and_height
