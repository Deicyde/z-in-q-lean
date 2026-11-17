import EffectivePolarization
import PolarizationKernel
import GeometricPrimeForm
import IgusaPeriodEndpoint

/-! The classical two-point section calculation, Poincaré evaluations and
the Galois action on Abel differences imply the three polarization properties
used in the original bounded polynomial theorem. -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel CanonicalTheta SixAbelMap
open DeterminantSections DeterminantAutoduality JacobianHeight JacobianConductor LocalJacobians ZInQ NumberField
noncomputable section

def ReducedThetaSection {u : ℚ} (hu : u ∉ contactSet) : Prop :=
  ∃ s : 𝟙_ (geometricJacobian hu).X.left.Modules ⟶ signedThetaLine hu,
    s ≠ 0 ∧ IsReduced (Scheme.Modules.zeroSchemeIdeal s).subscheme

/-- One reduced divisor in the complete linear system suffices. -/
theorem signed_reduced_of_section {u : ℚ} (hu : u ∉ contactSet)
    (one : ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1)
    (reduced : ReducedThetaSection hu) :
    IsReduced (Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).subscheme := by
  obtain ⟨s,hs,red⟩ := reduced
  rw [ThetaLinearSystem.zeroScheme_eq _ _ (signedThetaLine_invertible hu) one
    _ s (signedThetaSection_ne_zero hu) hs]
  exact red

theorem determinant_of_reduced_section {u : ℚ} (hu : u ∉ contactSet)
    (sections : PrimeFormGeometry hu) (picard : PoincareGenerates hu)
    (reduced : ReducedThetaSection hu) :
    DeterminantPolarization hu := by
  have one := signed_rank_of_prime_form hu sections
  let := signed_reduced_of_section hu one reduced
  exact ⟨one, (signed_principal_iff hu).mpr picard,
    rational_of_abel_support hu (signed_deck_abel_support hu)⟩

/-- All multiplicities are allowed. The same Cartier factorization theorem
applies simultaneously to every off-contact fibre. -/
theorem determinant_of_curve_data {u : ℚ} (hu : u ∉ contactSet)
    (factor : CartierPrimeFactorization) (sections : PrimeFormGeometry hu)
    (picard : PoincareGenerates hu) : DeterminantPolarization hu :=
  ⟨signed_rank_of_prime_form hu sections,(signed_principal_iff hu).mpr picard,
    rational_of_prime_factorization hu factor (signed_deck_abel_support hu)⟩

theorem original_of_determinant_curve_data (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), OpenCurveLifts hu)
    (sections : ∀ (u : ℚ) (hu : u ∉ contactSet), PrimeFormGeometry hu)
    (picard : ∀ (u : ℚ) (hu : u ∉ contactSet), PoincareGenerates hu)
    (factor : CartierPrimeFactorization)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (IgusaPeriod K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_igusa_period hF effective ddmm embedding coords (fun u hu =>
    determinant_of_curve_data hu factor (sections u hu) (picard u hu))
    bg periods genus rank

/-- The original bound using the general degree and image formulas for a
line bundle with finite kernel and the one-component Cartier factorization. -/
theorem original_of_effective_polarization (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), OpenCurveLifts hu)
    (image : EffectivePolarizationImage) (degree : EffectivePolarizationDegree)
    (factor : CartierPrimeFactorization)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (IgusaPeriod K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_igusa_period hF effective ddmm embedding coords
    (fun _ hu => signed_determinant_of_standard_facts hu image degree factor) bg periods genus rank

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.signed_reduced_of_section
#print axioms ZInQBlueprint.ThetaClass.determinant_of_reduced_section
#print axioms ZInQBlueprint.ThetaClass.determinant_of_curve_data
#print axioms ZInQBlueprint.ThetaClass.original_of_determinant_curve_data
#print axioms ZInQBlueprint.ThetaClass.original_of_effective_polarization
