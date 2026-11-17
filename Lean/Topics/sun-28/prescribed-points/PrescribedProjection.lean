import SignedSections
import SurfaceProjection

namespace Sun28.PrescribedPoints
open PairedClasses PreparedPoles TwistExtension TwistRank
noncomputable section

/-- The fixed-pair obligation remaining after all known sections and both
possible rational zero ordinates have been extracted. -/
def LiveResidual : Prop := ∀ β θ : ℕ, AdmissiblePair β θ → InputClass β → FixedSquares θ →
  NormConic β θ → θ≠1 → ¬Family β θ → ¬SquareSection β θ → ¬FactorPair β θ →
  ¬OneQuartic (β:ℚ) (θ:ℚ) → NonzeroPair (β:ℚ) (θ:ℚ)

theorem residual_iff_live : TwistExtension.Residual ↔ LiveResidual := by
  constructor
  · intro old b t a input f n ne quart sec fac out
    exact ((surface_iff_one_or_nonzero (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne')).mp
      (affine_iff_surface.mp (old b t a input f n ne quart sec fac))).resolve_left out
  · intro live b t a input f n ne quart sec fac
    apply affine_iff_surface.mpr
    apply (surface_iff_one_or_nonzero (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne')).mpr
    by_cases ok : OneQuartic (b:ℚ) (t:ℚ)
    · exact Or.inl ok
    · exact Or.inr (live b t a input f n ne quart sec fac ok)

theorem prepared_pole (live : LiveResidual) {B : ℚ} (ready : ClassPrepared B) :
    Ordinary.polePredicate ScalarHeight.smallMultipliers B := TwistExtension.pole (residual_iff_live.mpr live) ready
end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.residual_iff_live
#print axioms Sun28.PrescribedPoints.prepared_pole
