import GeometricPeriods
import ChartOpen

/-! The chart supplying the branch roots for the chosen squarefree twist. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
open SexticThetaHeight GlobalTwist IntegralSextic ResidualFactors
noncomputable section

/-- The affine polynomial used for the period computation is literally the
integral chart of the glued curve, at its prescribed twist. -/
theorem fixed_affine_eq_sextic {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    fixed ℚ u false = sextic u (delta u : ℚ) := by
  apply Polynomial.funext
  intro x
  rw [affine_equation hu]
  simp [fixed, integralEquation, form, m, n, alpha, beta, gamma, poleForm]

theorem paper_affine_eq_sextic {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    paper ℚ u false = C (CurveChart.yScale u)^2 * sextic u (delta u : ℚ) := by
  rw [paper_eq, fixed_affine_eq_sextic hu]
  simp

/-- At every complex point, the named paper chart and the chosen analytic
sextic have exactly the same roots. -/
theorem paper_root_iff {u : ℚ} (hu : u ∉ ZInQ.contactSet) (r : ℂ) :
    aeval r (paper ℚ u false) = 0 ↔ aeval r (sextic u (delta u : ℚ)) = 0 := by
  have h : (CurveChart.yScale u : ℂ) ≠ 0 := by exact_mod_cast CurveChart.yScale_ne hu
  rw [paper_affine_eq_sextic hu]
  simp [h]

end
end ZInQBlueprint.BinaryCover

namespace ZInQBlueprint.ThetaPeriod
open GlobalTwist SexticThetaHeight
noncomputable section

/-- Period hypotheses only at the twist used in the local reduction theorem. -/
def HasFixedPeriods : Prop := ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet),
  Nonempty (LabelledPeriod u (delta u : ℚ) hu (by exact_mod_cast (delta_pos u).ne'))

theorem labelledPeriods_of_fixedPeriods (h : HasFixedPeriods) : HasLabelledPeriods := by
  intro u hu
  exact ⟨_,_,h u hu⟩

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.BinaryCover.fixed_affine_eq_sextic
#print axioms ZInQBlueprint.BinaryCover.paper_affine_eq_sextic
#print axioms ZInQBlueprint.BinaryCover.paper_root_iff
#print axioms ZInQBlueprint.ThetaPeriod.labelledPeriods_of_fixedPeriods

namespace ZInQBlueprint
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- The period hypothesis uses the same squarefree twist as the local reduction proof. -/
theorem frozen_of_fixed_periods_and_local_traces
    (hp : ThetaPeriod.HasFixedPeriods)
    (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (fields : TraceFields (S.recursion L eps) S.extended)
    (torsion : ∀ n, n%8=5 → Squarefree n → ∀ Y : pointsOver (genusCompositum S.extended n),
      ∀ m : ℕ, 0 < m → m • Y.val = 0 →
        onePlusI (onePlusI (onePlusI Y.val)) = 0)
    (localTraces : ∀ n, n%8=5 → Squarefree n → ∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n ∧
      GaloisMinus n (tyzIsogeny ((2:ℕ) • representative (S.recursion L eps) n))) :
    ZInQ.FrozenTarget := by
  exact frozen_of_labelled_periods_and_local_traces (.inr (ThetaPeriod.labelledPeriods_of_fixedPeriods hp))
    S L eps h1 hc fields torsion localTraces

end
end ZInQBlueprint
#print axioms ZInQBlueprint.frozen_of_fixed_periods_and_local_traces
