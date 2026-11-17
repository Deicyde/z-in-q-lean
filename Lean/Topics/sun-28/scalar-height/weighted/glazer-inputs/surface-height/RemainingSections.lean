import SingleSection

namespace ZInQBlueprint.FiveMetric
open Sun28.PairedClasses Sun28.PrescribedPoints Sun28.PointFibres Sun28.PreparedPoles
  Sun28.GlobalDescent Sun28.GlobalSections Sun28.TwistRank Sun28.TwistExtension Sun28.PointLifts

noncomputable section

/-- The remaining simultaneous rational-point assertion uses one order of the signed quartic. -/
def RemainingSections := ∀ b d:ℕ, AdmissiblePair b d → InputClass b → FixedSquares d →
    NormConic b d → ¬FactorPair b d → ¬OneQuartic (b:ℚ) d →
    (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) d t) → ¬CancelledFactors b d →
    ∃ s:ℚ, 0<s ∧ s^2<d ∧ AllowedRatio b d s ∧ padicValRat 3 s=0 ∧
      ¬KnownOrbit (s^2/d) (b*lead (s^2/d)) ∧ represented b (s^2/d)

theorem remaining_sections_iff : RemainingSections ↔ Sun28.GlobalDescent.DescentResidual :=
by
  have h : Sun28.GlobalSections.SectionResidual ↔ RemainingSections :=
    Sun28.CommonPair.sections_outside_orbit
  exact Iff.trans h.symm Sun28.GlobalDescent.sections_iff_descent

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.remaining_sections_iff
