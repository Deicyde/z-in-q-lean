import BranchInvariant
import ThetaAndTrace

namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient SexticThetaHeight Polynomial
noncomputable section

/-- The labelled first Thomae formula, together with the two comparisons on the
same stable height. The algebraic identity of the branch weights is a theorem. -/
structure LabelledPeriod (u δ : ℚ) (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) where
  matrix : SiegelPeriod
  roots : Fin 6 → ℂ
  distinct : Function.Injective roots
  root : ∀ i, aeval (roots i) (sextic u δ) = 0
  label : Fin 10 ≃ Partition
  scale : ℂˣ
  thomae : ∀ i, thetaNull matrix (evenIndices i)^8 =
    (scale:ℂ)*branchValue (finiteBranches roots) (label i)
  stable : ℝ
  comparison : let e := of_sextic_thomae hu hδ roots distinct root label scale thomae (thetaNull_odd matrix)
    let h := chartHeight (thetaNull matrix) (eighth_ratios_algebraic e)
    |max 1 h - max 1 (stable + Real.log Real.pi)/2| ≤ ThetaMetric.pazukiConstant *
      Real.log (min (max 1 h) (max 1 (stable + Real.log Real.pi)) + 2)
  reduction : stable ≤ HeightBudget.vonKaenelBudget u

def LabelledPeriod.toThomae {u δ : ℚ} {hu : u ∉ ZInQ.contactSet} {hδ : δ ≠ 0}
    (p : LabelledPeriod u δ hu hδ) : ThomaePeriodData u δ hu hδ where
  matrix := p.matrix
  roots := p.roots
  distinct := p.distinct
  root := p.root
  label := p.label
  scale := p.scale
  thomae := p.thomae
  branchInvariant := BranchFormula.sextic_branch_invariant hu hδ p.roots p.distinct p.root p.label
  stable := p.stable
  comparison := p.comparison
  reduction := p.reduction

def HasLabelledPeriods : Prop := ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet),
  ∃ (δ : ℚ) (hδ : δ ≠ 0), Nonempty (LabelledPeriod u δ hu hδ)

theorem thomaePeriods_of_labelledPeriods (h : HasLabelledPeriods) : HasThomaePeriods := by
  intro u hu
  obtain ⟨δ,hδ,⟨p⟩⟩ := h u hu
  exact ⟨δ,hδ,⟨p.toThomae⟩⟩

theorem remaining_of_labelledPeriods (h : HasLabelledPeriods) : HeightBudget.RemainingComparisons :=
  remaining_of_thomaePeriods (thomaePeriods_of_labelledPeriods h)

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.LabelledPeriod.toThomae
#print axioms ZInQBlueprint.ThetaPeriod.thomaePeriods_of_labelledPeriods
#print axioms ZInQBlueprint.ThetaPeriod.remaining_of_labelledPeriods

namespace ZInQBlueprint
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- The squared height route needs the labelled analytic period and the height comparisons. -/
theorem frozen_of_labelled_periods_and_local_traces
    (hp : ThetaPeriod.HasSiegelPeriods ∨ ThetaPeriod.HasLabelledPeriods)
    (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (fields : TraceFields (S.recursion L eps) S.extended)
    (torsion : ∀ n, n%8=5 → Squarefree n → ∀ Y : pointsOver (genusCompositum S.extended n),
      ∀ m : ℕ, 0 < m → m • Y.val = 0 →
        onePlusI (onePlusI (onePlusI Y.val)) = 0)
    (localTraces : ∀ n, n%8=5 → Squarefree n → ∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n ∧
      GaloisMinus n (tyzIsogeny ((2:ℕ) • representative (S.recursion L eps) n))) :
    ZInQ.FrozenTarget := by
  apply frozen_of_periods_and_local_traces _ S L eps h1 hc fields torsion localTraces
  exact hp.imp_right ThetaPeriod.thomaePeriods_of_labelledPeriods

end
end ZInQBlueprint
#print axioms ZInQBlueprint.frozen_of_labelled_periods_and_local_traces
