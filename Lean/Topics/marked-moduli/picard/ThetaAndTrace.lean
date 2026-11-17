import ThomaeHeight
import TYZGaussianTorsion

namespace ZInQBlueprint
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- Bounded existence from the period comparisons on a literal sextic and the
published local CM laws on primitive genus traces. The coefficient on the
recursive point and the rational height of its modular parameter are deduced. -/
theorem frozen_of_periods_and_local_traces
    (hp : ThetaPeriod.HasSiegelPeriods ∨ ThetaPeriod.HasThomaePeriods)
    (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (fields : TraceFields (S.recursion L eps) S.extended)
    (torsion : ∀ n, n%8=5 → Squarefree n → ∀ Y : pointsOver (genusCompositum S.extended n),
      ∀ m : ℕ, 0 < m → m • Y.val = 0 →
        onePlusI (onePlusI (onePlusI Y.val)) = 0)
    (localTraces : ∀ n, n%8=5 → Squarefree n → ∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n ∧
      GaloisMinus n (tyzIsogeny ((2:ℕ) • representative (S.recursion L eps) n))) :
    ZInQ.FrozenTarget := by
  apply HeightBudget.frozen_of_remaining_and_class_rank _
    (publicRank_of_compositumTraces S L eps h1 hc fields
      (fun n hn hs Y m hm hz => gaussian_torsion (torsion n hn hs Y m hm hz)) localTraces)
  rcases hp with direct | thomae
  · exact ThetaApplication.remaining_of_fibres (SexticThetaHeight.thetaFibres_of_periods
      (ThetaPeriod.sexticPeriods_of_siegelPeriods direct))
  · exact ThetaPeriod.remaining_of_thomaePeriods thomae

end
end ZInQBlueprint
#print axioms ZInQBlueprint.frozen_of_periods_and_local_traces
