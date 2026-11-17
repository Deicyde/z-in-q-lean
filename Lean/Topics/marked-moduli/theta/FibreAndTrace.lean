import ThetaApplication
import TYZCuspRank

namespace ZInQBlueprint

/-- The two families of witnesses suffice for the pinned bounded-existence theorem. -/
theorem frozen_of_theta_fibres_and_traces (hf : ThetaApplication.HasThetaFibres)
    (ht : ∀ d (hd : d % 8 = 5), Squarefree d →
      Nonempty (TYZ.Specialization.TraceData d hd)) : ZInQ.FrozenTarget :=
  ThetaApplication.frozen_of_fibres_and_rank hf (TYZ.Specialization.publicRank_of_traces ht)

/-- Only odd values of the printed class-number sum enter the rank implication. -/
def HasOddTraces : Prop :=
  ∀ d (hd : d % 8 = 5), Squarefree d → ZInQ.RouteK.Rank5b.T5bCl d = 1 →
    Nonempty (TYZ.Specialization.TraceData d hd)

theorem certifiedRank_of_odd_traces (ht : HasOddTraces) : ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro d hd hs hOdd
  obtain ⟨D⟩ := ht d hd hs hOdd
  exact TYZ.Specialization.antiPoint_of_trace hd hs D.fieldPoints D.representative
    D.torsion_four D.double_minus D.period hOdd

theorem frozen_of_theta_fibres_and_odd_traces (hf : ThetaApplication.HasThetaFibres)
    (ht : HasOddTraces) : ZInQ.FrozenTarget :=
  ThetaApplication.frozen_of_fibres_and_rank hf (certifiedRank_of_odd_traces ht)

end ZInQBlueprint

#print axioms ZInQBlueprint.frozen_of_theta_fibres_and_traces
#print axioms ZInQBlueprint.certifiedRank_of_odd_traces
#print axioms ZInQBlueprint.frozen_of_theta_fibres_and_odd_traces
