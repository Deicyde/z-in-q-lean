import BranchHeightDescent
import OddTraceRank
import MergedBranch
import ZInQKernel.MainLiterature

/-! Intrinsic branch heights and odd CM trace rows at the bounded polynomial theorem. -/
namespace ZInQBlueprint.BranchHeight
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction

/-- The merged bounded-existence theorem with the intrinsic coordinate height
and primitive odd-row CM traces. -/
theorem frozen_of_canonical_height_and_cm_rows
    (height : CanonicalBranchBound) (D : RecursionData) (base : D.L 1 = 1)
    (periods : ClassThreePeriods D.L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 → OddRowCM D n) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_certifiedRankTYZClRk
    (public_jHeight_of_branchHeight (canonical_iff_bounded.mp height))
    (rank_of_cm_odd_rows D base periods rows)

/-- Fixed labelled periods supply the intrinsic branch height with exactly the
same rank hypotheses. -/
theorem frozen_of_fixed_periods_and_cm_rows
    (height : ThetaPeriod.HasFixedPeriods) (D : RecursionData) (base : D.L 1 = 1)
    (periods : ClassThreePeriods D.L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 → OddRowCM D n) :
    ZInQ.FrozenTarget :=
  frozen_of_canonical_height_and_cm_rows (canonical_of_fixedPeriods height) D base periods rows

end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.frozen_of_canonical_height_and_cm_rows
#print axioms ZInQBlueprint.BranchHeight.frozen_of_fixed_periods_and_cm_rows
