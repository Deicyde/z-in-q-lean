import BranchFields
import DivisorFields

/-! The branch-coordinate bound and precisely the divisor rows consumed by the proof. -/
namespace ZInQBlueprint.BranchHeight
open TYZ TYZ.Specialization TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- Bounded polynomial existence from the untwisted sextic and divisor-local genus data. -/
theorem frozen_of_untwisted_height_and_odd_rows
    (height : UntwistedBranchHeight) (D : RecursionData) (base : D.L 1 = 1)
    (periods : ClassThreePeriods D.L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 → OddRowTraces D n) :
    ZInQ.FrozenTarget :=
  HeightBudget.frozen_of_remaining_and_class_rank (remaining_of_branchHeight (untwisted_iff.mp height))
    (rank_of_divisor_traces D base periods rows)

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.frozen_of_untwisted_height_and_odd_rows
