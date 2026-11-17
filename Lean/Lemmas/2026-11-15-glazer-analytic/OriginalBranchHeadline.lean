import ZInQKernel.Contrib.GaussFE.Headline
import BranchHeightDescent
import BranchHeightCriterion

namespace ZInQBlueprint.OriginalBranch

/-- Glazer’s frozen integer-definition theorem from the intrinsic sextic height
bound and the two analytic-rank inputs still required by the PR64 headline. -/
theorem frozen_of_canonicalBranchBound_tyzReadingA_grossZagier
    (height : BranchHeight.CanonicalBranchBound)
    (tyz : ZInQ.Literature.TYZThm35ReadingA)
    (gz : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget :=
  ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier
    (BranchHeight.sixContactMin_of_branchHeight (BranchHeight.canonical_iff_bounded.mp height))
    tyz gz

end ZInQBlueprint.OriginalBranch

#print axioms ZInQBlueprint.OriginalBranch.frozen_of_canonicalBranchBound_tyzReadingA_grossZagier

