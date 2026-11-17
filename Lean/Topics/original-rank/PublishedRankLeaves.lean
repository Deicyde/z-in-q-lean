import ZInQKernel.Contrib.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.TopChain
import BranchHeightCriterion
import BranchHeightDescent

namespace ZInQBlueprint.OriginalRank

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- The original bounded polynomial using the intrinsic sextic height and the
six explicit genus-point and analytic inputs of the public PR114 draft. -/
theorem frozen_of_height_and_published_leaves
    (height : BranchHeight.CanonicalBranchBound)
    (integral : TYZThm11Integral)
    (classNumber : TYZLemma29Mod2)
    (reciprocity : Shimura.ShimuraReciprocityModFn)
    (factorization : TYZSplit.TYZThm33)
    (nonvanishing : ZInQ.GZDecomp.FHNonvanishing)
    (heegner : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (BranchHeight.sixContactMin_of_branchHeight (BranchHeight.canonical_iff_bounded.mp height))
    (TYZSplit.tyzThm35ReadingA_of_printedThm33 integral classNumber reciprocity factorization)
    ZInQ.GZTheta.Frontier.heckeThetaNewform nonvanishing heegner

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.frozen_of_height_and_published_leaves
