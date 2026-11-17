import PrintedHeightEndpoint
import CongruentNumberParity
import ModularSimpleZero

namespace ZInQBlueprint.OriginalRank

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- The five-congruence genus coefficient at vanishing derivative from the odd
central-value formula, CM reciprocity and the genus-point factorization. -/
theorem printed_derivative_of_genus_periods (central : OddCentralValueParity)
    (reciprocity : Shimura.ShimuraReciprocityModFn) (factorization : TYZSplit.TYZThm33) :
    SelectedTwists.PrintedBracketDerivative :=
  let h := oddCentralValueParity_iff.mp central
  printed_bracket_of_four_leaves h.1 (lemma29Mod2_of_thm11Mod2 h.2) reciprocity factorization

/-- A height bound and five arithmetic statements suffice for the bounded
Diophantine definition. The central-value statement uses unordered integer
factorizations and allows an independent sign at each argument. -/
theorem frozen_of_height_and_five_rank_inputs (height : BranchHeight.CanonicalBranchBound)
    (central : OddCentralValueParity) (reciprocity : Shimura.ShimuraReciprocityModFn)
    (factorization : TYZSplit.TYZThm33) (nonvanishing : ZInQ.GZDecomp.FHNonvanishing)
    (heegner : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget :=
  let h := oddCentralValueParity_iff.mp central
  frozen_of_height_and_published_leaves height h.1 (lemma29Mod2_of_thm11Mod2 h.2)
    reciprocity factorization nonvanishing heegner

/-- Replacing the derivative bracket by its three arithmetic ingredients
gives one geometric estimate and four arithmetic statements. -/
theorem frozen_of_height_and_four_rank_inputs (height : BranchHeight.CanonicalBranchBound)
    (central : OddCentralValueParity) (reciprocity : Shimura.ShimuraReciprocityModFn)
    (factorization : TYZSplit.TYZThm33) (rank : ModularSimpleZero) : ZInQ.FrozenTarget :=
  frozen_of_height_printed_modular_simple_zero height
    (printed_derivative_of_genus_periods central reciprocity factorization) rank

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.printed_derivative_of_genus_periods
#print axioms ZInQBlueprint.OriginalRank.frozen_of_height_and_five_rank_inputs

#print axioms ZInQBlueprint.OriginalRank.frozen_of_height_and_four_rank_inputs
