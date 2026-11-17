import PublishedRankLeaves
import PrintedTwists

namespace ZInQBlueprint.OriginalRank

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- Four explicit arithmetic hypotheses suffice for the integer coefficient
on journal page 760, with the derivative at the centre as its antecedent. -/
theorem printed_bracket_of_four_leaves
    (integral : TYZThm11Integral) (classNumber : TYZLemma29Mod2)
    (reciprocity : Shimura.ShimuraReciprocityModFn) (factorization : TYZSplit.TYZThm33) :
    SelectedTwists.PrintedBracketDerivative :=
  SelectedTwists.printed_iff_bracket.mpr (SelectedTwists.bracket_of_readingA
    (TYZSplit.tyzThm35ReadingA_of_printedThm33 integral classNumber reciprocity factorization))

/-- The printed derivative criterion and the selected rank statement suffice. -/
theorem frozen_of_height_four_leaves_selected_rank (height : BranchHeight.CanonicalBranchBound)
    (integral : TYZThm11Integral) (classNumber : TYZLemma29Mod2)
    (reciprocity : Shimura.ShimuraReciprocityModFn) (factorization : TYZSplit.TYZThm33)
    (rank : SelectedTwists.SelectedGrossZagier) : ZInQ.FrozenTarget :=
  SelectedTwists.frozen_of_printed_bracket height
    (printed_bracket_of_four_leaves integral classNumber reciprocity factorization) rank

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.printed_bracket_of_four_leaves
#print axioms ZInQBlueprint.OriginalRank.frozen_of_height_four_leaves_selected_rank
