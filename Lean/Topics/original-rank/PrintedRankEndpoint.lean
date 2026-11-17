import ModularSimpleZero
import PrintedTwistModel

namespace ZInQBlueprint.OriginalRank

/-- The selected rank implication from the order-greater-than-one case of
the published genus coefficient and the modular positive-rank theorem. -/
theorem selected_rank_of_printed_results (genus : HigherOrderGenusCoefficient)
    (rank : ModularSimpleZero) : ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  SelectedTwists.rank_of_bracket
    (SelectedTwists.printed_iff_bracket.mp (higher_order_iff_printed_derivative.mp genus))
    (selected_rank_of_modular_simple_zero rank)

/-- The bounded polynomial from the intrinsic height and the two literature
implications on the actual normalized curves. -/
theorem frozen_from_height_and_printed_rank (height : BranchHeight.CanonicalBranchBound)
    (genus : HigherOrderGenusCoefficient) (rank : ModularSimpleZero) : ZInQ.FrozenTarget :=
  frozen_of_height_printed_modular_simple_zero height (higher_order_iff_printed_derivative.mp genus) rank

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.selected_rank_of_printed_results
#print axioms ZInQBlueprint.OriginalRank.frozen_from_height_and_printed_rank
