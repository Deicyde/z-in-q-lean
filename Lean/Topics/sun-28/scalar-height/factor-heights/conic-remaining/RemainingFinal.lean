import ConeCells
import QuarticRank

namespace Sun28.ConicRemaining
open Sun28.ScalarRankZero Sun28.ScalarDepth Sun28.ConicArithmetic Sun28.ScalarHeight Sun28.Ordinary

theorem nonpositive_by_elementary_rank (sel:PositiveSelmerSelection) (descent:TwoIsogenyRank)
    (red:OddGoodReduction) (x:ℚ):¬Sun28.ConicCovers.positiveParameter x :=
  @no_positive_of_rank sel (@short_rank_of_three descent empty_three) red x

theorem scalar_of_elementary_rank (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (sel:PositiveSelmerSelection) (est:NegativeExceptionalScalarBound) : ScalarBound :=
  @scalar_of_three_quartics descent reduction sel empty_three est

end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.nonpositive_by_elementary_rank
#print axioms Sun28.ConicRemaining.scalar_of_elementary_rank
