import PublicAntiCurve
import PublicRankJoin

namespace ZInQBlueprint.PublicRankJoin

theorem frozen_of_geometry_and_antiPoint
    (h : GeometricComparisons ZInQ.Mult.S_mul) (hAnti : OddClassSumToAntiPoint) :
    ZInQ.FrozenTarget :=
  frozen_of_geometry_and_class_rank h (certifiedRank_of_oddClassSumToAntiPoint hAnti)

#print axioms frozen_of_geometry_and_antiPoint
end ZInQBlueprint.PublicRankJoin
