import PublicHeightFromGeometry
import ZInQKernel.RouteK.RankVariants

/-! The effective height calculation and the actual public rank endpoint in one Lean environment. -/
namespace ZInQBlueprint.PublicRankJoin

/-- The three fibre comparisons at the primes used in multiplication give the exact height premise. -/
theorem sixContactMin_of_geometricComparisons (h : GeometricComparisons ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  height_of_comparisons h

/-- Bounded existence follows from the three numerical height comparisons on the same fibre
and the class-number criterion for an infinite-order rational point on the congruent-number curve. -/
theorem frozen_of_geometry_and_class_rank
    (h : GeometricComparisons ZInQ.Mult.S_mul)
    (hRank : ZInQ.RouteK.Rank.CertifiedRankTYZClRk) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (sixContactMin_of_geometricComparisons h) hRank

#print axioms sixContactMin_of_geometricComparisons
#print axioms frozen_of_geometry_and_class_rank
end ZInQBlueprint.PublicRankJoin
