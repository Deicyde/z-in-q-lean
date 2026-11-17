import TwistGroup
import ZInQKernel.RouteK.Rank.Statements

/-! Transfer the infinite-order anti-invariant point to the very curve used by the public rank predicate. -/
namespace ZInQBlueprint.PublicRankJoin

/-- The rational point obtained from (u,v√(-d)) has infinite order in the public model C_d. -/
theorem public_point_of_antiPoint (d : ℕ) (hd : 0 < d) (h : Rank.AntiPoint d) :
    ∃ P : (ZInQ.shortCurve (-(d : ℚ)^2)).toAffine.Point, ¬ IsOfFinAddOrder P := by
  obtain ⟨P, hP⟩ := Rank.negativeTwistDescent d hd h
  refine ⟨P, ?_⟩
  intro hFinite
  obtain ⟨k, hk, hZero⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hFinite
  exact hP k hk hZero

/-- Genus-point input directly on the published class-group sum at the exact public predicate. -/
def OddClassSumToAntiPoint : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ZInQ.RouteK.Rank5b.T5bCl d = 1 → Rank.AntiPoint d

theorem certifiedRank_of_oddClassSumToAntiPoint (h : OddClassSumToAntiPoint) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hs hsum
  exact public_point_of_antiPoint d (by omega) (h d hd hs hsum)

#print axioms public_point_of_antiPoint
#print axioms certifiedRank_of_oddClassSumToAntiPoint
end ZInQBlueprint.PublicRankJoin
