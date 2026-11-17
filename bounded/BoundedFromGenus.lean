import PublishedGenusRows

namespace ZOverQ.Bounded

open ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b
open ZInQBlueprint.TYZ ZInQBlueprint.OriginalRank ZInQBlueprint.OriginalRank.PublishedGenusRows

/-- The continuation and central vanishing for the congruent-number twists of sign minus one. -/
def CentralZero : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∃ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧ F 1 = 0

/-- The positive-rank consequence of a simple zero for a rational elliptic curve. -/
def SimpleZeroRank : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ F : ℂ → ℂ,
    IsLContinuation E F → analyticOrderAt F 1 = 1 →
    ∃ P : E.toAffine.Point, ¬ IsOfFinAddOrder P

/-- Compare the class-group parity in the original assembly with the integer
coefficient in the published genus criterion. -/
theorem rank_of_genus (criterion : PublishedTian47) (central : CentralZero)
    (rank : SimpleZeroRank) : ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hs hrow
  obtain ⟨F,hF,hzero⟩ := central d hd hs
  have ha := hF.1.analyticAt (1 : ℂ)
  have hder : deriv F 1 ≠ 0 := by
    intro hz
    have order : 2 ≤ analyticOrderAt F 1 := by
      apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) ha).2
      intro i hi
      interval_cases i <;> simp [hzero,hz]
    have even := higher_order_of_tian47 criterion d hd hs F hF order
    have hmod := even.natCast_zmod_two
    rw [printedCoefficient_mod_two hd hs,hrow] at hmod
    exact one_ne_zero hmod
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  exact rank _ (shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0))) F hF
    (ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hder)

/-- Glazer’s bounded polynomial theorem from the six-contact estimate, Tian’s
published genus criterion, central vanishing, and the simple-zero rank theorem. -/
theorem bounded_from_height_and_literature (height : ZInQ.SixContactMin)
    (criterion : PublishedTian47) (central : CentralZero) (rank : SimpleZeroRank) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    height (rank_of_genus criterion central rank)

end ZOverQ.Bounded

#print axioms ZOverQ.Bounded.rank_of_genus
#print axioms ZOverQ.Bounded.bounded_from_height_and_literature
