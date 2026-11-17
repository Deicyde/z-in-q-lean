import PublishedGenusRows
import TYZMultisetWeights
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5

namespace ZOverQ.Bounded

open ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b
open ZInQBlueprint.TYZ ZInQBlueprint.OriginalRank.PublishedGenusRows

/-- Both sums in Tian's sufficient condition count unordered factorizations. -/
def OddGenusRow (d : ℕ) : Prop := Odd (rowSum d FirstRow) ∨ Odd (rowSum d TianSecond)

/-- The class-group coefficient equals Tian's weighted sum over unordered
multisets, with the two distinguished factors and the residue-one remainder. -/
theorem tian_multiset_coefficient {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d) :
    unorderedSum hs TianSecond genusNumber = printedCoefficient d hd := by
  classical
  exact (unorderedGenusSum_eq hs TianSecond).trans (tian_second_sum_eq hd)

/-- The exact analytic content of the existential form of Tian's theorem used here.
The specified higher-order branch is zero. The lower-order values and isogeny
indices in that formulation are existentially quantified. -/
theorem tian_iff_orders :
    PublishedTian47 ↔ ∀ d : ℕ, d % 8 = 5 → Squarefree d → OddGenusRow d →
      ∀ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F →
        ¬ 2 ≤ analyticOrderAt F 1 := by
  constructor
  · rintro ⟨lower, rho, source⟩ d hd hs hrow F hF high
    obtain ⟨k, hk⟩ := source d hd hs hrow
    rw [zero_branch lower d hd hs F hF high] at hk
    have hz : (0 : ℤ) = 2 * k + 1 := by
      exact_mod_cast (show (0 : ℚ) = 2 * (k : ℚ) + 1 by simpa using hk)
    omega
  · intro bound
    refine ⟨fun _ => 1, fun _ => 0, ?_⟩
    intro d hd hs hrow
    have excluded : ¬ ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧
        2 ≤ analyticOrderAt F 1 := by
      rintro ⟨F, hF, high⟩
      exact bound d hd hs hrow F hF high
    exact ⟨0, by simp [normalized, excluded]⟩

/-- Entire continuation with central zero for the congruent-number twists of sign minus one. -/
def CentralZero : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∃ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧ F 1 = 0

/-- The Gaussian Hecke series gives the continuation and its functional equation. -/
theorem central_zero : CentralZero := by
  intro d hd hs
  obtain ⟨cont, fe⟩ := ZInQ.Contrib.GaussFE.literature_hecke_fe
  obtain ⟨F, hF⟩ := cont d hd hs
  exact ⟨F, hF, rootNumberVanishing_of_functionalEquation fe d hd hs F hF⟩

/-- Either odd genus sum forces a simple zero of the arithmetic L-function. -/
theorem simple_zero_of_odd_row (criterion : PublishedTian47) {d : ℕ}
    (hd : d % 8 = 5) (hs : Squarefree d) (hrow : OddGenusRow d) {F : ℂ → ℂ}
    (hF : IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F) : analyticOrderAt F 1 = 1 := by
  have low : analyticOrderAt F 1 ≤ 1 := by
    by_contra h
    exact tian_iff_orders.mp criterion d hd hs hrow F hF (two_le_of_not_le_one h)
  have zero := rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5 d hd hs F hF
  exact enat_eq_one low (analyticOrderAt_ne_zero.mpr ⟨hF.1.analyticAt 1, zero⟩)

/-- The positive-rank consequence of a simple central zero. -/
abbrev SimpleZeroRank := ZInQ.Literature.GrossZagier

/-- The class-group test of the polynomial construction is Tian's second row. -/
theorem odd_row_of_class_sum {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d)
    (hrow : T5bCl d = 1) : OddGenusRow d := by
  apply Or.inr
  rw [tian_second_sum_eq hd]
  apply Nat.not_even_iff_odd.mp
  intro even
  have hmod := even.natCast_zmod_two
  rw [printedCoefficient_mod_two hd hs, hrow] at hmod
  exact one_ne_zero hmod

private theorem rank_at_central_zero (criterion : PublishedTian47) (central : CentralZero)
    (rank : SimpleZeroRank)
    {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d) (hrow : OddGenusRow d) :
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬ IsOfFinAddOrder P := by
  obtain ⟨F, hF, _⟩ := central d hd hs
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  exact rank _ (shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0))) F hF
    (simple_zero_of_odd_row criterion hd hs hrow hF)

/-- A non-torsion rational point exists for either of Tian's two odd genus sums. -/
theorem rank_of_odd_row (criterion : PublishedTian47) (rank : SimpleZeroRank)
    {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d) (hrow : OddGenusRow d) :
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬ IsOfFinAddOrder P :=
  rank_at_central_zero criterion central_zero rank hd hs hrow

/-- Positive rank on every twist selected by the polynomial. -/
theorem certified_rank_from_tian (criterion : PublishedTian47) (rank : SimpleZeroRank) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  fun _ hd hs row => rank_of_odd_row criterion rank hd hs (odd_row_of_class_sum hd hs row)

/-- Glazer's full bounded theorem, assuming the six-contact estimate and the
two literature inputs for the genus sum and the rank of an elliptic curve. -/
theorem bounded_from_height_tian_gross_zagier (height : ZInQ.SixContactMin)
    (criterion : PublishedTian47) (rank : SimpleZeroRank) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    height (certified_rank_from_tian criterion rank)

/-- Compatibility with the earlier formulation that included central vanishing. -/
theorem rank_of_genus (criterion : PublishedTian47) (central : CentralZero)
    (rank : SimpleZeroRank) : ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  fun _ hd hs row => rank_at_central_zero criterion central rank hd hs (odd_row_of_class_sum hd hs row)

/-- Compatibility with the earlier four-hypothesis bounded theorem. -/
theorem bounded_from_height_and_literature (height : ZInQ.SixContactMin)
    (criterion : PublishedTian47) (central : CentralZero) (rank : SimpleZeroRank) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    height (rank_of_genus criterion central rank)

end ZOverQ.Bounded

#print axioms ZOverQ.Bounded.tian_iff_orders
#print axioms ZOverQ.Bounded.tian_multiset_coefficient
#print axioms ZOverQ.Bounded.central_zero
#print axioms ZOverQ.Bounded.simple_zero_of_odd_row
#print axioms ZOverQ.Bounded.odd_row_of_class_sum
#print axioms ZOverQ.Bounded.rank_of_odd_row
#print axioms ZOverQ.Bounded.certified_rank_from_tian
#print axioms ZOverQ.Bounded.bounded_from_height_tian_gross_zagier
#print axioms ZOverQ.Bounded.rank_of_genus
#print axioms ZOverQ.Bounded.bounded_from_height_and_literature
