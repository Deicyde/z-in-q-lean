import CompanionExclusion
import CompanionRank

namespace Sun28.NormPartners
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.SeededPartners Sun28.GlobalSections
open Sun28.CompanionRank Sun28.Corank
noncomputable section

theorem local_eight_torsion {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (outside : ¬CancelledFactors b d) [AddGroup.FG (RationalPoint ((b*q)*d))]
    (size : (localClasses ((b*q)*d)).ncard = 8) (P : RationalPoint ((b*q)*d)) : IsOfFinAddOrder P := by
  by_contra non
  apply all_companions_fail ad outside C
  exact (candidate_companion_iff ad C size).mpr ⟨P,non⟩

/-- Conditional on the stated exact primary Kummer sequences, finite
generation, eight local classes and the exclusions force the entire
nonrational alternative on the companion: r=0, divisible corank one,
and zero finite reduced two-primary group. -/
theorem local_eight_divisible {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (outside : ¬CancelledFactors b d) [AddGroup.FG (RationalPoint ((b*q)*d))]
    (K : PrimaryData (RationalPoint ((b*q)*d))) (comparison : LocalComparison ((b*q)*d) K)
    (size : (localClasses ((b*q)*d)).ncard = 8) :
    K.d=1 ∧ Subsingleton K.reduced ∧ Finite (RationalPoint ((b*q)*d)) := by
  have qpos : 0<q := lt_trans Nat.zero_lt_one C.nontrivial
  have lp : 0<b*q*d := Nat.mul_pos (Nat.mul_pos ad.1 qpos) ad.2.1
  have nozero : K.d≠0 := by
    intro zero
    apply all_companions_fail ad outside C
    apply (candidate_companion_iff_eight ad C size).mpr
    exact (eight_rational_iff lp K comparison size).mpr zero
  obtain ⟨r,T,_,_,⟨f⟩⟩ := split_finitely_generated (RationalPoint ((b*q)*d))
  have result := corank_one K f (four_torsion lp) (card_first K comparison size)
  obtain rfl : r=0 := by omega
  exact ⟨by omega,result.1,Finite.of_equiv _ f.symm.toEquiv⟩

end
end Sun28.NormPartners
#print axioms Sun28.NormPartners.local_eight_torsion
#print axioms Sun28.NormPartners.local_eight_divisible
