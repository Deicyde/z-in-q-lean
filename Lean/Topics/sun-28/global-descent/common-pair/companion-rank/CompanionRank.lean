import IntegralMarkedRank
import PartnerProjection

namespace Sun28.CompanionRank
open Sun28.SelmerRealization Sun28.SeededPartners Sun28.PairedClasses
noncomputable section

private theorem b_gt_one {b d : ℕ} (ad : AdmissiblePair b d) : 1<b := by
  obtain ⟨_,_,_,_,_,_,_,r,_⟩ := ad
  omega

/-- Every first curve of the family has a point of infinite order with the
specified mark, and eight distinct classes modulo doubling. -/
theorem candidate_first {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q) :
    (∃ P : RationalPoint (b*q), labels (b*q) P=((b:ℤ),1) ∧ ¬IsOfFinAddOrder P) ∧
    EightPointClasses (b*q) :=
  marked_cover_rank (b_gt_one ad) C.nontrivial rfl C.squarefree C.rational_first

theorem candidate_companion {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (M : Cover ℚ ((b*q)*d) b 1) :
    (∃ P : RationalPoint ((b*q)*d), labels ((b*q)*d) P=((b:ℤ),1) ∧ ¬IsOfFinAddOrder P) ∧
    EightPointClasses ((b*q)*d) := by
  have cd := C.coprime.coprime_dvd_right (dvd_mul_left d 6)
  have sf := Nat.squarefree_mul_iff.mpr ⟨cd,C.squarefree,ad.2.2.2.1⟩
  have qp := C.nontrivial
  have dp := ad.2.1
  exact marked_cover_rank (b_gt_one ad) (k:=q*d) (by nlinarith) (Nat.mul_assoc ..) sf M

/-- When its local set has eight labels, solubility of the companion
cover is exactly equivalent to positive rational rank. -/
theorem candidate_companion_iff {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    [AddGroup.FG (RationalPoint ((b*q)*d))] (eight : (localClasses ((b*q)*d)).ncard=8) :
    Cover ℚ ((b*q)*d) b 1 ↔ ∃ P : RationalPoint ((b*q)*d), ¬IsOfFinAddOrder P := by
  constructor
  · intro M
    obtain ⟨P,_,point⟩ := (candidate_companion ad C M).1
    exact ⟨P,point⟩
  · exact companion_of_rank ad C eight

/-- If the local set has eight labels, the distinguished companion is
rational precisely when there are eight rational classes. -/
theorem candidate_companion_iff_eight {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (eight : (localClasses ((b*q)*d)).ncard=8) :
    Cover ℚ ((b*q)*d) b 1 ↔ EightPointClasses ((b*q)*d) := by
  have qp := C.nontrivial
  have lp : 0<b*q*d := Nat.mul_pos (Nat.mul_pos ad.1 (by omega)) ad.2.1
  exact ⟨fun M => (candidate_companion ad C M).2, fun classes =>
    all_classes_realized lp (Sun28.MarkedDescent.kummer_separation lp) classes eight _ C.local_second⟩

/-- For every prepared pair and every height cutoff there is a larger
multiplier with the first conclusion and the matching everywhere-local mark. -/
theorem unbounded_marked_rank {b d : ℕ} (ad : AdmissiblePair b d) (B : ℕ) :
    ∃ q>B, Candidate b d q ∧ (∃ P : RationalPoint (b*q),
      labels (b*q) P=((b:ℤ),1) ∧ ¬IsOfFinAddOrder P) ∧ EightPointClasses (b*q) ∧
      ((b:ℤ),1) ∈ localClasses ((b*q)*d) := by
  obtain ⟨q,large,C⟩ := candidates_unbounded ad B
  exact ⟨q,large,C,(candidate_first ad C).1,(candidate_first ad C).2,C.local_second⟩

end
end Sun28.CompanionRank

#print axioms Sun28.CompanionRank.candidate_first
#print axioms Sun28.CompanionRank.candidate_companion
#print axioms Sun28.CompanionRank.candidate_companion_iff
#print axioms Sun28.CompanionRank.candidate_companion_iff_eight
#print axioms Sun28.CompanionRank.unbounded_marked_rank
