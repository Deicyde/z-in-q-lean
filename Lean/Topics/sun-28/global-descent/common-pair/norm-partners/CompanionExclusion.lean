import QuarticCover

namespace Sun28.NormPartners
open Sun28.SelmerRealization Sun28.SeededPartners Sun28.PairedClasses Sun28.GlobalSections
open Sun28.TwistRank Sun28.TwistExtension Sun28.PrescribedPoints Sun28.PointFibres
noncomputable section

private theorem shapes {b d q:ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q) :
    1<b ∧ 1<q*d ∧ Squarefree (b*(q*d)) := by
  have dm := ad.2.1
  have bm := ad.2.2.2.2.2.2.2.1
  have qm := C.nontrivial
  have cp : (b*q).Coprime d := C.coprime.coprime_dvd_right (dvd_mul_left d 6)
  have sf := Nat.squarefree_mul_iff.mpr ⟨cp,C.squarefree,ad.2.2.2.1⟩
  exact ⟨by omega,by nlinarith,by simpa only [Nat.mul_assoc] using sf⟩

theorem candidate_quartics {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q) :
    Family b q ∧ (Cover ℚ ((b*q)*d) b 1 ↔ Family b (q*d)) := by
  obtain ⟨bb,qd,sf⟩ := shapes ad C
  exact ⟨family_of_cover bb C.nontrivial C.squarefree C.rational_first,
    by simpa only [Nat.mul_assoc] using cover_iff_family bb qd sf⟩

theorem cancelled_of_companion {b d q : ℕ} (ad : AdmissiblePair b d)
    (C : Candidate b d q) (hit : Cover ℚ ((b*q)*d) b 1) : CancelledFactors b d := by
  obtain ⟨first,second⟩ := candidate_quartics ad C
  exact ⟨q,C.nontrivial,C.squarefree,C.coprime,Or.inl first,Or.inl (second.mp hit)⟩

/-- Once the overlapping factorizations have been excluded, the full
marked companion is insoluble over Q for every candidate. -/
theorem all_companions_fail {b d : ℕ} (ad : AdmissiblePair b d) (outside : ¬CancelledFactors b d)
    {q : ℕ} (C : Candidate b d q) : ¬Cover ℚ ((b*q)*d) b 1 :=
  fun hit => outside (cancelled_of_companion ad C hit)

/-- The eight antecedent tests that the existing candidate reduction consumes. -/
def Residual (b d : ℕ) : Prop :=
  AdmissiblePair b d ∧ InputClass b ∧ FixedSquares d ∧ NormConic b d ∧
  ¬FactorPair b d ∧ ¬OneQuartic (b:ℚ) d ∧ (∀ t:ℚ, t≠0 → ¬RatioCover (b:ℚ) d t) ∧ ¬CancelledFactors b d

theorem companion_iff_no_residual : CompanionLift ↔ ¬∃ b d, Residual b d := by
  constructor
  · rintro H ⟨b,d,ad,inp,fix,norm,fac,one,ratio,cancel⟩
    obtain ⟨q,C,hit⟩ := H b d ad inp fix norm fac one ratio cancel
    exact all_companions_fail ad cancel C hit
  · intro none b d ad inp fix norm fac one ratio cancel
    exact (none ⟨b,d,ad,inp,fix,norm,fac,one,ratio,cancel⟩).elim

end
end Sun28.NormPartners
#print axioms Sun28.NormPartners.candidate_quartics
#print axioms Sun28.NormPartners.cancelled_of_companion
#print axioms Sun28.NormPartners.all_companions_fail
#print axioms Sun28.NormPartners.companion_iff_no_residual
