import SeededPair
import ExplicitProjection
import MarkedSeparation

namespace Sun28.SeededPartners
open Sun28 Sun28.PreparedPoles Sun28.PairedClasses Sun28.SelmerRealization
open Sun28.PrescribedPoints Sun28.SupportMatrix Sun28.TwistRank Sun28.TwistExtension
open Sun28.PointLifts Sun28.PointFibres Sun28.GlobalDescent Sun28.GlobalSections
open ZInQBlueprint.FiveMetric ZInQBlueprint.Diagonal210 ZInQBlueprint.CMPeriods
open ZInQBlueprint.IntegralSections ZInQBlueprint.DiamondHeight Sun28.MultiplierChoice Sun28.Concrete
open private admissible_nonsquare from OrbitResidual
noncomputable section

/-- The first marked class has a rational point. The same class on the
companion is tested at every place in the definition of localClasses. -/
structure Candidate (b d q : ℕ) : Prop where
  nontrivial : 1<q
  squarefree : Squarefree (b*q)
  coprime : (b*q).Coprime (6*d)
  residue : (b*q)%12=11
  companion_residue : ((b*q)*d)%12=11
  rational_first : Cover ℚ (b*q) b 1
  local_second : ((b:ℤ),1) ∈ localClasses ((b*q)*d)

theorem candidates_unbounded {b d : ℕ} (ad : AdmissiblePair b d) (B : ℕ) :
    ∃ q>B, Candidate b d q := by
  obtain ⟨q,H,s,c,r,t,pt,localPt⟩ := seeded_pair ad (max B 1)
  exact ⟨q,(le_max_left _ _).trans_lt H,(le_max_right _ _).trans_lt H,s,c,r,t,pt,localPt⟩

private theorem nonsquare_nat {m : ℕ} (sf : Squarefree m) (big : 1 < m) : ¬IsSquare (m:ℚ) := by
  intro H
  obtain ⟨z,e⟩:=Rat.isSquare_natCast_iff.mp H
  rw [e] at sf big
  have unit := sf z dvd_rfl
  rw [Nat.isUnit_iff] at unit
  simp [unit] at big

theorem pair_of_partner {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (P : Cover ℚ ((b*q)*d) b 1) : NonzeroPair b d := by
  obtain ⟨_,_,sq⟩ := Nat.squarefree_mul_iff.mp C.squarefree
  have qd : q.Coprime d := ((Nat.coprime_mul_iff_left.mp C.coprime).2.coprime_dvd_right
    (dvd_mul_left d 6))
  have qs : Squarefree (q*d) := Nat.squarefree_mul_iff.mpr ⟨qd,sq,ad.2.2.2.1⟩
  have big := C.nontrivial
  have dp := ad.2.1
  have big2 : 1<q*d := by nlinarith
  have bp : 0<(b:ℚ) := by exact_mod_cast ad.1
  have qp : 0<(q:ℚ) := by exact_mod_cast (show 0<q by omega)
  have H := pair_of_covers (θ:=(d:ℚ)) (l:=(b:ℚ)*q) bp (mul_pos bp qp) (by exact_mod_cast dp) (admissible_nonsquare ad)
  apply H
  · simpa [mul_div_cancel_left₀ _ bp.ne'] using nonsquare_nat sq big
  · rw [mul_assoc,mul_div_cancel_left₀ _ bp.ne']
    exact_mod_cast nonsquare_nat qs big2
  · simpa using (rational_cover (b*q) b).mp C.rational_first
  · simpa using (rational_cover ((b*q)*d) b).mp P

/-- On the residual prepared inputs, some candidate must lift its one
specified companion class. Universality across candidates is unnecessary. -/
def CompanionLift : Prop := ∀ b d : ℕ, AdmissiblePair b d → InputClass b → FixedSquares d →
    NormConic b d → ¬FactorPair b d → ¬OneQuartic (b:ℚ) d →
    (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) d t) → ¬CancelledFactors b d →
    ∃ q, Candidate b d q ∧ Cover ℚ ((b*q)*d) b 1

theorem sections_of_companion (lift : CompanionLift) : RemainingSections := by
  intro b d ad inp fixed norm factors out ratios cancelled
  obtain ⟨q,chosen,P⟩:=lift b d ad inp fixed norm factors out ratios cancelled
  have surface := (surface_iff_one_or_nonzero (by exact_mod_cast ad.1) (by exact_mod_cast ad.2.1.ne')).mpr
    (Or.inr (pair_of_partner ad chosen P))
  obtain ⟨s,pos,short,allowed,v,marked⟩:=reduced_ratio ad out surface
  exact ⟨s,pos,short,allowed,v,Sun28.CommonPair.orbit_excluded ad out pos short v,marked⟩

theorem companion_of_rank {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    [AddGroup.FG (RationalPoint ((b*q)*d))]
    (count : (localClasses ((b*q)*d)).ncard=8)
    (point : ∃ P : RationalPoint ((b*q)*d), ¬IsOfFinAddOrder P) :
    Cover ℚ ((b*q)*d) b 1 := by
  have qp := C.nontrivial
  have lp : 0<b*q*d := Nat.mul_pos (Nat.mul_pos ad.1 (by omega)) ad.2.1
  exact all_classes_realized lp (Sun28.MarkedDescent.kummer_separation lp)
    (eight_of_infinite_point lp point) count _ C.local_second

set_option maxRecDepth 14000
set_option exponentiation.threshold 250
theorem polynomial_of_companion (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72) (quadric : ConeCount.PublishedQuadricCount)
    (rows : CommonRows.PairCorrectedInputs) (lift : CompanionLift) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 oneSignPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  one_sign table fibres realCurves quadric rows (sections_of_companion lift) x

end
end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.candidates_unbounded
#print axioms Sun28.SeededPartners.pair_of_partner
#print axioms Sun28.SeededPartners.sections_of_companion
#print axioms Sun28.SeededPartners.companion_of_rank
#print axioms Sun28.SeededPartners.polynomial_of_companion
