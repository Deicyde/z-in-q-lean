import LocalPreparation
import RegularFibre

namespace Sun28.LocalQuartics
open Sun28.PointLifts Sun28.PairedClasses Sun28.PrescribedPoints Sun28.PreparedPoles
  Sun28.PointFibres Sun28.PointDescent Sun28.TwistRank Sun28.TwistExtension
noncomputable section

def RationalCover (b k : ℕ) : Prop :=
  ∃ U V Y : ℚ, Y≠0 ∧ Y^2=k*quarticForm (b:ℚ) U V

theorem rational_cover_iff_twist {b k : ℕ} (bp : 0<b) (kp : 0<k) :
    RationalCover b k ↔ TwistPoint b (b*k) := by
  rw [twist_iff_quartic bp (Nat.mul_pos bp kp)]
  have B : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  have K : (k:ℚ)≠0 := by exact_mod_cast kp.ne'
  constructor
  · rintro ⟨U,V,Y,yn,E⟩
    change Y^2=k*quartic b U V at E
    refine ⟨U,V,(k:ℚ)/Y,?_⟩
    push_cast;field_simp
    exact E
  · rintro ⟨U,V,w,E⟩
    push_cast at E
    have e : (k:ℚ)=quartic b U V*w^2 := by
      apply mul_left_cancel₀ B
      linear_combination E
    have wn : w≠0 := by intro z;apply K;simpa [z] using e
    refine ⟨U,V,(k:ℚ)/w,div_ne_zero K wn,?_⟩
    change ((k:ℚ)/w)^2=k*quartic b U V
    field_simp
    simpa only [mul_comm] using e

theorem rational_of_both {b θ q : ℕ} (bp : 0<b) (tp : 0<θ) (qp : 0<q)
    (H : RationalCover b q ∧ RationalCover b (q*θ)) : Surface b θ := by
  apply (surface_iff_pair (by exact_mod_cast bp) (by exact_mod_cast tp.ne')).mpr
  have f := (rational_cover_iff_twist bp qp).mp H.1
  have g := (rational_cover_iff_twist bp (Nat.mul_pos qp tp)).mp H.2
  refine ⟨(b*q:ℕ),by exact_mod_cast (Nat.mul_pos bp qp).ne',?_,?_⟩
  · exact f
  · change Sun28.TwistExtension.Point (b:ℚ) ((b*(q*θ):ℕ):ℚ) at g
    simpa only [Nat.cast_mul,mul_assoc] using g

/-- A sufficient choice of rational points, at some prime in the displayed
progression. Requiring these particular primes is a stronger global problem. -/
def PrimeCoverResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) →
  ∃ q>max b θ, q.Prime ∧ q≡1 [MOD 24*b*θ] ∧ RationalCover b q ∧ RationalCover b (q*θ)

theorem regular_of_prime_covers (H : PrimeCoverResidual) : RegularResidual := by
  apply residual_iff_regular.mp
  intro b θ a i f N c o t
  obtain ⟨q,_,pr,_,F,G⟩:=H b θ a i f N c o t
  exact (surface_iff_local_ratios a).mp (rational_of_both a.1 a.2.1 pr.pos ⟨F,G⟩)

end
end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.rational_cover_iff_twist
#print axioms Sun28.LocalQuartics.rational_of_both
#print axioms Sun28.LocalQuartics.regular_of_prime_covers
