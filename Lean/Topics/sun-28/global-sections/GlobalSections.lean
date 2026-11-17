import MovingSection
import FixedTwistFamily

namespace Sun28.GlobalSections
open Sun28.PairedClasses Sun28.PreparedPoles Sun28.PrescribedPoints Sun28.TwistRank
  Sun28.TwistExtension Sun28.PointFibres Sun28.PointDescent Sun28.PointLifts
noncomputable section

private theorem class_nonsquare {b θ:ℕ} (a:AdmissiblePair b θ) : ¬IsSquare (b:ℚ) := by
  intro sq
  obtain ⟨k,e⟩:=Rat.isSquare_natCast_iff.mp sq
  have mod3 : k*k%3=2:=by
    have h:=a.2.2.2.2.2.2.2.1
    rw [e] at h
    omega
  rw [Nat.mul_mod] at mod3
  have le:=Nat.mod_lt k (by decide : 0<3)
  interval_cases k%3 <;> norm_num at mod3

theorem regular_iff_section {b θ:ℕ} (a:AdmissiblePair b θ) {s:ℚ}
    (pos:0<s) (short:s^2<θ) (out:¬OneQuartic (b:ℚ) θ) :
    RegularFibre b θ s.num s.den ↔ represented b (s^2/θ) := by
  rw [←single_iff_regular a.1 a.2.1 pos.ne' out]
  exact single_iff_represented (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) pos short
    (class_nonsquare a) out

theorem reduced_ratio {b θ:ℕ} (a:AdmissiblePair b θ) (out:¬OneQuartic (b:ℚ) θ)
    (surf:Surface b θ) :
    ∃ s:ℚ, 0<s ∧ s^2<θ ∧ AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧ represented b (s^2/θ) := by
  obtain ⟨s,allowed,F⟩:=(surface_iff_local_ratios a).mp surf
  obtain ⟨k,hk,short,G⟩:=principal_ratio (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) out allowed.1 F
  exact ⟨k,hk,short,allowed_of_fibre a hk.ne' G,three_unit_of_fibre a hk.ne' G,
    (single_iff_represented (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) hk short (class_nonsquare a) out).mp G⟩

def SectionResidual : Prop := ∀ b θ:ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) θ →
  (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) θ t) → ¬CancelledFactors b θ →
  ∃ s:ℚ, 0<s ∧ s^2<θ ∧ AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧ represented b (s^2/θ)

theorem residual_iff_sections : RegularResidual ↔ SectionResidual := by
  constructor
  · intro R b θ a i f norm factors bound missed _
    obtain ⟨s,pos,short,allowed,v,G⟩:=R b θ a i f norm factors bound missed
    exact ⟨s,pos,short,allowed,v,(regular_iff_section a pos short bound).mp G⟩
  · intro R b θ a i f norm factors bound missed
    by_cases hit:CancelledFactors b θ
    · obtain ⟨s,pos,short,allowed,v,H⟩:=reduced_ratio a bound
        (surface_of_old a.1 a.2.1 (realized_of_cancelled a.1 a.2.1 hit))
      exact ⟨s,pos,short,allowed,v,(regular_iff_section a pos short bound).mpr H⟩
    · obtain ⟨s,pos,short,allowed,v,H⟩:=R b θ a i f norm factors bound missed hit
      exact ⟨s,pos,short,allowed,v,(regular_iff_section a pos short bound).mpr H⟩

end
end Sun28.GlobalSections

#print axioms Sun28.GlobalSections.regular_iff_section
#print axioms Sun28.GlobalSections.reduced_ratio
#print axioms Sun28.GlobalSections.residual_iff_sections
