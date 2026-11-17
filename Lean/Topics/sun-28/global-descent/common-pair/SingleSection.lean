import TwiceSigned
import SwappedQuartic

/-! The standard section and its eight translations give precisely the old single-quartic case. -/
namespace Sun28.CommonPair
open Sun28.PairedClasses Sun28.PrescribedPoints Sun28.PointFibres Sun28.PreparedPoles
  Sun28.GlobalDescent Sun28.GlobalSections Sun28.TwistRank Sun28.TwistExtension Sun28.PointLifts
open private admissible_nonsquare from OrbitResidual
noncomputable section

theorem square_second {b d:ℚ} (sq:IsSquare d) : OneQuartic b d := by
  obtain ⟨y,eq⟩:=sq
  exact ⟨1,0,y,Or.inl (by simpa [quartic,pow_two] using eq)⟩

theorem section_iff_original {b d:ℕ} (a:AdmissiblePair b d) (ns:¬IsSquare (d:ℚ)) :
    SectionHit b d ↔ OneQuartic (b:ℚ) d :=
  (section_iff_transposed a).trans
    (one_symmetry (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) (admissible_nonsquare a) ns).symm

/-- On a residual input no physical ratio can realize one of the eight known classes. -/
theorem orbit_excluded {b d:ℕ} (a:AdmissiblePair b d) (out:¬OneQuartic (b:ℚ) d)
    {s:ℚ} (pos:0<s) (short:s^2<d) (unit:padicValRat 3 s=0) :
    ¬KnownOrbit (s^2/d) (b*lead (s^2/d)) := by
  have ds:¬IsSquare (d:ℚ) := fun h=>out (square_second h)
  exact fun h=>out ((section_iff_original a ds).mp (hit_of_orbit a pos short unit h))

/-- A single quartic suffices, with the exceptional eight elliptic classes already ruled out. -/
theorem sections_outside_orbit :
    SectionResidual ↔ ∀ b d:ℕ, AdmissiblePair b d → InputClass b → FixedSquares d →
      NormConic b d → ¬FactorPair b d → ¬OneQuartic (b:ℚ) d →
      (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) d t) → ¬CancelledFactors b d →
      ∃ s:ℚ, 0<s ∧ s^2<d ∧ AllowedRatio b d s ∧ padicValRat 3 s=0 ∧
        ¬KnownOrbit (s^2/d) (b*lead (s^2/d)) ∧ represented b (s^2/d) := by
  constructor
  · intro H b d a inp fixed norm factor out ratio cancel
    obtain ⟨s,pos,short,allowed,v,rep⟩:=H b d a inp fixed norm factor out ratio cancel
    exact ⟨s,pos,short,allowed,v,orbit_excluded a out pos short v,rep⟩
  · intro H b d a inp fixed norm factor out ratio cancel
    obtain ⟨s,pos,short,allowed,v,_,rep⟩:=H b d a inp fixed norm factor out ratio cancel
    exact ⟨s,pos,short,allowed,v,rep⟩

end
end Sun28.CommonPair
#print axioms Sun28.CommonPair.square_second
#print axioms Sun28.CommonPair.section_iff_original
#print axioms Sun28.CommonPair.orbit_excluded
#print axioms Sun28.CommonPair.sections_outside_orbit
