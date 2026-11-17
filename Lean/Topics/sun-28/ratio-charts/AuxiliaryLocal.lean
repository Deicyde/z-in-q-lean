import QuarticHensel
import AuxiliaryPrime
import ConductorProjection28

namespace Sun28.LocalQuartics
open Sun28.PairedClasses Sun28.PreparedPoles

/-- Reduction of one of the given square towers at its first level. -/
theorem residue_of_tower {p a : ℕ} (tower : LocalSquareAt p a) : IsSquare (a:ZMod p) := by
  obtain ⟨x,h⟩ := tower 1
  rw [pow_one] at h
  have e := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h
  exact ⟨x,by simpa [sq] using e.symm⟩

theorem fresh_progression {b θ : ℕ} (bp : 0<b) (tp : 0<θ) (bound : ℕ) :
    ∃ q > max bound (max b θ), q.Prime ∧ q≡1 [MOD 24*b*θ] :=
  Nat.forall_exists_prime_gt_and_modEq _ (by positivity) (by simp)

/-- At the newly introduced prime, the two quartics have the same branch point. -/
theorem square_at_auxiliary {b θ q : ℕ} (bp : 1<b) (bt : b%24=17)
    (pr : q.Prime) (big : b<q) (prog : q≡1 [MOD 24*b*θ]) : IsSquare (b:ZMod q) := by
  let : Fact q.Prime := ⟨pr⟩
  have mod4 : q≡1 [MOD 4] := prog.of_dvd ⟨6*b*θ,by ring⟩
  have modb : q≡1 [MOD b] := prog.of_dvd ⟨24*θ,by ring⟩
  have q4 : q%4=1 := mod4
  have bo : Odd b := Nat.odd_iff.mpr (by omega)
  have jb := jacobiSym.quadratic_reciprocity_one_mod_four (a:=q) q4 bo
  have bq : (b:ZMod q)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) big)
  apply (legendreSym.eq_one_iff' q bq).mp
  rw [jacobiSym.legendreSym.to_jacobiSym,←jb,jacobiSym.mod_left]
  have one : (q:ℤ)%b=1 := by
    have v : q%b=1 := (show q%b=1%b from modb).trans (Nat.mod_eq_of_lt bp)
    exact_mod_cast v
  rw [one,jacobiSym.one_left]

end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.residue_of_tower
#print axioms Sun28.LocalQuartics.fresh_progression
#print axioms Sun28.LocalQuartics.square_at_auxiliary
