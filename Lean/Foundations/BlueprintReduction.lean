import Std

namespace BlueprintReduction

/-- The two reference indices differ by a unit in the residue ring.
Neither h nor h−c needs an inverse for this last subtraction. -/
theorem shifted_residue {R : Type} [Lean.Grind.CommRing R]
    (h u n l l' c inv : R) (unit : c * inv = 1) (eq : l = l')
    (first : h * l = u) (second : (h-c)*l' = u-c*n) : l = n := by
  subst l'
  have cancel : c*(l-n) = 0 := by grobner
  have cleared : (c*(l-n))*inv = 0 := by rw [cancel]; grind
  grobner

private theorem small_multiple {x : Int} {k : Nat}
    (h : (k : Int) ∣ x) (bound : x.natAbs < k) : x = 0 := by
  by_cases hx : x = 0
  · exact hx
  · have lower := Nat.le_of_dvd (Int.natAbs_pos.mpr hx) (Int.ofNat_dvd_left.mp h)
    omega

/-- The second size estimate is needed only after the Lucas error vanishes. -/
theorem successive_separation (M : Nat) (lucas numerator : Int)
    (dl : ((M^52 : Nat) : Int) ∣ lucas) (dn : ((M^16 : Nat) : Int) ∣ numerator)
    (bl : lucas.natAbs < M^52)
    (bn : lucas = 0 → numerator.natAbs < M^16) :
    lucas = 0 ∧ numerator = 0 := by
  have hl := small_multiple dl bl
  exact ⟨hl, small_multiple dn (bn hl)⟩

#print axioms shifted_residue
#print axioms successive_separation
end BlueprintReduction
