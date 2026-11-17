import Std

namespace CompanionTrace

private def beta : Nat := 412690661369
private def twist : Nat := 66596377080407144678843471

/-- Test the projective slope over the given finite prime field, including zero
as a square and the unique point at infinity when the abscissa is the root n. -/
def slopeTest (p x u : Nat) : Bool :=
  let square := fun (z : Nat) =>
    (List.range p).any fun y => y*y % p == z % p
  let b := beta % p
  let n := twist % p
  if x % p == n then
    square (1 + 3*b*u*u)
  else
    (List.range p).any fun s =>
      (x+p-n)*s*s % p == b*(x+3*n) % p &&
      square ((s*s+3*b)*((s+b*u)^2+3*b*(1+s*u)^2))

/-- The finite lifts use either a normalized finite slope or the slope at infinity. -/
theorem slopeTest_iff (p x u : Nat) :
    slopeTest p x u = true ↔
      if x % p = twist % p then
        ∃ y < p, y*y % p = (1+3*(beta%p)*u*u) % p
      else
        ∃ s < p, (x+p-twist%p)*s*s % p = (beta%p)*(x+3*(twist%p)) % p ∧
          ∃ y < p, y*y % p =
            ((s*s+3*(beta%p))*((s+(beta%p)*u)^2+3*(beta%p)*(1+s*u)^2)) % p := by
  by_cases e : x % p = twist % p <;> simp [slopeTest, e, List.any_eq_true]

/-- Reduced abscissas of the odd multiples of the supplied rational point. -/
private def xAt (m x1 x3 x5 : Nat) : Nat :=
  if m = 1 ∨ m = 9 then x1 else if m = 3 ∨ m = 7 then x3 else x5

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

theorem admissible31 :
    [1,3,5,7,9].filter (fun m => slopeTest 31 (xAt m 16 1 0) 20) = [3,5,7] := by
  decide +kernel

theorem admissible953 :
    [1,3,5,7,9].filter (fun m => slopeTest 953 (xAt m 22 107 125) 496) = [1,9] := by
  decide +kernel

/-- The two necessary local conditions are incompatible for a common odd multiplier. -/
theorem no_common_multiplier (m : Nat) (odd : m % 2 = 1)
    (at31 : slopeTest 31 (xAt (m%10) 16 1 0) 20 = true)
    (at953 : slopeTest 953 (xAt (m%10) 22 107 125) 496 = true) : False := by
  have h : m%10 ∈ [1,3,5,7,9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h31 : m%10 ∈ [1,3,5,7,9].filter (fun i => slopeTest 31 (xAt i 16 1 0) 20) :=
    List.mem_filter.mpr ⟨h, at31⟩
  have h953 : m%10 ∈ [1,3,5,7,9].filter (fun i => slopeTest 953 (xAt i 22 107 125) 496) :=
    List.mem_filter.mpr ⟨h, at953⟩
  rw [admissible31] at h31
  rw [admissible953] at h953
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h31 h953
  omega

#print axioms CompanionTrace.slopeTest_iff
#print axioms CompanionTrace.admissible31
#print axioms CompanionTrace.admissible953
#print axioms CompanionTrace.no_common_multiplier
end CompanionTrace
