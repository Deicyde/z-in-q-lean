import Std

namespace ScalarPrimes
open Lean.Grind Std

section FormalIdentities
variable {R : Type} [CommRing R]

/-- The prime-selection polynomial supplies a fourth root modulo its divisors. -/
theorem fourth_root (c m : R) : (c*m)^4-c = c*(c^3*m^4-1) := by grobner

/-- Changing one digit gives the linear term used to prescribe the next residue. -/
theorem lift_digit (t p x : R) :
    (t+p*x)^4-t^4-4*t^3*p*x = p^2*x^2*(6*t^2+4*t*p*x+p^2*x^2) := by grobner

/-- The derivative of the scalar has no additional zero at a nonzero quartic root. -/
theorem adjacent_numerator (c k l t : R) (ratio : k=t*l) :
    c*l^4-k^4 = l^4*(c-t^4) := by rw [ratio]; grobner
end FormalIdentities

private theorem diff_bound (x y cap : Nat) (hx : x ≤ cap) (hy : y ≤ cap) :
    ((x : Int) - (y : Int)).natAbs ≤ cap := by
  by_cases h : (y : Int) ≤ x
  · have eq := Int.natAbs_of_nonneg (a := (x : Int)-y) (by omega)
    omega
  · have eq := Int.natAbs_of_nonneg (a := -((x : Int)-y)) (by omega)
    rw [Int.natAbs_neg] at eq
    omega

/-- Coordinates are their absolute values. A forced nonzero quadratic factor
    divisible by p bounds the projective height in the original chart. -/
theorem slope_height (p β a b H : Nat) (pos : 1 ≤ β) (ha : a ≤ H) (hb : b ≤ H)
    (nonzero : ((b^2 : Nat) : Int) - ((β*a^2 : Nat) : Int) ≠ 0)
    (divides : (p : Int) ∣ ((b^2 : Nat) : Int) - ((β*a^2 : Nat) : Int)) :
    p ≤ β*H^2 := by
  have lower := Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) (Int.ofNat_dvd_left.mp divides)
  have bound : H^2 ≤ β*H^2 := by
    simpa using Nat.mul_le_mul_right (H^2) pos
  have upper := diff_bound (b^2) (β*a^2) (β*H^2)
      (Nat.le_trans (Nat.pow_le_pow_left hb 2) bound)
      (Nat.mul_le_mul_left β (Nat.pow_le_pow_left ha 2))
  exact Nat.le_trans lower upper

/-- The numerical exclusion holds through the largest integral height allowed
    by this single prime. -/
theorem exact_cutoff :
    412690661369 * 13050329281404375598463818262952944^2 < 607 * 2^256+1 ∧
    607 * 2^256+1 ≤ 412690661369 * (13050329281404375598463818262952944+1)^2 := by
  decide

def squaresMod (m x : Nat) : Nat → Nat
  | 0 => x % m
  | n+1 => let y := squaresMod m x n; (y*y) % m

theorem squaresMod_spec (m x n : Nat) : squaresMod m x n = x^(2^n) % m := by
  induction n with
  | zero => simp [squaresMod]
  | succ n ih =>
    rw [squaresMod, ih, Nat.pow_succ 2 n, Nat.pow_mul, Nat.pow_two]
    exact (Nat.mul_mod _ _ _).symm

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 32768 in
/-- The modular-power certificate, evaluated by the proved repeated-squaring rule. -/
theorem proth_residue :
    squaresMod (607*2^256+1) (3^607) 255 = 607*2^256 := by decide

end ScalarPrimes
#print axioms ScalarPrimes.fourth_root
#print axioms ScalarPrimes.lift_digit
#print axioms ScalarPrimes.adjacent_numerator
#print axioms ScalarPrimes.slope_height
#print axioms ScalarPrimes.exact_cutoff
#print axioms ScalarPrimes.squaresMod_spec
#print axioms ScalarPrimes.proth_residue
