module

public import Std

@[expose] public section

namespace CommonIndex
open Lean.Grind

/-- The only squared positive denominator dividing the coefficient of the gate. -/
theorem square_denom (d : Nat) (divides : d^2 ∣ 510) : d = 1 := by
  have bound := Nat.le_of_dvd (by decide : 0 < 510) divides
  have small : d < 23 := by
    by_cases h : d < 23
    · exact h
    · have h' : 23 ≤ d := by omega
      have bad : 23^2 ≤ d^2 := Nat.pow_le_pow_left h' 2
      omega
  have tab : ∀ i : Fin 23, i.val^2 ∣ 510 → i.val = 1 := by decide
  exact tab ⟨d, small⟩ divides

/-- The endpoint of soundness on the canonical rational input. -/
theorem integer_of_gate {x : Rat} {n : Int}
    (label : 2401+510*x^2 = (n : Rat)) : ∃ z : Int, x = (z : Rat) := by
  have h : x^2 = mkRat (n-2401) 510 := by
    rw [Rat.mkRat_eq_div, Rat.intCast_sub]
    change x^2 = ((n : Rat)-2401) / 510
    have prod : x^2 * 510 = (n : Rat)-2401 := by grobner
    rw [← prod, Rat.mul_div_cancel (by decide : (510 : Rat) ≠ 0)]
  have hd := congrArg Rat.den h
  simp only [Rat.den_pow, Rat.den_mkRat, if_neg (by decide : (510 : Nat) ≠ 0)] at hd
  have div : x.den^2 ∣ 510 :=
    ⟨Nat.gcd 510 (n-2401).natAbs, by
      rw [hd, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]⟩
  exact ⟨x.num, Rat.ext rfl (square_denom _ div)⟩

/-- The product of two marked factors in the stored coordinate b(b-1). -/
theorem four_factors {R : Type} [CommRing R] (b : R) :
    (b-2401)*(32*b+343) = 32*b*(b-1)-76457*b-823543 := by grobner

/-- Cubic residual for the reweighted scalar fifth power. -/
theorem fifth_power {R : Type} [CommRing R] (r k : R) :
    let z := r^2*(r+k)
    z*r^2-k*z*r+k^2*z-k^3*r^2 = r^5 := by dsimp; grobner

/-- Removing both copies of an even intersection preserves divisibility by four. -/
theorem branch_parity (a b i n : Int) (ha : a % 4 = 0) (hb : b % 4 = 0)
    (hi : i % 2 = 0) (hn : n % 2 = 1) :
    a + b - 2*i ≠ 2*n := by omega

/-- The two candidate valuations at a place of odd first valuation are distinct. -/
theorem separated_valuations (u v r : Int) (h : r % 2 = 1) : 2*u ≠ r+2*v := by omega

theorem lower_gap {R : Type} [CommRing R] (c : R) :
    (3*c+1)*(c+3)-3*(c-1)^2 = 16*c := by grobner

end CommonIndex

#print axioms CommonIndex.square_denom
#print axioms CommonIndex.integer_of_gate
#print axioms CommonIndex.four_factors
#print axioms CommonIndex.fifth_power
#print axioms CommonIndex.branch_parity
#print axioms CommonIndex.separated_valuations
#print axioms CommonIndex.lower_gap
