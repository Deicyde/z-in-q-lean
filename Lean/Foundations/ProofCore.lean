import Std

/- The arithmetic at the two ends of the ordinary-value proof.
   The global height estimate, pole existence and model are separate inputs. -/
namespace ProofCore

/-- At an odd contact, 1-rq² has valuation at most zero
    when q is nonzero. Its two terms have distinct valuations. -/
theorem shrink_at_contact (d v : Int) (hd : d % 2 = 1) :
    d + 2 * v ≠ 0 ∧ min 0 (d + 2 * v) ≤ 0 := by
  constructor
  · omega
  · exact Int.min_le_left _ _

/-- If v(D)≤0, the second term of 1+a²D²/r has strictly negative
    valuation. The displayed result is then the valuation of the pole input. -/
theorem bad_local_value (d b s : Int) (hd : 0 < d) (hb : b ≤ 0) (hs : s ≤ 0) :
    2*b + 2*s - d < 0 ∧
    d + 2*b + 2*min 0 (2*b + 2*s - d) = 6*b + 4*s - d ∧
    6*b + 4*s - d < 0 ∧ (6*b + 4*s - d) % 2 = d % 2 := by
  have h : 2*b + 2*s - d ≤ 0 := by omega
  rw [Int.min_eq_right h]
  omega

/-- The valuation a pole witness must exclude. In the good case the
    valuation of 1+a²D²/r can jump if its two terms have equal valuation. -/
theorem contact_forces_divisor (d b s pole : Int)
    (hd : 0 < d) (hodd : d % 2 = 1) (hb : b ≤ 0)
    (badCase : s ≤ 0 → pole = d + 2*b + 2*min 0 (2*b + 2*s - d))
    (accepted : ¬ (pole < 0 ∧ pole % 2 = 1)) : 0 < s := by
  apply Classical.byContradiction
  intro contrary
  have hs : s ≤ 0 := by omega
  obtain ⟨_, heq, hneg, hparity⟩ := bad_local_value d b s hd hb hs
  have h := badCase hs
  exact accepted (by omega)

/-- Combine the two finite Taylor remainders without dividing by the possibly nonunit r. -/
theorem jetCancellation {R : Type} [Lean.Grind.CommRing R] (r s a l h u eH eU power : R)
    (hh : h = r*l + power*eH) (hu : u = s*l + power*eU)
    (eqn : u = a*h) :
    (s-r*a)*l = power*(a*eH-eU) := by
  grind

/-- A fraction with positive denominator. The separation proof even works
    with an unreduced presentation when that denominator has the asserted bound. -/
structure Fraction where
  num : Int
  den : Nat
  den_pos : 0 < den

def HasValue (q : Fraction) (n : Int) : Prop := q.num = n * (q.den : Int)

/-- Cross multiplication of |q - n| < 1 / K for positive K. -/
def Near (q : Fraction) (n : Int) (K : Nat) : Prop :=
  (q.num - n * (q.den : Int)).natAbs * K < q.den

theorem isolate (q : Fraction) (n : Int) (K : Nat) (bound : q.den ≤ K)
    (close : Near q n K) : HasValue q n := by
  change (q.num - n * (q.den : Int)).natAbs * K < q.den at close
  change q.num = n * (q.den : Int)
  apply Classical.byContradiction
  intro contrary
  have nonzero : q.num - n * (q.den : Int) ≠ 0 := by omega
  have positive : 1 ≤ (q.num - n * (q.den : Int)).natAbs := Int.natAbs_pos.mpr nonzero
  have lower := Nat.mul_le_mul_right K positive
  rw [Nat.one_mul] at lower
  omega

/-- Both directions of assembly. In the application j is an elliptic label,
    slice is the pole condition, and window is the coded pair of rational endpoints. -/
theorem value_graph {Label : Type} (K : Label → Nat)
    (slice : Label → Fraction → Prop) (window : Int → Label → Fraction → Prop)
    (bounded : ∀ j q, slice j q → q.den ≤ K j)
    (covers : ∀ q n, HasValue q n → ∃ j, slice j q)
    (narrow : ∀ n j q, window n j q → Near q n (K j))
    (center : ∀ n j q, HasValue q n → window n j q)
    (q : Fraction) (n : Int) :
    (∃ j, slice j q ∧ window n j q) ↔ HasValue q n := by
  constructor
  · rintro ⟨j, hs, hw⟩
    exact isolate q n (K j) (bounded j q hs) (narrow n j q hw)
  · intro h
    obtain ⟨j, hs⟩ := covers q n h
    exact ⟨j, hs, center n j q h⟩

end ProofCore

#print axioms ProofCore.contact_forces_divisor
#print axioms ProofCore.jetCancellation
#print axioms ProofCore.value_graph
