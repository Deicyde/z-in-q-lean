import Contact84
import PhysicalHeight

namespace StructuralReduction.Transfer84
open IndependentIndices IndependentIndices.Assembly WitnessTransfer.Height

/-- Each listed prime is a good contact with its own evaluated conjugate elliptic charts. -/
def EvaluatedContacts (x : Fin 84 → Rat) (m n : Int) (ps : List Nat) : Prop :=
  ∀ p ∈ ps, StructuralHeights.Prime p ∧ ¬ (p : Int) ∣ 210 ∧
    StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label (cell x 1))) ∧
    HasLocalScalarCharts p x m n

private theorem coprime_six_of_good {p : Nat} (hp : StructuralHeights.Prime p)
    (good : ¬ (p : Int) ∣ 210) : Nat.Coprime 6 p := by
  rcases hp.2 _ (Nat.gcd_dvd_right 6 p) with h | h
  · exact h
  · have dvd : p ∣ 6 := h ▸ Nat.gcd_dvd_left 6 p
    exact False.elim (good (Int.natCast_dvd_natCast.mpr (Nat.dvd_trans dvd (by decide : 6 ∣ 210))))

/-- The seventeenth power of the radical of any list of evaluated contacts divides n−1. -/
theorem radical_divisor84 (marked : Bool) (x : Fin 84 → Rat)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0)
    (m n : Int) (ps : List Nat) (contacts : EvaluatedContacts x m n ps) :
    ((radical ps ^ 17 : Nat) : Int) ∣ n-1 := by
  apply aggregate 17 (n-1) ps
  intro p member
  obtain ⟨prime,good,hit,charts⟩ := contacts p member
  exact scalar_divisor_at_contact84 marked x active zero m n prime good hit charts

/-- Height and group data for an input with the indicated root labels. The scalar list
may be empty or have repetitions. Its height estimate is required for this very list. -/
structure HeightData84 (x : Fin 84 → Rat) where
  labels : Labels
  first : Observed labels (SquareGate.label (cell x 1))
  second : Observed labels (SquareGate.label (cell x 1))
  third : Observed labels (SquareGate.label (cell x 1))
  scalarMultiplier : Int
  primes : List Nat
  contacts : EvaluatedContacts x scalarMultiplier labels.n₂ primes
  scalarHeight : multiplicativeHeight (SquareGate.label (cell x 1)) ≤
    2^(2*scalarConstant*(radical primes)^17)
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  anchorNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int) ∣ labels.n₂-1
  abscissas : 2*(labelSize labels)^2 ≤ 15+3*largest first.slopeCeiling second.slopeCeiling third.slopeCeiling

/-- The disclosed height and geometry inputs imply integrality for the literal ordinary
and marked outputs. The three fixed rank-zero curves are unnecessary for this implication. -/
theorem integer_of_zero84 (marked : Bool) (x : Fin 84 → Rat) (zero : output marked x=0)
    (geometry : cell x 1≠0 → Nonempty (HeightData84 x)) : InputRestriction.IsInteger (cell x 1) := by
  by_cases inputZero : cell x 1=0
  · exact ⟨0,by simpa using inputZero⟩
  obtain ⟨h⟩ := geometry inputZero
  let scalar : ScalarContacts (cell x 1) h.labels.n₂ := {
    primes := h.primes
    away := fun p member => coprime_six_of_good (h.contacts p member).1 (h.contacts p member).2.1
    atPrime := by
      intro p member
      obtain ⟨prime,good,hit,charts⟩ := h.contacts p member
      exact scalar_divisor_at_contact84 marked x (fun _ => inputZero) zero h.scalarMultiplier
        h.labels.n₂ prime good hit charts
    fiveMark := h.scalarHeight
  }
  exact (integral_from_observations (cell x 1) h.labels h.first h.second h.third scalar
    h.oddFirst h.lastNonzero h.anchorNonzero h.anchor h.abscissas).2.2

#print axioms radical_divisor84
#print axioms integer_of_zero84
end StructuralReduction.Transfer84
