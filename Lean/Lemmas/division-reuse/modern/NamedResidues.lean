module

public import MarkedNamed
public import AnchorResidues

@[expose] public section

namespace MarkedNamed
open EllipticOrbit.Field
open Prime23 (PairRed scale)

/-- Evaluation at the actual abscissa (57 − 28 √2)/8. -/
noncomputable def value (n : ℤ) : K :=
  (E.ΨSq n).eval (ofPair (57/8,-7/2)) / (E.Φ n).eval (ofPair (57/8,-7/2))

private theorem same_reciprocal (S : Point) :
    MarkedNamed.reciprocal E S=ReciprocalDivision.reciprocal (D:=D) S := by
  cases S <;> simp [MarkedNamed.reciprocal, ReciprocalDivision.reciprocal,
    EllipticOrbit.Law.abscissa, one_div]

theorem value_eq (n : ℤ) : value n=ReciprocalDivision.reciprocal (D:=D) (n • P) :=
  (physical_named n).symm.trans (same_reciprocal _)

/-- The coefficients reduce in the order with basis 1,√2, including the ramified prime. -/
theorem named_residues (n : ℤ) (hn : n ≠ 0) :
    PairRed 2 (scale (8*(n:ℚ)^2)⁻¹ (coeffs (value n))) (1,0) ∧
    PairRed 3 (scale (9*(n:ℚ)^2)⁻¹ (coeffs (value (2*n)))) (0,1) := by
  simpa only [value_eq, Prime23.Actual.orbit] using Prime23.Actual.actual_residues n hn

/-- Both normalized canonical division quotients are coefficientwise principal units. -/
theorem named_quotient_residues (n : ℤ) (hn : n ≠ 0) :
    PairRed 2 (coeffs (value n / ((n:K)^2 * value 1))) (1,0) ∧
    PairRed 3 (coeffs (value (2*n) / ((n:K)^2 * value 2))) (1,0) := by
  have baseOne : value 1=ReciprocalDivision.reciprocal (D:=D) P := by rw [value_eq, one_zsmul]
  have baseTwo : value 2=ReciprocalDivision.reciprocal (D:=D) ((2:ℕ) • P) := by
    have eq : (2:ℤ) • P=(2:ℕ) • P := rfl
    exact (value_eq 2).trans (congrArg (ReciprocalDivision.reciprocal (D:=D)) eq)
  rw [baseOne, baseTwo, value_eq, value_eq]
  exact Prime23.Actual.actual_quotient_residues n hn

/-- Both named evaluations are nonzero separately at each nonzero signed multiple. -/
theorem evaluations_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (E.ΨSq n).eval (ofPair (57/8,-7/2)) ≠ 0 ∧
    (E.Φ n).eval (ofPair (57/8,-7/2)) ≠ 0 := by
  have nz := (((named_residues n hn).1.1).invOne (by decide)).1
  have live : value n ≠ 0 := by
    intro h
    apply nz
    simp [scale, coeffs, h]
  constructor <;> intro h <;> exact live (by simp [value, h])

theorem value_zero : value 0 = 0 := by
  simp [value]

#print axioms evaluations_ne_zero
#print axioms value_zero
#print axioms value_eq
#print axioms named_residues
#print axioms named_quotient_residues
end MarkedNamed
