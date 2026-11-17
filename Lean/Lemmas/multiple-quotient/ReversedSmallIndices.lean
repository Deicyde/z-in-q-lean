import ActualReciprocalDivision
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

namespace ReciprocalDivision
open EllipticOrbit.Law

private theorem bits_two : bits 2 = .bit0 (.bit1 .zero) := by decide +kernel
private theorem bits_three : bits 3 = .bit1 (.bit1 .zero) := by decide +kernel

theorem quotient_two {R : Type*} [CommRing R] (z : R) :
    quotientPair z 2 = ((1 + z)^2, 4 * (1 - z)) := by
  rw [quotientPair, bits_two]
  apply Prod.ext <;> dsimp [adjacent, double, middle] <;> ring

theorem quotient_three {R : Type*} [CommRing R] (z : R) :
    quotientPair z 3 = ((1 + 6*z - 3*z^2)^2, (3 - 6*z - z^2)^2) := by
  rw [quotientPair, bits_three]
  apply Prod.ext <;> dsimp [adjacent, double, middle] <;> ring

/-- Both entries, with their exact leading normalizations, agree with the
    literal reversed Mathlib division polynomials for doubling. -/
theorem reversed_division_two {K : Type*} [Field K] (D q : K) (hq : q ≠ 0) :
    (quotientPair (D*q^2) 2).1 = q^4 * ((curve D).Φ 2).eval q⁻¹ ∧
    (quotientPair (D*q^2) 2).2 = q^3 * ((curve D).ΨSq 2).eval q⁻¹ := by
  rw [quotient_two, WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two]
  simp [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve]
  constructor <;> field_simp <;> ring

/-- The corresponding literal polynomial identity for tripling. -/
theorem reversed_division_three {K : Type*} [Field K] (D q : K) (hq : q ≠ 0) :
    (quotientPair (D*q^2) 3).1 = q^9 * ((curve D).Φ 3).eval q⁻¹ ∧
    (quotientPair (D*q^2) 3).2 = q^8 * ((curve D).ΨSq 3).eval q⁻¹ := by
  rw [quotient_three, WeierstrassCurve.Φ_three, WeierstrassCurve.ΨSq_three]
  simp [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve]
  constructor <;> field_simp <;> ring

end ReciprocalDivision
