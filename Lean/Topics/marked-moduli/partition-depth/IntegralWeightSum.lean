import PartitionOrders
import BranchI4Sum
import DirectCharts
import Mathlib.Algebra.MvPolynomial.Funext

/-! The quartic identity for the sum of the ten weights over an arbitrary coefficient ring. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial
noncomputable section
set_option maxHeartbeats 2500000
variable {R S : Type*} [CommRing R] [CommRing S]

private def quart (a b c d e g h : R) : R :=
  1620*a^2*h^2 - 540*a*b*g*h - 504*a*c*e*h + 300*a*c*g^2 +
  324*a*d^2*h - 180*a*d*e*g + 48*a*e^3 + 300*b^2*e*h - 80*b^2*g^2 -
  180*b*c*d*h + 4*b*c*e*g + 36*b*d^2*g - 12*b*d*e^2 + 48*c^3*h -
  12*c^2*d*g + 4*c^2*e^2

private def invariant (f : R[X]) := quart (f.coeff 0) (f.coeff 1) (f.coeff 2)
  (f.coeff 3) (f.coeff 4) (f.coeff 5) (f.coeff 6)

private def linprod (r : Fin 6 → R) : R[X] := ∏ i, (X-C (r i))

private theorem map_invariant (φ : R →+* S) (f : R[X]) :
    φ (invariant f) = invariant (f.map φ) := by
  simp only [invariant,quart,coeff_map,map_sub,map_add,map_mul,map_pow,map_ofNat]

private theorem map_linprod (φ : R →+* S) (r : Fin 6 → R) :
    (linprod r).map φ = linprod (φ ∘ r) := by
  simp [linprod,Polynomial.map_prod,Polynomial.map_sub]

private theorem map_weights (φ : R →+* S) (r : Fin 6 → R) :
    φ (∑ i, weight r i) = ∑ i, weight (φ ∘ r) i := by
  simp [weight,triangle,map_sum]

private theorem complex_sum (r : Fin 6 → ℂ) :
    ∑ i, weight r i = invariant (linprod r) := by
  simp_rw [complex_weight]
  rw [BranchFormula.sum_rowWeights,BranchI4.monic_i4_sum]
  have hc (k : Fin 7) : (linprod r).coeff k = BranchI4.rootsCoeff r k := by
    unfold linprod
    rw [BranchI4.expand_roots]
    change (C (BranchI4.rootsCoeff r 0)+C (BranchI4.rootsCoeff r 1)*X+C (BranchI4.rootsCoeff r 2)*X^2+C (BranchI4.rootsCoeff r 3)*X^3+C (BranchI4.rootsCoeff r 4)*X^4+C (BranchI4.rootsCoeff r 5)*X^5+C (BranchI4.rootsCoeff r 6)*X^6).coeff k = _
    fin_cases k <;> norm_num [coeff_C_mul,coeff_add,coeff_X_pow,coeff_X,coeff_C]
  unfold invariant
  have h (k : ℕ) (hk : k<7) : (linprod r).coeff k = BranchI4.rootsCoeff r k := hc ⟨k,hk⟩
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),h 5 (by decide),h 6 (by decide)]
  rfl

/-- The complex identity has integer coefficients, so evaluation transports it to every ring. -/
theorem integral_weight_sum (r : Fin 6 → R) :
    ∑ i, weight r i = invariant (linprod r) := by
  let Xs : Fin 6 → MvPolynomial (Fin 6) ℤ := MvPolynomial.X
  have identity : ∑ i, weight Xs i = invariant (linprod Xs) := by
    apply MvPolynomial.funext
    intro x
    rw [map_weights,map_invariant,map_linprod]
    let φ := Int.castRingHom ℂ
    apply (Int.cast_injective (α := ℂ))
    change φ _ = φ _
    rw [map_weights,map_invariant,map_linprod]
    exact complex_sum _
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom R) r
  have h := congrArg ψ identity
  rw [map_weights,map_invariant,map_linprod] at h
  have hx : ψ ∘ Xs = r := funext (fun i => MvPolynomial.eval₂Hom_X' _ _ i)
  rwa [hx] at h

private theorem coeff_monic (t : R) (n : ℕ) :
    (DirectCharts.monicSextic t).coeff n =
      (if n=6 then 1 else 0) + (if n=5 then 9-t else 0) +
      (if n=4 then 27-9*t else 0) + (if n=3 then t^2-32*t+27 else 0) +
      (if n=2 then 6*t^2-54*t else 0) + (if n=1 then 12*t^2-36*t else 0) +
      (if n=0 then 8*t^2 else 0) := by
  rw [DirectCharts.monic_coeffs]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C]

/-- The distinguished scale for the two local charts of the paper's sextic. -/
theorem monic_weight_sum (r : Fin 6 → R) (t : R)
    (he : (∏ i, (X-C (r i))) = DirectCharts.monicSextic t) :
    ∑ i, weight r i = -144*t^2*(t^2+27)^2 := by
  rw [integral_weight_sum]
  change invariant (∏ i, (X-C (r i))) = _
  rw [he]
  simp only [invariant,coeff_monic]
  norm_num
  unfold quart
  ring

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.integral_weight_sum
#print axioms ZInQBlueprint.BranchDepth.monic_weight_sum
