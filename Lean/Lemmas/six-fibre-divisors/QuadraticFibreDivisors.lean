import ProjectiveFibreFunctions
import Nyll.AlgebraicCurves.Divisors.Norm.SumGaloisSmulEqPullbackPushforward
import Nyll.AlgebraicCurves.Divisors.Principal.HasPrincipalDivisorsFiniteDimensionalRatFunc
import Nyll.AlgebraicCurves.Places.Degree.DegEqOneAlgClosed
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegEqOneAlgClosed
import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegPosFiniteDimensional
import Mathlib.FieldTheory.Galois.Basic

/-! Every pair of fibres of a quadratic rational function on a smooth projective curve
over an algebraically closed field is linearly equivalent. The principal function is explicit. -/
namespace ZInQBlueprint.FibreDivisors

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
noncomputable section
open Classical

variable {K E : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field E]
variable [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]

def deck (s : E ≃ₐ[RatFunc K] E) : SemilinearAut K E := SemilinearAut.ofAlgAut (s.restrictScalars K)

def orbitDivisor (s : E ≃ₐ[RatFunc K] E) (P : Place K E) : Divisor K E :=
  pointDivisor P + pointDivisor (deck s • P)

omit [CharZero K] in
theorem inertia_one (P : Place K E) : P.inertiaDeg (RatFunc K) = 1 := by
  have hb := RationalFunctionField.deg_eq_one_of_isAlgClosed K (P.restrict (RatFunc K))
  have hm := P.deg_restrict_mul_inertiaDeg (F := RatFunc K)
  rw [hb, one_mul] at hm
  have hp := Place.inertiaDeg_pos_of_finiteDimensional (F := RatFunc K) P
  exact hm.trans (Place.deg_eq_one_of_isAlgClosed P (by omega))

local instance : HasPrincipalDivisors K E := hasPrincipalDivisors_of_finiteDimensional_ratFunc K E

variable [IsGalois (RatFunc K) E]

theorem orbit_eq_pullback (d : Module.finrank (RatFunc K) E = 2)
    (s : E ≃ₐ[RatFunc K] E) (hs : s ≠ 1) (P : Place K E) :
    orbitDivisor s P = Divisor.pullback E (pointDivisor (P.restrict (RatFunc K))) := by
  classical
  have he : (Finset.univ : Finset (E ≃ₐ[RatFunc K] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs.symm, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, d]
  have ho : deck (1 : E ≃ₐ[RatFunc K] E) = 1 := by
    unfold deck
    rw [← map_one (SemilinearAut.ofAlgAut (K := K) (F := E))]
    congr 1
  have H := Divisor.sum_galois_smul_eq_pullback_pushforward (F := RatFunc K) (pointDivisor P)
  change (∑ t : E ≃ₐ[RatFunc K] E, deck t • pointDivisor P) = _ at H
  rw [he, Finset.sum_pair hs.symm, ho, one_smul] at H
  simpa [pointDivisor, orbitDivisor, inertia_one] using H

theorem orbit_difference_order (d : Module.finrank (RatFunc K) E = 2)
    (s : E ≃ₐ[RatFunc K] E) (hs : s ≠ 1) (P Q : Place K E) (w : Place K E) :
    (orbitDivisor s P - orbitDivisor s Q) w = w.ord (algebraMap (RatFunc K) E
      (quotient (placeEquivOption K (P.restrict (RatFunc K)))
        (placeEquivOption K (Q.restrict (RatFunc K))))) := by
  classical
  rw [orbit_eq_pullback d s hs P, orbit_eq_pullback d s hs Q, ← map_sub]
  apply Divisor.pullback_apply_eq_ord
  intro v
  have h := quotient_order (placeEquivOption K (P.restrict (RatFunc K)))
    (placeEquivOption K (Q.restrict (RatFunc K))) v
  have hi (v : Place K (RatFunc K)) : ofOption K (placeEquivOption K v) = v :=
    (placeEquivOption K).symm_apply_apply v
  simpa only [hi] using h

theorem orbit_difference_principal (d : Module.finrank (RatFunc K) E = 2)
    (s : E ≃ₐ[RatFunc K] E) (hs : s ≠ 1) (P Q : Place K E) :
    (orbitDivisor s P - orbitDivisor s Q).IsPrincipal :=
  ⟨_, (map_ne_zero (algebraMap (RatFunc K) E)).mpr (quotient_ne_zero _ _),
    orbit_difference_order d s hs P Q⟩

end
end ZInQBlueprint.FibreDivisors

#print axioms ZInQBlueprint.FibreDivisors.inertia_one
#print axioms ZInQBlueprint.FibreDivisors.orbit_eq_pullback
#print axioms ZInQBlueprint.FibreDivisors.orbit_difference_order
#print axioms ZInQBlueprint.FibreDivisors.orbit_difference_principal

