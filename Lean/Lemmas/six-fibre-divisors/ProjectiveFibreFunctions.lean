import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.FiniteOrder
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Mathlib.Algebra.Polynomial.RingDivision

/-! The rational function cutting out the difference of two projective points. -/
namespace ZInQBlueprint.FibreDivisors

open AlgebraicCurve AlgebraicCurve.RationalFunctionField Polynomial
noncomputable section
open Classical

variable {K : Type*} [Field K]

def factor : Option K → RatFunc K
  | none => 1
  | some a => algebraMap K[X] (RatFunc K) (X - C a)

theorem factor_ne_zero (a : Option K) : factor a ≠ 0 := by
  cases a with
  | none => exact one_ne_zero
  | some a => exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

def quotient (a b : Option K) : RatFunc K := factor a / factor b

theorem quotient_ne_zero (a b : Option K) : quotient a b ≠ 0 :=
  div_ne_zero (factor_ne_zero a) (factor_ne_zero b)

abbrev pointDivisor {F : Type*} [Field F] [Algebra K F] (v : Place K F) : Divisor K F :=
  Finsupp.single v 1

variable [IsAlgClosed K]

theorem factor_order (a : Option K) (v : Place K (RatFunc K)) :
    v.ord (factor a) =
      (pointDivisor (ofOption K a) - pointDivisor (placeInfty K)) v := by
  classical
  cases a with
  | none => simp [factor, ofOption, Place.ord_one]
  | some a =>
    rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨c, rfl⟩ | rfl
    · rw [factor, ord_placeOfPoint_algebraMap c (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C]
      by_cases h : c = a
      · subst c
        simp [ofOption, pointDivisor, placeOfPoint_ne_placeInfty, Ne.symm (placeOfPoint_ne_placeInfty K a)]
      · have hd : placeOfPoint K c ≠ placeOfPoint K a := fun e => h (placeOfPoint_injective K e)
        simp [ofOption, pointDivisor, h, hd, Ne.symm hd, Ne.symm (placeOfPoint_ne_placeInfty K c)]
    · rw [factor, ord_placeInfty_algebraMap (X_sub_C_ne_zero a)]
      simp [ofOption, pointDivisor, placeOfPoint_ne_placeInfty, Ne.symm (placeOfPoint_ne_placeInfty K a)]

theorem quotient_order (a b : Option K) (v : Place K (RatFunc K)) :
    (pointDivisor (ofOption K a) - pointDivisor (ofOption K b)) v = v.ord (quotient a b) := by
  rw [quotient, div_eq_mul_inv, v.ord_mul (factor_ne_zero a) (inv_ne_zero (factor_ne_zero b)),
    v.ord_inv, factor_order, factor_order]
  simp only [Finsupp.sub_apply]
  omega

end
end ZInQBlueprint.FibreDivisors

#print axioms ZInQBlueprint.FibreDivisors.factor_order
#print axioms ZInQBlueprint.FibreDivisors.quotient_order

