import PositiveRootHeight
import IntegerRootBound
import ArchimedeanTriple

namespace HeightSpecialization
open Lean.Grind Std StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.HeightSupport
open ProjectionFibres.Comparison IndependentIndices IndependentIndices.Assembly WitnessTransfer.Height
attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]
variable {l : Analytic.LogLaw K}

/-- The elementary integer index test follows from the logarithmic lower estimate. -/
theorem index_height_of_log {x : Fin 84→Rat} {ns : Labels}
    (laws : Analytic.BinaryLogLaw l) (mult : Analytic.ProductLogLaw l)
    (lower : (((labelSize ns)^2:Nat):K)≤6+l.log ((J x:Nat):K)) : IndexHeight x ns := by
  let j:=J x
  have jp : 0<j := Nat.lt_of_lt_of_le (Nat.lcm_pos (atWire x 1249).den_pos (atWire x 1252).den_pos) (Nat.le_max_left ..)
  have jo : (1:K)≤(j:K) := by
    simpa only [Semiring.natCast_one] using OrderedRing.natCast_le_natCast_of_le (R:=K) 1 j jp
  have jlog:=l.monotone OrderedRing.zero_lt_one jo
  have one:=l.power (x:=(1:K)) OrderedRing.zero_lt_one 0
  simp only [Semiring.pow_zero,Semiring.natCast_zero,Semiring.zero_mul] at one
  rw [one] at jlog
  have lo:=Analytic.three_log_two laws
  have hi:=Analytic.four_log_two laws mult
  have pos : (0:K)≤l.log 2 := by grind
  change (((labelSize ns)^2:Nat):K)≤6+l.log (j:K) at lower
  have step:=OrderedRing.mul_le_mul_of_nonneg_right lower pos
  have absorb:=OrderedRing.mul_le_mul_of_nonneg_left (by grind : l.log (2:K)≤1) jlog
  change 2^((labelSize ns)^2)≤64*j
  apply Nat.le_of_not_gt
  intro contrary
  have clash:=laws.strict (OrderedRing.pos_natCast_of_pos _ (Nat.mul_pos (by decide : 0<64) jp))
    (OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ contrary)
  have two : ((2:Nat):K)=2 := by grind
  change l.log (((2^6*j:Nat)):K)<_ at clash
  rw [Semiring.natCast_mul,mult.product (OrderedRing.pos_natCast_of_pos _ (by decide : 0<2^6))
    (OrderedRing.pos_natCast_of_pos _ jp),Semiring.natCast_pow,Semiring.natCast_pow,two,
    l.power (by grind : (0:K)<2),l.power (by grind : (0:K)<2)] at clash
  grind

/-- Formula in the two rational coefficients of the actual product, valid also
when the second coefficient vanishes. -/
theorem index_height_of_primitive_quadratic {x : Fin 84→Rat} {ns : Labels} (r : K) (sqrtTwo : r^2=2)
    (laws : Analytic.BinaryLogLaw l) (mult : Analytic.ProductLogLaw l)
    (plus : 1≤Analytic.embedRat (atWire x 1249)+Analytic.embedRat (atWire x 1252)*r)
    (minus : 1≤Analytic.embedRat (atWire x 1249)-Analytic.embedRat (atWire x 1252)*r)
    (lower : (((labelSize ns)^2:Nat):K)≤6+Analytic.positiveQuadraticHeight l (atWire x 1249) (atWire x 1252)) :
    IndexHeight x ns := by
  apply index_height_of_log laws mult
  have hi:=Analytic.explicit_height_le_joint l _ _ r sqrtTwo plus minus
  change _≤6+l.log ((jointHeight (atWire x 1249) (atWire x 1252):Nat):K)
  grind

#print axioms index_height_of_log
#print axioms index_height_of_primitive_quadratic
end HeightSpecialization
