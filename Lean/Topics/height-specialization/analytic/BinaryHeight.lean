import AnalyticHeight

namespace HeightSpecialization.Analytic
open Lean.Grind Std IndependentIndices
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

/-- Two real-log properties used by the binary multiplicative-height conversions. -/
structure BinaryLogLaw (l : LogLaw K) where
  strict : ∀{x y},(0:K)<x → x<y → l.log x<l.log y
  tangent : ∀{x},(0:K)<x → 1-x⁻¹≤l.log x

omit [LawfulOrderLT K] in
private theorem positive_power (x : K) (h : (0:K)<x) : ∀ n : Nat,0<x^n
  | 0 => by rw [Semiring.pow_zero];exact OrderedRing.zero_lt_one
  | n+1 => by rw [Semiring.pow_succ];exact OrderedRing.mul_pos (positive_power x h n) h

/-- The integer inequality 27⁹ < 2·25⁹ and the tangent at 27/25 give a rational
certificate for 2 < 3 log 2. -/
theorem three_log_two {l : LogLaw K} (laws : BinaryLogLaw l) : (2:K)<3*l.log 2 := by
  have d : (0:K)<25 := by grind
  have n : (0:K)<27 := by grind
  let y:K:=27/25
  have yp : 0<y := by
    unfold y
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_pos n (Field.IsOrdered.inv_pos_iff.mpr d)
  have y25 : y*(25:K)=27 := Field.div_mul_cancel (Preorder.ne_of_gt d)
  have yinv : y⁻¹*(27:K)=25 := by
    calc _=y⁻¹*(y*25) := by rw [y25]
         _=_ := by rw [←Semiring.mul_assoc,Field.inv_mul_cancel (Preorder.ne_of_gt yp),Semiring.one_mul]
  have power:=congrArg (fun a:K=>a^9) y25
  change (y*25)^9=(27:K)^9 at power
  rw [CommSemiring.mul_pow] at power
  have intBound:=OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ (by decide : 27^9<2*25^9)
  simp only [Semiring.natCast_pow,Semiring.natCast_mul] at intBound
  have bound : y^9<2 := by
    apply Classical.byContradiction
    intro bad
    have small : (2:K)≤y^9 := by grind
    have pos:=positive_power (25:K) d 9
    have clash:=OrderedRing.mul_le_mul_of_nonneg_right small (Preorder.le_of_lt pos)
    rw [power] at clash
    grind
  have up:=laws.strict (positive_power y yp 9) bound
  rw [l.power yp] at up
  have lower:=laws.tangent yp
  grind

theorem twice_log_two {l : LogLaw K} (laws : BinaryLogLaw l) : (1:K)≤2*l.log 2 := by
  have h:=three_log_two laws
  grind

private theorem compare_log {l : LogLaw K} (laws : BinaryLogLaw l) (H E : Nat)
    (bound : l.log (H:K)≤(E:K)*l.log 2) : H≤2^E := by
  have pos : (0:K)<2 := by grind
  apply Nat.le_of_not_gt
  intro bad
  have x:=OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ bad
  have clash:=laws.strict (OrderedRing.pos_natCast_of_pos _ (Nat.pow_pos (by decide : 0<2))) x
  have two : ((2:Nat):K)=2 := by grind
  rw [Semiring.natCast_pow,two,l.power pos] at clash
  grind

theorem binary_height {l : LogLaw K} (laws : BinaryLogLaw l) (H B : Nat)
    (logHeight : l.log (H:K)≤(B:K)) : H≤2^(2*B) := by
  apply compare_log laws
  rw [Semiring.natCast_mul]
  have h:=OrderedRing.mul_le_mul_of_nonneg_left (twice_log_two laws) (OrderedRing.natCast_nonneg (a:=B) (R:=K))
  grind

theorem binary_height_squared {l : LogLaw K} (laws : BinaryLogLaw l) (H B : Nat)
    (logHeight : l.log (H:K)≤(B:K)) : H^2≤2^(3*B) := by
  by_cases pos : 0<H
  · apply compare_log laws
    rw [Semiring.natCast_pow,l.power (OrderedRing.pos_natCast_of_pos _ pos),Semiring.natCast_mul]
    have h:=OrderedRing.mul_le_mul_of_nonneg_left (Preorder.le_of_lt (three_log_two laws)) (OrderedRing.natCast_nonneg (a:=B) (R:=K))
    grind
  · have z : H=0 := by omega
    simp [z]

theorem scalar_binary {l : LogLaw K} (laws : BinaryLogLaw l) (ps : List Nat) (H : Nat) (A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉scalarSet)
    (G : l.log (H:K)≤2*bigger 0 A+128) (input : FibreInput l scalarSet (support ps) A) :
    H≤2^(2*HeightClosure.constant scalarSet*(radical ps)^17) := by
  rw [Nat.mul_assoc]
  exact binary_height laws _ _ (scalar_manuscript_constant l ps _ A prime away G input)

theorem detector_binary_squared {l : LogLaw K} (laws : BinaryLogLaw l) (ps : List Nat) (H : Nat) (A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉detectorSet)
    (G : l.log (H:K)≤2*bigger 0 A+128) (input : FibreInput l detectorSet (support ps) A) :
    H^2≤2^(3*HeightClosure.constant detectorSet*(radical ps)^17) := by
  rw [Nat.mul_assoc]
  exact binary_height_squared laws _ _ (detector_manuscript_constant l ps _ A prime away G input)

end HeightSpecialization.Analytic
