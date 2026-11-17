import BinaryHeight

namespace HeightSpecialization.Analytic
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

structure ProductLogLaw (l : LogLaw K) : Prop where
  product : ∀{x y},(0:K)<x → 0<y → l.log (x*y)=l.log x+l.log y

omit [LawfulOrderLT K] in
private theorem log_one (l : LogLaw K) : l.log (1:K)=0 := by
  have h:=l.power (x:=(1:K)) OrderedRing.zero_lt_one 0
  simpa only [Semiring.pow_zero,Semiring.natCast_zero,Semiring.zero_mul] using h

private theorem upper_tangent {l : LogLaw K} (laws : BinaryLogLaw l) (m : ProductLogLaw l)
    {x : K} (pos : 0<x) : l.log x≤x-1 := by
  have invp:=Field.IsOrdered.inv_pos_iff.mpr pos
  have tangent:=laws.tangent invp
  rw [Field.inv_inv] at tangent
  have sum:=m.product pos invp
  rw [Field.mul_inv_cancel (Preorder.ne_of_gt pos),log_one] at sum
  grind

/-- Upper tangency at 9/8 and the integer inequality 2·8⁶ < 9⁶ imply 4 log 2 ≤ 3. -/
theorem four_log_two {l : LogLaw K} (laws : BinaryLogLaw l) (m : ProductLogLaw l) :
    4*l.log (2:K)≤3 := by
  have d : (0:K)<8 := by grind
  have n : (0:K)<9 := by grind
  let y:K:=9/8
  have yp : (0:K)<y := by
    unfold y
    rw [Field.div_eq_mul_inv]
    exact OrderedRing.mul_pos n (Field.IsOrdered.inv_pos_iff.mpr d)
  have y8 : y*(8:K)=9 := Field.div_mul_cancel (Preorder.ne_of_gt d)
  have power:=congrArg (fun a:K=>a^6) y8
  change (y*8)^6=(9:K)^6 at power
  rw [CommSemiring.mul_pow] at power
  have intBound:=OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ (by decide : 2*8^6<9^6)
  simp only [Semiring.natCast_pow,Semiring.natCast_mul] at intBound
  have bound : (2:K)≤y^6 := by
    apply Classical.byContradiction
    intro bad
    have small : y^6≤2 := by grind
    have pos : (0:K)<8^6 := by grind
    have clash:=OrderedRing.mul_le_mul_of_nonneg_right small (Preorder.le_of_lt pos)
    rw [power] at clash
    grind
  have up:=l.monotone (by grind : (0:K)<2) bound
  rw [l.power yp] at up
  have lower:=upper_tangent laws m yp
  grind

private theorem natlog_power (l : LogLaw K) (a e : Nat) (p : 0<a) :
    l.log ((a^e:Nat):K)=(e:K)*l.log (a:K) := by
  rw [Semiring.natCast_pow,l.power (OrderedRing.pos_natCast_of_pos _ p)]

/-- The two additive height estimates imply the integral root-height comparison. -/
theorem root_log_bound {l : LogLaw K} (laws : BinaryLogLaw l) (m : ProductLogLaw l)
    (N J : Nat) (jpos : 0<J) (hC : K)
    (root : ((N^2:Nat):K)≤6+hC) (comparison : 2*hC≤2*l.log (J:K)+3*l.log 2) :
    2^(4*N^2)≤2^30*J^3 := by
  have j : (0:K)<(J:K) := OrderedRing.pos_natCast_of_pos _ jpos
  have one : (1:K)≤(J:K) := by
    have a:=OrderedRing.natCast_le_natCast_of_le (R:=K) 1 J jpos
    simpa only [Semiring.natCast_one] using a
  have jl:=l.monotone OrderedRing.zero_lt_one one
  rw [log_one] at jl
  have upper:=four_log_two laws m
  have lower:=three_log_two laws
  have two : ((2:Nat):K)=2 := by grind
  have twice : 2*((N^2:Nat):K)≤12+2*l.log (J:K)+3*l.log 2 := by grind
  have scale:=OrderedRing.mul_le_mul_of_nonneg_right twice (by grind : (0:K)≤2*l.log 2)
  have logJ:=OrderedRing.mul_le_mul_of_nonneg_right upper jl
  have sq:=OrderedRing.mul_le_mul_of_nonneg_right (by grind : l.log (2:K)≤1) (by grind : (0:K)≤l.log 2)
  have budget : ((4*N^2:Nat):K)*l.log (2:K)≤30*l.log 2+3*l.log (J:K) := by
    rw [Semiring.natCast_mul]
    grind
  apply Nat.le_of_not_gt
  intro contrary
  have tpos : 0<2^30*J^3 := Nat.mul_pos (by decide) (Nat.pow_pos jpos)
  have clash:=laws.strict (OrderedRing.pos_natCast_of_pos _ tpos)
    (OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ contrary)
  have logProduct:=m.product (OrderedRing.pos_natCast_of_pos (R:=K) _ (by decide : 0<2^30))
    (OrderedRing.pos_natCast_of_pos (R:=K) _ (Nat.pow_pos jpos : 0<J^3))
  rw [Semiring.natCast_mul,logProduct,natlog_power l 2 30 (by decide),natlog_power l J 3 jpos,
      natlog_power l 2 _ (by decide),two] at clash
  grind

/-- Version in the usual additive Faltings-height convention with 3/2 as a scalar. -/
theorem root_log_bound_half {l : LogLaw K} (laws : BinaryLogLaw l) (m : ProductLogLaw l)
    (N J : Nat) (jpos : 0<J) (hC : K)
    (root : ((N^2:Nat):K)≤6+hC) (comparison : hC≤l.log (J:K)+(3/2:K)*l.log 2) :
    2^(4*N^2)≤2^30*J^3 := by
  apply root_log_bound laws m N J jpos hC root
  have half : (3/2:K)*2=3 := Field.div_mul_cancel (by grind)
  have move : 2*((3/2:K)*l.log 2)=3*l.log 2 := by
    calc _=((3/2:K)*2)*l.log 2 := by grobner
         _=_ := by rw [half]
  have scale:=OrderedRing.mul_le_mul_of_nonneg_left comparison (by grind : (0:K)≤2)
  rw [Semiring.left_distrib,move] at scale
  exact scale

end HeightSpecialization.Analytic
