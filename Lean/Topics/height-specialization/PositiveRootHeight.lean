import GeometryEndpoint

namespace HeightSpecialization
open Lean.Grind Std StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.HeightSupport
open ProjectionFibres.Comparison IndependentIndices IndependentIndices.Assembly WitnessTransfer.Height
attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]
variable {l : Analytic.LogLaw K}

private theorem H_pos (u : Rat) : 0<H u := Nat.lt_of_lt_of_le u.den_pos (Nat.le_max_right ..)

private theorem four_log_joint (x : Fin 84→Rat) (dom : domain x) (l : Analytic.LogLaw K) :
    4*l.log ((J x:Nat):K)≤5*l.log ((H (slope x (tallest x)):Nat):K) := by
  have jpos : 0<J x := Nat.lt_of_lt_of_le (Nat.lcm_pos (atWire x 1249).den_pos
    (atWire x 1252).den_pos) (Nat.le_max_left ..)
  have e:=l.monotone (OrderedRing.pos_natCast_of_pos _ (Nat.pow_pos jpos (n:=4)))
    (OrderedRing.natCast_le_natCast_of_le (R:=K) _ _ (physical_joint_height dom))
  change l.log (((J x)^4:Nat):K)≤_ at e
  rw [Semiring.natCast_pow,Semiring.natCast_pow,
    l.power (OrderedRing.pos_natCast_of_pos _ jpos),l.power (OrderedRing.pos_natCast_of_pos _ (H_pos _))] at e
  grind

/-- A totally positive product with both conjugates above one permits the direct
additive estimate. The root input below is the single remaining elliptic inequality. -/
theorem positive_root_bound {x : Fin 84→Rat} {ns : Labels} (dom : domain x)
    (mult : Analytic.ProductLogLaw l) (lower : (((labelSize ns)^2:Nat):K)≤6+l.log ((J x:Nat):K))
    (g : FibreBound l Analytic.detectorSet (fullPrimes (slope x (tallest x))) (2+1/slope x (tallest x))) :
    2*(labelSize ns)^2<3*(detectorConstant*(M x (tallest x))^17) := by
  let t:=slope x (tallest x)
  let u:=2+1/t
  let V:=detectorConstant*(M x (tallest x))^17
  have nz : t≠0 := by
    intro e
    apply noMark x (tallest x) dom
    change P t=0
    simp [e,P]
  have trans:=l.monotone (OrderedRing.pos_natCast_of_pos _ (H_pos t))
    (OrderedRing.natCast_le_natCast_of_le (R:=K) _ _ (mobius_height t nz))
  change l.log ((H t:Nat):K)≤l.log ((3*H u:Nat):K) at trans
  rw [Semiring.natCast_mul,mult.product (OrderedRing.pos_natCast_of_pos _ (by decide : 0<3))
    (OrderedRing.pos_natCast_of_pos _ (H_pos u))] at trans
  have log3:=l.upper (by grind : (0:K)<((3:Nat):K))
  have five:=Analytic.detector_manuscript_constant l (fullPrimes t) _ _
    (fun p hp=>((mem_fullPrimes _ _).mp hp).1) (fun p hp=>((mem_fullPrimes _ _).mp hp).2.1)
    g.comparison g.fibre
  change l.log ((H u:Nat):K)≤(V:K) at five
  have joint:=four_log_joint x dom l
  change 4*l.log ((J x:Nat):K)≤5*l.log ((H t:Nat):K) at joint
  have pos:=Nat.pow_pos (scale_radical_pos x (tallest x)) (n:=17)
  have vhuge : 39<V := Nat.lt_of_lt_of_le (by decide +kernel : 39<detectorConstant)
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left detectorConstant pos)
  have forty:=OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ vhuge
  change 2*(labelSize ns)^2<3*V
  apply Nat.lt_of_not_ge
  intro wrong
  have contradiction:=OrderedRing.natCast_le_natCast_of_le (R:=K) _ _ wrong
  simp only [Semiring.natCast_mul] at contradiction
  grind

#print axioms positive_root_bound
end HeightSpecialization
