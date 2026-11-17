import ScaleSelection
import BinaryHeight

namespace HeightSpecialization
open Lean.Grind Std StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.HeightSupport
open IndependentIndices IndependentIndices.Assembly ProjectionFibres.Comparison WitnessTransfer.Height
attribute [local instance] Semiring.natCast Ring.intCast
set_option maxRecDepth 8192

private theorem height_neg (x : Rat) : H (-x)=H x := by
  simp [H,multiplicativeHeight]

theorem mobius_height (t : Rat) (live : t≠0) : H t ≤ 3*H (2+1/t) := by
  let u:Rat:=2+1/t
  have den (x : Rat) : (((2:Int):Rat)-x).den=x.den := by
    change (Rat.sub ((2:Int):Rat) x).den=_
    simp [Rat.sub]
  have e : ((2:Int):Rat)-u= -t⁻¹ := by dsimp [u];rw [Rat.div_def];grobner
  have inv := height_inv t live
  have translate : H (((2:Int):Rat)-u) ≤ 3*H u := by
    have tr:=Int.natAbs_sub_le ((2:Int)*(u.den:Int)) u.num
    rw [Int.natAbs_mul,Int.natAbs_natCast] at tr
    have a : u.den≤H u := Nat.le_max_right ..
    have b : u.num.natAbs≤H u := Nat.le_max_left ..
    change max _ _ ≤ 3*H u
    rw [reduced_num,den]
    change (2*(u.den:Int)-u.num).natAbs≤2*u.den+u.num.natAbs at tr
    omega
  rw [e,height_neg,inv] at translate
  exact translate

variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]
variable {l : Analytic.LogLaw K}

/-- The comparison at the given five-mark argument and its modular or CM fibre. -/
structure FibreBound (l : Analytic.LogLaw K) (sigma ps : List Nat) (u : Rat) where
  faltings : K
  comparison : l.log ((H u:Nat):K)≤2*Analytic.bigger 0 faltings+128
  fibre : Analytic.FibreInput l sigma (Analytic.support ps) faltings

theorem analytic_slope {x : Fin 84→Rat} {f : Scale} (dom : domain x)
    (laws : Analytic.BinaryLogLaw l)
    (g : FibreBound l Analytic.detectorSet (fullPrimes (slope x f)) (2+1/(slope x f))) :
    SlopeHeight x f := by
  let t:=slope x f
  have nz : t≠0 := by
    intro e
    apply noMark x f dom
    change P t=0
    simp [e,P]
  have power:=Analytic.detector_binary_squared laws (fullPrimes t) _ _
    (fun p hp=>((mem_fullPrimes _ _).mp hp).1)
    (fun p hp=>((mem_fullPrimes _ _).mp hp).2.1) g.comparison g.fibre
  rw [Nat.mul_assoc] at power
  have bound:=Nat.pow_le_pow_left (mobius_height t nz) 2
  rw [Nat.mul_pow] at bound
  change (H t)^2≤2^(4+3*(detectorConstant*(M x f)^17))
  rw [Nat.pow_add]
  exact Nat.le_trans bound (Nat.mul_le_mul (by decide : 3^2≤2^4) power)

theorem analytic_scalar (B : Rat) (laws : Analytic.BinaryLogLaw l)
    (g : FibreBound l Analytic.scalarSet (scalarFullPrimes B) B) :
    H B≤2^(2*scalarConstant*(radical (scalarFullPrimes B))^17) := by
  apply Analytic.scalar_binary laws _ _ _ (fun p hp=>((mem_scalarFullPrimes _ _).mp hp).1) _ g.comparison g.fibre
  intro p hp mem
  obtain ⟨_,notDiv,n17,_⟩:=(mem_scalarFullPrimes _ _).mp hp
  simp [Analytic.scalarSet] at mem
  rcases mem with h|h|h|h|h
  all_goals subst p
  all_goals first | exact notDiv (by decide) | exact n17 rfl

#print axioms mobius_height
#print axioms analytic_slope
#print axioms analytic_scalar
end HeightSpecialization
