import PrimeInputs
import AnchorBase23

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} [NeZero p]

def DivisionValue (D q y : Q2) (m : Int) (a b : List Int) : Prop :=
  let z:=times D (sq q)
  times y (eval (1::a) z)=times q (eval ((m*m)::b) z)

def Normalized (p : Nat) [NeZero p] (q y : Q2) (m : Rat) : Prop :=
  ∃ u, PairRed p u (1,0) ∧ y=times (scale (m^2) q) u

theorem normalized_one (q : Q2) : Normalized p q q 1 := by
  refine ⟨(1,0),pairOne,?_⟩
  rw [tm_one]; apply Prod.ext <;> dsimp [scale] <;> grobner

theorem Normalized.trans {q r s : Q2} {a b : Rat} (h : Normalized p q r a)
    (j : Normalized p r s b) : Normalized p q s (a*b) := by
  obtain ⟨u,ur,ue⟩:=h
  obtain ⟨v,vr,ve⟩:=j
  exact ⟨times u v,compose ur vr ue ve⟩

theorem baseD_integral (p : Nat) [NeZero p] : IntegralPair p Base.D :=
  ⟨((11:Int),(-6:Int)),redInt 11,redInt (-6)⟩

end Prime23
