import Std

namespace ReciprocalDivision

inductive Bits
  | zero
  | bit0 (s : Bits)
  | bit1 (s : Bits)
  deriving Repr, DecidableEq

def Bits.index : Bits → Nat
  | .zero => 0
  | .bit0 s => 2*s.index
  | .bit1 s => 2*s.index+1

def bits (n : Nat) : Bits :=
  if n=0 then .zero else
    if n%2=0 then .bit0 (bits (n/2)) else .bit1 (bits (n/2))
termination_by n
decreasing_by all_goals omega

@[simp] theorem index_bits (n : Nat) : (bits n).index=n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [bits]
    split
    · rename_i e; simpa [Bits.index] using e.symm
    · have step := ih (n/2) (by omega)
      split <;> simp only [Bits.index,step] <;> omega

section Operations
variable {R : Type u} [Zero R] [OfNat R 1] [Add R] [Sub R] [Mul R]

def double (z : R) (p : R×R) : R×R :=
  let a := p.1
  let b := p.2
  let d := z*(b*b)
  let t := a*a+d
  let v := a*b*(a*a-d)
  (t*t, (v+v)+(v+v))

def middle (z : R) (p r : R×R) : R×R :=
  let t := p.1*r.1+z*(p.2*r.2)
  let v := p.1*r.2-r.1*p.2
  (t*t,v*v)

/-- Simultaneously evaluate the divisions for n and n+1. -/
def adjacent (z : R) : Bits → (R×R)×(R×R)
  | .zero => ((1,0),(1,1))
  | .bit0 s => let t := adjacent z s; (double z t.1,middle z t.1 t.2)
  | .bit1 s => let t := adjacent z s; (middle z t.1 t.2,double z t.2)

def quotientPair (z : R) (n : Nat) : R×R := (adjacent z (bits n)).1

end Operations

/-- Integer polynomial expressions in a single variable. No division occurs. -/
inductive Expr
  | zero | one | var
  | add (a b : Expr) | sub (a b : Expr) | mul (a b : Expr)

instance : Zero Expr := ⟨.zero⟩
instance : OfNat Expr 1 := ⟨.one⟩
instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩

def Expr.eval {R : Type u} [Zero R] [OfNat R 1] [Add R] [Sub R] [Mul R] (z : R) : Expr → R
  | .zero => 0
  | .one => 1
  | .var => z
  | .add a b => a.eval z + b.eval z
  | .sub a b => a.eval z - b.eval z
  | .mul a b => a.eval z * b.eval z

section Evaluation
variable {R : Type u} [Zero R] [OfNat R 1] [Add R] [Sub R] [Mul R] (z : R)

private def mapPair (t : Expr×Expr) : R×R := ((t.1).eval z,(t.2).eval z)

private theorem map_double (p : Expr×Expr) :
    mapPair z (double Expr.var p)=double z (mapPair z p) := rfl
private theorem map_middle (p r : Expr×Expr) :
    mapPair z (middle Expr.var p r)=middle z (mapPair z p) (mapPair z r) := rfl

theorem eval_adjacent (s : Bits) :
    let e := adjacent Expr.var s
    (mapPair z e.1,mapPair z e.2)=adjacent z s := by
  induction s with
  | zero => rfl
  | bit0 s ih =>
    change (mapPair z (double _ _),mapPair z (middle _ _ _))=_
    rw [map_double,map_middle,adjacent,← ih]
  | bit1 s ih =>
    change (mapPair z (middle _ _ _),mapPair z (double _ _))=_
    rw [map_middle,map_double,adjacent,← ih]

theorem eval_quotient (n : Nat) :
    let e := quotientPair Expr.var n
    (e.1.eval z,e.2.eval z)=quotientPair z n :=
  congrArg Prod.fst (eval_adjacent z (bits n))

end Evaluation

section Leading
open Lean.Grind
attribute [local instance] Semiring.natCast
variable {R : Type u} [CommRing R]

private theorem double_zero (k : R) : double 0 (1,k^2)=(1,(2*k)^2) := by
  apply Prod.ext <;> dsimp [double] <;> grobner

private theorem middle_zero (k : R) : middle 0 (1,k^2) (1,(k+1)^2)=(1,(2*k+1)^2) := by
  apply Prod.ext <;> dsimp [middle] <;> grobner

theorem constant_adjacent (s : Bits) :
    adjacent (0:R) s=((1,(s.index:R)^2),(1,((s.index:R)+1)^2)) := by
  induction s with
  | zero =>
    apply Prod.ext <;> apply Prod.ext <;> dsimp [adjacent,Bits.index] <;> grobner
  | bit0 s ih =>
    simp only [adjacent,ih,double_zero,middle_zero,Bits.index]
    simp only [Semiring.natCast_mul,← Semiring.ofNat_eq_natCast 2]
  | bit1 s ih =>
    simp only [adjacent,ih,middle_zero,double_zero,Bits.index]
    simp only [Semiring.natCast_mul,Semiring.natCast_add,Semiring.natCast_one,← Semiring.ofNat_eq_natCast 2]
    apply Prod.ext <;> apply Prod.ext <;> dsimp <;> grobner

theorem constant_quotient (n : Nat) : quotientPair (0:R) n=(1,(n:R)^2) := by
  simpa only [quotientPair,index_bits] using congrArg Prod.fst (constant_adjacent (R:=R) (bits n))

end Leading
end ReciprocalDivision
