import ChordDepth

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K : Type} [Field K] {D : K} {w : ExtensionPlace p K} {d : Int}

/-- Concrete projective points in a fixed positive-depth neighborhood of infinity. -/
structure LocalPoint (w : ExtensionPlace p K) (D : K) (d : Int) where
  t : K
  s : K
  equation : OnCurve D t s
  layer : Layer w d t s

namespace LocalPoint

def origin : LocalPoint w D d :=
  ⟨0,0,by unfold OnCurve;grobner,deep_zero w _,deep_zero w _⟩

def reflect (P : LocalPoint w D d) : LocalPoint w D d where
  t:= -P.t
  s:= -P.s
  equation:=by have eq:=P.equation;unfold OnCurve at *;grobner
  layer:=⟨deep_neg w P.layer.1,deep_neg w P.layer.2⟩

def add (positive : 0<d) (integral : w.deep 0 D) (P Q : LocalPoint w D d) : LocalPoint w D d :=
  let c:=chord w positive integral P.equation Q.equation P.layer Q.layer
  ⟨c.t,c.l*c.t-c.k,c.onCurve,c.layer⟩

theorem add_error (pos : 0<d) (hD : w.deep 0 D) (P Q : LocalPoint w D d) :
    w.deep (5*d) ((P.add pos hD Q).t-P.t-Q.t) :=
  (chord w pos hD P.equation Q.equation P.layer Q.layer).error

def natural (pos : 0<d) (hD : w.deep 0 D) (P : LocalPoint w D d) : Nat → LocalPoint w D d
  | 0=>origin
  | n+1=>(natural pos hD P n).add pos hD P

def signed (pos : 0<d) (hD : w.deep 0 D) (P : LocalPoint w D d) : Int → LocalPoint w D d
  | .ofNat n=>P.natural pos hD n
  | .negSucc n=>(P.natural pos hD (n+1)).reflect

/-- Signed iteration of the explicit chord on field pairs, independent of a
group carrier. The factorization in chord certifies each addition and doubling. -/
theorem signed_error (pos : 0<d) (hD : w.deep 0 D) (P : LocalPoint w D d) (n : Int) :
    w.deep (5*d) ((P.signed pos hD n).t-(n:K)*P.t) := by
  have nat (j : Nat) : w.deep (5*d) ((P.natural pos hD j).t-((j:Int):K)*P.t) := by
    induction j with
    | zero =>
      change w.deep _ (0-((0:Int):K)*P.t)
      rw [Ring.intCast_zero,show (0:K)-0*P.t=0 by grobner]
      exact deep_zero w _
    | succ j ih =>
      let A:=P.natural pos hD j
      have e:=A.add_error pos hD P
      change w.deep _ ((A.add pos hD P).t-((j.succ:Int):K)*P.t)
      rw [Int.natCast_succ,Ring.intCast_add,Ring.intCast_one,
        show (A.add pos hD P).t-(((j:Int):K)+1)*P.t =
          ((A.add pos hD P).t-A.t-P.t)+(A.t-((j:Int):K)*P.t) by grobner]
      exact w.deep_add e ih
  cases n with
  | ofNat j=>exact nat j
  | negSucc j=>
    change w.deep _ (-(P.natural pos hD (j+1)).t-(Int.negSucc j:K)*P.t)
    rw [show Int.negSucc j= -((j+1:Nat):Int) by omega,Ring.intCast_neg]
    rw [show -(P.natural pos hD (j+1)).t-(-(((j+1:Nat):Int):K))*P.t =
      -((P.natural pos hD (j+1)).t-(((j+1:Nat):Int):K)*P.t) by grobner]
    exact deep_neg w (nat (j+1))

/-- A concrete rational point witnesses equality in the fifth-order bound at 5. -/
theorem sharp_at_five :
    let t : Rat:=5
    let s : Rat:=t^3*(1-t^4)
    let D : Rat:=1/(1-t^4)^2
    let l:=slope D t t s s
    let k:=s-l*t
    let h:=t+t-2*D*l*k/leading D l
    OnCurve D t s ∧ order 5 t=1 ∧ order 5 s=3 ∧ order 5 D=0 ∧
      order 5 (slopeDen D t s s)=0 ∧ order 5 (leading D l)=0 ∧ order 5 (h-t-t)=5 := by
  dsimp only [OnCurve]
  decide +kernel

end LocalPoint
end ProjectionFibres
