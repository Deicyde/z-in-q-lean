import TriClosed
import ComparisonChart
namespace PhysicalProjection.FieldRows
set_option exponentiation.threshold 2500
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data

inductive Block | A | S | T | Z deriving DecidableEq, Repr
inductive Relation | root | first | second | product | quartic | output | iSquare | kSquare deriving DecidableEq, Repr

def Block.number : Block→Nat | .A=>0 | .S=>1 | .T=>2 | .Z=>3
def Block.h : Block→Nat | .A=>2 | .S=>6 | .T=>8 | .Z=>12
def Block.squareSlot : Block→Nat | .A=>84 | .S=>86 | .T=>92 | .Z=>98
def field (z : Assignment) (i : Nat) : Q2 := (z i,z (i+1))
def plus (x y : Q2) : Q2 := (x.1+y.1,x.2+y.2)
def scale (s : Rat) (x : Q2) : Q2 := (s*x.1,s*x.2)
def minus (x y : Q2) : Q2 := plus x (scale (-1) y)
def aa : Q2 := (-1,7/4)
def bb : Q2 := (39/8,-9/2)
def invAA : Q2 := (8/41,14/41)
def aval (k : Block) (z : Assignment) : Q2 := scale (if k=Block.S then 3^297 else 1) (field z k.h)
def bval (k : Block) (z : Assignment) : Q2 :=
  if k=Block.S then
    let a:=aval k z
    let d:=plus (times (sq aa) (sq a)) D2
    times invAA (plus (times bb a) (scale (3^883) (times d (field z 176))))
  else field z (k.h+2)
def L (g : Bool) (k : Block) (z : Assignment) :=
  let l:=field z (104+4*k.number)
  if k=Block.A then plus l (2398+(if g then 67830 else 510)*(z 1)^2,0) else l

def coreFormula (g : Bool) (k : Block) (r : Relation) (z : Assignment) (a b : Q2) : Q2 :=
  let i:=k.number; let c:=sq a
  let V:=field z (16+4*i); let I:=field z (18+4*i)
  let W:=field z (48+4*i); let K:=field z (50+4*i)
  let q:=scale (-1) (times K (field z (68+2*i)))
  match r with
  | .root => minus (plus (sq b) D2) (sq c)
  | .first => minus (minus (minus (times a I) (times b V)) (times c q)) (times D2 (times V W))
  | .second => plus (plus (plus (times a K) (times b q)) (times c V)) (times D2 (times q W))
  | .product => minus (times V q) (times c W)
  | .quartic => minus (plus (plus (plus (sq V) (sq q)) (times D2 (sq W))) (scale 2 (times b W))) one
  | .output => minus (times I (L g k z)) (times V (scale 3 (field z 66)))
  | .iSquare => let t:=field z (122+2*i); minus (plus (times (times D2 c) (t.1,2*t.2)) (sq I)) c
  | .kSquare => let t:=field z k.squareSlot; minus (plus (times (times D2 c) (t.1,2*t.2)) (sq K)) c

def dilate (i : Nat) : Int := if i=6 ∨ i=7 then 3^297 else if i=176 ∨ i=177 then 3^883 else 1

def shifted (z : Assignment) (i : Nat) : Rat := (dilate i:Rat)*z i

def plainB (k : Block) (z : Assignment) : Q2 :=
  if k=Block.S then
    let a:=field z k.h
    let d:=plus (times (sq aa) (sq a)) D2
    times invAA (plus (times bb a) (times d (field z 176)))
  else field z (k.h+2)

def plain (g : Bool) (k : Block) (r : Relation) (z : Assignment) :=
  coreFormula g k r z (field z k.h) (plainB k z)

def formula (g : Bool) (k : Block) (r : Relation) (z : Assignment) :=
  plain g k r (if k=.S then shifted z else z)

def component (imag : Bool) (x : Q2) := if imag then x.2 else x.1

theorem shifted_S (z : Assignment) :
    let a:=aval .S z;let d:=plus (times (sq aa) (sq a)) D2
    times aa (bval .S z)=plus (times bb a) (scale (3^883) (times d (field z 176))) := by
  have inv (v : Q2) : times aa (times invAA v)=v := by
    apply Prod.ext <;> dsimp [aa,invAA,times] <;> grobner
  exact inv _

/-- Both scaled input pairs implement the S root used by the physical formula. -/
theorem shifted_a (z : Assignment) : field (shifted z) 6=aval .S z := by
  apply Prod.ext <;> dsimp [field,shifted,aval,scale,Block.h,dilate] <;> grobner

theorem shifted_b (z : Assignment) : plainB .S (shifted z)=bval .S z := by
  have y : field (shifted z) 176=scale (3^883) (field z 176) := by
    apply Prod.ext <;> dsimp [field,shifted,scale,dilate] <;> grobner
  have move (k : Rat) (d w : Q2) : times d (scale k w)=scale k (times d w) := by
    apply Prod.ext <;> dsimp [times,scale] <;> grobner
  change times invAA (plus (times bb (field (shifted z) 6)) (times (plus (times (sq aa) (sq (field (shifted z) 6))) D2) (field (shifted z) 176)))=_
  rw [shifted_a,y,move];rfl

end PhysicalProjection.FieldRows
