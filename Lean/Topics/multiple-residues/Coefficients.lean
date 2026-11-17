import BinaryDivisionPolynomials

namespace ReciprocalDivision
namespace Coefficients
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- Coefficients are in ascending order, so the constant term comes first. -/
def add : List Int → List Int → List Int
  | [], b => b
  | a, [] => a
  | a::s, b::t => (a+b)::add s t

def scale (c : Int) (l : List Int) := l.map (c * ·)

def mul : List Int → List Int → List Int
  | [], _ => []
  | a::s, t => add (scale a t) (0::mul s t)

def ofExpr : Expr → List Int
  | .zero => []
  | .one => [1]
  | .var => [0,1]
  | .add a b => add (ofExpr a) (ofExpr b)
  | .sub a b => add (ofExpr a) (scale (-1) (ofExpr b))
  | .mul a b => mul (ofExpr a) (ofExpr b)

variable {R : Type u} [CommRing R]

def eval (z : R) : List Int → R
  | [] => 0
  | a::t => (a:R) + z*eval z t

private theorem eval_add (z : R) (s t : List Int) :
    eval z (add s t)=eval z s+eval z t := by
  induction s generalizing t with
  | nil => simp only [add, eval]; grobner
  | cons a s ih =>
    cases t with
    | nil => simp only [add,eval]; grobner
    | cons b t => simp only [add,eval,Ring.intCast_add,ih]; grobner

private theorem eval_scale (z : R) (a : Int) (s : List Int) :
    eval z (scale a s)=(a:R)*eval z s := by
  induction s with
  | nil => simp only [scale,List.map_nil,eval]; grobner
  | cons b t ih =>
    change (↑(a*b):R)+z*eval z (scale a t)=_
    rw [Ring.intCast_mul,ih,eval]
    grobner

private theorem eval_mul (z : R) (s t : List Int) :
    eval z (mul s t)=eval z s*eval z t := by
  induction s with
  | nil => simp only [mul,eval]; grobner
  | cons a s ih => simp only [mul,eval_add,eval_scale,eval,Ring.intCast_zero,ih]; grobner

theorem eval_ofExpr (z : R) (e : Expr) : eval z (ofExpr e)=e.eval z := by
  induction e with
  | zero => rfl
  | one => simp only [ofExpr,eval,Expr.eval,Ring.intCast_one]; grobner
  | var => simp only [ofExpr,eval,Expr.eval,Ring.intCast_zero,Ring.intCast_one]; grobner
  | add a b ha hb => simp only [ofExpr,eval_add,ha,hb,Expr.eval]
  | sub a b ha hb =>
    simp only [ofExpr,eval_add,eval_scale,ha,hb,Expr.eval,Ring.intCast_neg,Ring.intCast_one]
    grobner
  | mul a b ha hb => simp only [ofExpr,eval_mul,ha,hb,Expr.eval]

private theorem head_zero (s : List Int) : eval (0:Int) s = s.headD 0 := by
  cases s <;> simp [eval,List.headD]

private theorem eval_head_tail (z : R) (s : List Int) :
    eval z (s.headD 0::s.tail)=eval z s := by
  cases s with
  | nil => simp only [List.headD,List.tail_nil,eval,Ring.intCast_zero]; grobner
  | cons => rfl

private theorem natAbs_square (m : Int) : (m.natAbs:Int)^2=m*m := by
  cases m with
  | ofNat n => change (n:Int)^2=(n:Int)*(n:Int); grobner
  | negSucc n =>
    change ((n+1:Nat):Int)^2=Int.negSucc n*Int.negSucc n
    rw [Int.negSucc_eq]
    grobner

private def lists (m : Int) : List Int × List Int :=
  let t := quotientPair Expr.var m.natAbs
  (ofExpr t.1,ofExpr t.2)

/-- The polynomial remainders after removing 1 and m² from the two constant terms. -/
def topTail (m : Int) : List Int := (lists m).1.tail
def bottomTail (m : Int) : List Int := (lists m).2.tail

private theorem heads (m : Int) : ((lists m).1.headD 0,(lists m).2.headD 0)=(1,m*m) := by
  change ((ofExpr _).headD 0,(ofExpr _).headD 0)=_
  rw [← head_zero,← head_zero,eval_ofExpr,eval_ofExpr]
  exact (eval_quotient (0:Int) m.natAbs).trans ((constant_quotient m.natAbs).trans (by rw [natAbs_square]))

/-- These are the coefficient lists used in the prime-by-prime residue calculation. -/
theorem table_eval (z : R) (m : Int) :
    (eval z (1::topTail m),eval z ((m*m)::bottomTail m))=quotientPair z m.natAbs := by
  have h := heads m
  have ht := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change (lists m).1.headD 0=1 at ht
  change (lists m).2.headD 0=m*m at hb
  rw [← ht,← hb,topTail,bottomTail,eval_head_tail,eval_head_tail]
  change (eval z (ofExpr _),eval z (ofExpr _))=_
  rw [eval_ofExpr,eval_ofExpr]
  exact eval_quotient z m.natAbs

#print axioms table_eval
end Coefficients
end ReciprocalDivision
