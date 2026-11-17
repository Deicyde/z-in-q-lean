import Clear
namespace Physical130
open ZeroInput.Sparse ProjectionDescent CircuitTransport

inductive Column | c | u | v deriving DecidableEq

def extract (j : Nat) : List Nat → Column × List Nat
  | [] => (.c,[])
  | i::m => if i=j then (.u,m) else if i=j+1 then (.v,m) else
      let a := extract j m
      (a.1,i::a.2)

def factor (z : ProjectionDescent.Assignment) (j : Nat) : Column → Rat | .c => 1 | .u => z j | .v => z (j+1)

private theorem extract_value (z : ProjectionDescent.Assignment) (j : Nat) (m : List Nat) :
    monomialValue z m=factor z j (extract j m).1*monomialValue z (extract j m).2 := by
  induction m with
  | nil => simp [extract,factor,monomialValue]
  | cons i m ih =>
    by_cases a : i=j
    · subst i; simp [extract,factor,monomialValue]
    · by_cases h : i=j+1
      · simp [extract,h,factor,monomialValue]
      · simp only [extract,if_neg a,if_neg h,monomialValue]
        grobner

def column (j : Nat) (k : Column) : Polynomial→Polynomial
  | [] => []
  | t::ts => let e:=extract j t.monomial
             if e.1=k then ⟨t.coefficient,e.2⟩::column j k ts else column j k ts

theorem split_value (z : ProjectionDescent.Assignment) (j : Nat) (p : Polynomial) :
    value z p=value z (column j .c p)+z j*value z (column j .u p)+z (j+1)*value z (column j .v p) := by
  induction p with
  | nil => simp [column,value];grobner
  | cons t ts ih =>
    have a:=extract_value z j t.monomial
    cases e : (extract j t.monomial).1 <;> simp [e,factor] at a <;>
      simp only [column,e,reduceCtorEq,if_false,if_true,value,termValue] <;> grobner

structure Aff where
  c : Word
  u : Word
  v : Word
  den : Nat

def line (b : Book) (env : Coords) (j : Nat) (p : Polynomial) : Aff :=
  let c:=column j .c p
  let u:=column j .u p
  let v:=column j .v p
  let d:=Nat.lcm (common env c) (Nat.lcm (common env u) (common env v))
  let term := accumulate b env d (integer b 0)
  ⟨term c,term u,term v,d⟩

theorem clear_acc {b x env z} (h : Along b x env z) (d : Nat) (p : Polynomial)
    (mult : common env p ∣ d) :
    (accumulate b env d (integer b 0) p).value b x=(d:Rat)*value z p := by
  have go (w : Word) (poly : Polynomial) (hm : common env poly ∣ d) :
      (accumulate b env d w poly).value b x=w.value b x+(d:Rat)*value z poly := by
    induction poly generalizing w with
    | nil => simp [accumulate,value,Rat.add_zero]
    | cons t ts ih =>
      change (accumulate b env d (plus b w (clearTerm b env d t)) ts).value b x=_
      rw [ih _ (Nat.dvd_trans (Nat.dvd_lcm_right _ _) hm),plus_value,
        clear_term_value h _ _ (Nat.dvd_trans (Nat.dvd_lcm_left _ _) hm)]
      simp only [value];grobner
  rw [go _ p mult,integer_value,Rat.intCast_zero,Rat.zero_add]

structure AffCorrect (b : Book) (x z : ProjectionDescent.Assignment) (j : Nat) (p : Polynomial) (l : Aff) : Prop where
  pos : 0<l.den
  c : l.c.value b x=(l.den:Rat)*value z (column j .c p)
  u : l.u.value b x=(l.den:Rat)*value z (column j .u p)
  v : l.v.value b x=(l.den:Rat)*value z (column j .v p)

theorem line_correct {b x env z} (h : Along b x env z) (j : Nat) (p : Polynomial) :
    AffCorrect b x z j p (line b env j p) := by
  have pos (q : Polynomial) : 0<common env q := (clear_row_value h q).1
  refine ⟨Nat.lcm_pos (pos _) (Nat.lcm_pos (pos _) (pos _)),?_,?_,?_⟩
  · exact clear_acc h _ _ (Nat.dvd_lcm_left _ _)
  · exact clear_acc h _ _ (Nat.dvd_trans (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _))
  · exact clear_acc h _ _ (Nat.dvd_trans (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _))
end Physical130
