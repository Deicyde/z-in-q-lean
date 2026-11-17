import DetectorArithmetic
namespace ProjectionFibres.Comparison
open StructuralReduction Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

structure Step where
  index : Nat
  m : Nat
  y : Q
  z : Q
  qN : Rat
  qD : Rat
  factor : Q

def Step.weight (s : Step) := s.qN/s.qD
def Step.valid (s : Step) (r delta : Rat) : Prop :=
  1≤s.m ∧ s.y.d≠0 ∧ s.z.d≠0 ∧ s.qD≠0 ∧ s.factor.d≠0 ∧ boundEq s.y s.z ∧
  factorEq s.z ⟨s.qN,0,s.qD⟩ s.factor ∧ s.weight*r^(4*s.m-3)*delta^(4*s.m)=1

def Q.safe (q : Q) := q.d≠0

/-- Test rows grow in reverse instruction order while the quadratically encoded product grows forward. -/
inductive Chain (r delta : Rat) : List Step→Q→Prop
  | nil : Chain r delta [] one
  | add {xs before} (old : Chain r delta xs before) (s : Step) (after : Q)
      (valid : s.valid r delta) (safe : after.d≠0) (eq : productEq before s.factor after) :
      Chain r delta (s::xs) after

structure Data where
  R : Rat
  delta : Rat
  traceN : Rat
  traceD : Rat
  finalQ : Q
  steps : List Step

def Data.trace (a : Data) := a.traceN/a.traceD
def Data.valid (a : Data) :=
  a.R≠0 ∧ a.delta≠0 ∧ a.traceN≠0 ∧ a.traceD≠0 ∧
  Chain a.R a.delta a.steps a.finalQ ∧ traceEq a.finalQ ⟨a.traceN,0,a.traceD⟩

theorem fraction_nonzero {a d : Rat} (ha : a≠0) (hd : d≠0) : a/d≠0 := by
  intro z
  have eq:=Rat.div_mul_cancel (a:=a) hd
  rw [z,Rat.zero_mul] at eq
  exact ha eq.symm

private theorem rational_mul_pow (a b : Rat) (n : Nat) : (a*b)^n=a^n*b^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ,ih];grobner
private theorem rational_pow_nz {a : Rat} (h : a≠0) (n : Nat) : a^n≠0 := by
  induction n with
  | zero => rw [Rat.pow_zero];decide
  | succ n ih => rw [Rat.pow_succ];exact fun bad=>(Rat.mul_eq_zero.mp bad).elim ih h

theorem weight_equation {n d a b c e : Rat} {i j : Nat} (hd : d≠0) (hb : b≠0) (he : e≠0)
    (h : n*a^i*c^j=d*b^i*e^j) : (n/d)*(a/b)^i*(c/e)^j=1 := by
  have u : (a/b)^i*b^i=a^i := by rw [←rational_mul_pow,Rat.div_mul_cancel hb]
  have v : (c/e)^j*e^j=c^j := by rw [←rational_mul_pow,Rat.div_mul_cancel he]
  have m : (n/d)*d=n:=Rat.div_mul_cancel hd
  have fact : ((n/d)*(a/b)^i*(c/e)^j)*(d*b^i*e^j)=d*b^i*e^j := by
    calc
      _=((n/d)*d)*((a/b)^i*b^i)*((c/e)^j*e^j) := by grobner
      _=_ := by rw [m,u,v,h]
  have nonzero : d*b^i*e^j≠0 := fun z=>(Rat.mul_eq_zero.mp z).elim (fun t=>(Rat.mul_eq_zero.mp t).elim hd (rational_pow_nz hb i)) (rational_pow_nz he j)
  have cancel {x y : Rat} (nz : y≠0) (same : x*y=y) : x=1 := by
    have h : (x-1)*y=0 := by grobner
    have e:=(Rat.mul_eq_zero.mp h).resolve_right nz
    grobner
  exact cancel nonzero fact

end ProjectionFibres.Comparison
