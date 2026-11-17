import PhysicalComparisons

namespace ProjectionFibres.Comparison
open StructuralReduction Lean.Grind WitnessTransfer
attribute [local instance] Semiring.natCast Ring.intCast

/-- Three rational coefficient wires represent (a+bρ)/d. -/
structure Q where
  a : Rat
  b : Rat
  d : Rat

def Q.constant (a b : Rat) : Q := ⟨a,b,1⟩
def Q.add (x y : Q) : Q := ⟨x.a*y.d+y.a*x.d,x.b*y.d+y.b*x.d,x.d*y.d⟩
def Q.mul (x y : Q) : Q := ⟨x.a*y.a+2*x.b*y.b,x.a*y.b+x.b*y.a,x.d*y.d⟩
def Q.conjugate (x : Q) : Q := ⟨x.a,-x.b,x.d⟩
def Q.same (x y : Q) : Prop := x.a*y.d=y.a*x.d ∧ x.b*y.d=y.b*x.d

variable {p : Nat} {K : Type} [Field K] (v : ExtensionPlace p K) (rho : K)
def Q.num (x : Q) : K := v.incl.map x.a+v.incl.map x.b*rho
def Q.eval (x : Q) : K := x.num v rho/v.incl.map x.d

theorem Q.clears (x : Q) (h : x.d≠0) : x.eval v rho*v.incl.map x.d=x.num v rho :=
  Field.div_mul_cancel (v.agrees x.d h).1

private theorem cancel {a b c : K} (hc : c≠0) (eq : a*c=b*c) : a=b := by
  calc a = a*(c*c⁻¹) := by rw [Field.mul_inv_cancel hc,Semiring.mul_one]
       _ = b*(c*c⁻¹) := by rw [←Semiring.mul_assoc,eq,Semiring.mul_assoc]
       _=b := by rw [Field.mul_inv_cancel hc,Semiring.mul_one]

theorem Q.eval_same {x y : Q} (same : x.same y) (hx : x.d≠0) (hy : y.d≠0) :
    x.eval v rho=y.eval v rho := by
  have a:=congrArg v.incl.map same.1
  have b:=congrArg v.incl.map same.2
  rw [v.incl.mul,v.incl.mul] at a b
  apply cancel (v.product (v.agrees x.d hx).1 (v.agrees y.d hy).1).1
  calc
    _ = (x.eval v rho*v.incl.map x.d)*v.incl.map y.d := by grobner
    _ = (y.eval v rho*v.incl.map y.d)*v.incl.map x.d := by
      rw [Q.clears v rho x hx,Q.clears v rho y hy];unfold Q.num;grobner
    _ = _ := by grobner

theorem Q.eval_add (x y : Q) (hx : x.d≠0) (hy : y.d≠0) :
    (x.add y).eval v rho=x.eval v rho+y.eval v rho := by
  have hz : (x.add y).d≠0 := fun z=>(Rat.mul_eq_zero.mp z).elim hx hy
  apply cancel (v.agrees _ hz).1
  rw [Q.clears v rho _ hz]
  change _=(x.eval v rho+y.eval v rho)*v.incl.map (x.d*y.d)
  unfold Q.num Q.add
  simp only [v.incl.add,v.incl.mul]
  have a:=Q.clears v rho x hx
  have b:=Q.clears v rho y hy
  unfold Q.num at a b
  grobner

private theorem map_two : v.incl.map 2=(2:K) := by
  calc _=v.incl.map ((2:Int):Rat) := congrArg _ (by decide)
       _=((2:Int):K) := v.incl.int 2
       _=2 := by grobner

theorem Q.eval_mul (root : rho^2=2) (x y : Q) (hx : x.d≠0) (hy : y.d≠0) :
    (x.mul y).eval v rho=x.eval v rho*y.eval v rho := by
  have hz : (x.mul y).d≠0 := fun z=>(Rat.mul_eq_zero.mp z).elim hx hy
  apply cancel (v.agrees _ hz).1
  rw [Q.clears v rho _ hz]
  change _=(x.eval v rho*y.eval v rho)*v.incl.map (x.d*y.d)
  unfold Q.num Q.mul
  simp only [v.incl.add,v.incl.mul,map_two v]
  have a:=Q.clears v rho x hx
  have b:=Q.clears v rho y hy
  unfold Q.num at a b
  grobner

theorem Q.eval_conjugate (x : Q) (hx : x.d≠0) :
    x.conjugate.eval v rho=x.eval v (-rho) := by
  apply cancel (v.agrees _ hx).1
  rw [show x.d=x.conjugate.d from rfl,Q.clears v rho x.conjugate hx]
  change _=x.eval v (-rho)*v.incl.map x.d
  rw [Q.clears v (-rho) x hx]
  unfold Q.num Q.conjugate
  have ng : v.incl.map (-x.b)= -v.incl.map x.b := by
    have e:=v.incl.add (-x.b) x.b
    rw [Rat.neg_add_cancel,v.incl.zero] at e
    grobner
  rw [ng];grobner

theorem Q.eval_constant (a b : Rat) : (Q.constant a b).eval v rho=v.incl.map a+v.incl.map b*rho := by
  change _/v.incl.map 1=_;rw [v.incl.one,Field.div_eq_mul_inv,Field.inv_one,Semiring.mul_one];rfl

theorem Q.eval_rational (a d : Rat) (den : d≠0) :
    (Q.mk a 0 d).eval v rho=v.incl.map (a/d) := by
  apply cancel (v.agrees _ den).1
  rw [Q.clears v rho _ den,←v.incl.mul,Rat.div_mul_cancel den]
  unfold Q.num;rw [v.incl.zero,Semiring.zero_mul,AddCommMonoid.add_zero]

end ProjectionFibres.Comparison
