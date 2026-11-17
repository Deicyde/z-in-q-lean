import QuadraticPivots

namespace ProjectionFibres

/-- The real coefficient of the signed elliptic row at address 513. -/
def curve (a b z w : Rat) : Rat :=
  1-11*a^2+24*a*b-22*b^2-9*a*z^2-18*a*w^2-36*b*z*w

def qnorm (a b : Rat) : Rat := a^2-2*b^2

theorem norm_of_curve {a b z w : Rat} (row : curve a b z w=0) : qnorm a b≠0 := by
  intro eq
  obtain ⟨rfl,rfl⟩ := (CircuitTransport.Quadratic.norm_zero_iff a b).mp eq
  unfold curve at row
  grobner

/-- Scalar quantities depending only on the coordinates which will be retained. -/
structure Data where
  L : Rat
  C : Rat
  A : Rat
  guard : Rat
  kappa : Rat
  t : Rat
  s : Rat
  j : Rat
  z : Rat
  w : Rat
  other : Rat → Rat → Prop

def pole (t s j B : Rat) : Rat :=
  j^2*(t^2-17*B)*(t^2+51*B)-(289-17*B)*(17*B-s^2)*(17*B+3*s^2)

def homogeneousPole (t s j N D : Rat) : Rat :=
  j^2*(t^2*D-17*N)*(t^2*D+51*N)*D-
    (289*D-17*N)*(17*N-s^2*D)*(17*N+3*s^2*D)

/-- Kept factored to make the reason for each denominator visible. -/
def Data.M (f : Data) (q : Rat) := f.A^2+f.C*f.L^2*q^2
def Data.K (f : Data) := f.A*f.L^2
def Data.N (f : Data) (q : Rat) := (f.M q)^2
def Data.D (f : Data) := f.C*f.K^2
def Data.h (f : Data) := f.guard*f.A

structure OldPoint (f : Data) (a b d m v i : Rat) : Prop where
  curveEq : curve a b f.z f.w=0
  others : f.other a b
  num : d*f.L=f.A
  reciprocal : m*d*f.L=d^2+f.C*(qnorm a b)^2
  corr : m^2=f.kappa*v*f.C
  sextic : pole f.t f.s f.j (f.kappa*v)=0
  inverse : i*f.guard=1

def NewPoint (f : Data) (x y : Rat) : Prop :=
  let a:=f.h*x
  let b:=f.h*y
  curve a b f.z f.w=0 ∧ f.other a b ∧
    homogeneousPole f.t f.s f.j (f.N (qnorm a b)) f.D=0

private theorem cancel {a b c : Rat} (nz : c≠0) (eq : a*c=b*c) : a=b := by grind

theorem homogeneous_identity (t s j N D B : Rat) (rel : B*D=N) :
    homogeneousPole t s j N D = D^3*pole t s j B := by
  rw [←rel]
  unfold pole homogeneousPole
  grobner

theorem scalar_denominator {f : Data} {a b d m v i : Rat}
    (p : OldPoint f a b d m v i) (L0 : f.L≠0) (C0 : f.C≠0) :
    f.A≠0 ∧ f.guard≠0 := by
  have q0:=norm_of_curve p.curveEq
  have first:=p.num
  have second:=p.reciprocal
  have inv:=p.inverse
  constructor
  · intro z
    have dz : d=0 := (Rat.mul_eq_zero.mp (first.trans z)).resolve_right L0
    rw [dz] at second
    have t : f.C*(qnorm a b)^2=0 := by grobner
    have tq:=(Rat.mul_eq_zero.mp t).resolve_left C0
    have ts : qnorm a b * qnorm a b=0 := by grobner
    exact (Rat.mul_eq_zero.mp ts).elim q0 q0
  · intro z
    rw [z,Rat.mul_zero] at inv
    exact (by decide : (0:Rat)≠1) inv

/-- Three short linear relations determine the three deleted coordinates. -/
theorem scalar_products {f : Data} {a b d m v i : Rat} (p : OldPoint f a b d m v i) :
    m*f.K=f.M (qnorm a b) ∧ (f.kappa*v)*f.D=f.N (qnorm a b) := by
  have first:=p.num
  have second:=p.reciprocal
  have corr:=p.corr
  have mult : m*f.K=f.M (qnorm a b) := by
    unfold Data.K Data.M
    calc
      _ = (m*d*f.L)*f.L^2 := by rw [←first];grobner
      _ = _ := by rw [second,←first];grobner
  refine ⟨mult,?_⟩
  unfold Data.N Data.D
  rw [←mult]
  calc
    _ = (f.kappa*v*f.C)*f.K^2 := by grobner
    _ = _ := by rw [←corr];grobner

theorem compress {f : Data} {a b d m v i : Rat} (p : OldPoint f a b d m v i)
    (L0 : f.L≠0) (C0 : f.C≠0) : NewPoint f (a/f.h) (b/f.h) := by
  obtain ⟨A0,g0⟩:=scalar_denominator p L0 C0
  have h0 : f.h≠0 := by unfold Data.h;grind [Rat.mul_eq_zero]
  have ha : f.h*(a/f.h)=a := by rw [Rat.mul_comm,Rat.div_mul_cancel h0]
  have hb : f.h*(b/f.h)=b := by rw [Rat.mul_comm,Rat.div_mul_cancel h0]
  unfold NewPoint
  rw [ha,hb]
  refine ⟨p.curveEq,p.others,?_⟩
  rw [homogeneous_identity _ _ _ _ _ _ (scalar_products p).2,p.sextic,Rat.mul_zero]

/-- The polynomial curve row itself excludes the entire exceptional divisor. -/
theorem open_of_new {f : Data} {x y : Rat} (p : NewPoint f x y) :
    f.A≠0 ∧ f.guard≠0 := by
  have row:=p.1
  have z : f.h≠0 := by
    intro eq
    rw [eq,Rat.zero_mul,Rat.zero_mul] at row
    unfold curve at row
    grobner
  constructor <;> intro eq <;> apply z <;> simp [Data.h,eq]

theorem lift {f : Data} {x y : Rat} (p : NewPoint f x y)
    (L0 : f.L≠0) (C0 : f.C≠0) (k0 : f.kappa≠0) :
    let a:=f.h*x
    let b:=f.h*y
    let q:=qnorm a b
    OldPoint f a b (f.A/f.L) (f.M q/f.K) ((f.N q/f.D)/f.kappa) f.guard⁻¹ := by
  obtain ⟨A0,g0⟩:=open_of_new p
  let a:=f.h*x
  let b:=f.h*y
  let q:=qnorm a b
  let d:=f.A/f.L
  let m:=f.M q/f.K
  let B:=f.N q/f.D
  have K0 : f.K≠0 := by unfold Data.K;grind [Rat.mul_eq_zero]
  have D0 : f.D≠0 := by unfold Data.D;grind [Rat.mul_eq_zero]
  have dL : d*f.L=f.A := Rat.div_mul_cancel L0
  have mK : m*f.K=f.M q := Rat.div_mul_cancel K0
  have BD : B*f.D=f.N q := Rat.div_mul_cancel D0
  have val : f.kappa*(B/f.kappa)=B := by rw [Rat.mul_comm,Rat.div_mul_cancel k0]
  change OldPoint f a b d m (B/f.kappa) _
  refine ⟨p.1,p.2.1,dL,?_,?_,?_,Rat.inv_mul_cancel _ g0⟩
  · apply cancel (show f.L^2≠0 by grind)
    calc
      _ = m*f.K := by unfold Data.K;rw [←dL];grobner
      _ = f.M q := mK
      _ = _ := by unfold Data.M;rw [←dL];change _=(d^2+f.C*q^2)*f.L^2;grobner
  · rw [val]
    apply cancel (show f.K^2≠0 by grind)
    calc
      _ = (m*f.K)^2 := by grobner
      _ = f.N q := by rw [mK];rfl
      _ = B*f.D := BD.symm
      _ = _ := by unfold Data.D;grobner
  · rw [val]
    have x0:=p.2.2
    change homogeneousPole f.t f.s f.j (f.N q) f.D=0 at x0
    rw [homogeneous_identity _ _ _ _ _ _ BD] at x0
    exact (Rat.mul_eq_zero.mp x0).resolve_left (by grind)

/-- Equivalence on each fixed base, including empty fibres. -/
theorem fibres_iff (f : Data) (L0 : f.L≠0) (C0 : f.C≠0) (k0 : f.kappa≠0) :
    (∃ a b d m v i, OldPoint f a b d m v i) ↔ ∃ x y, NewPoint f x y := by
  constructor
  · rintro ⟨a,b,d,m,v,i,p⟩
    exact ⟨a/f.h,b/f.h,compress p L0 C0⟩
  · rintro ⟨x,y,p⟩
    exact ⟨_,_,_,_,_,_,lift p L0 C0 k0⟩

#print axioms norm_of_curve
#print axioms scalar_denominator
#print axioms scalar_products
#print axioms homogeneous_identity
#print axioms open_of_new
#print axioms fibres_iff
end ProjectionFibres
