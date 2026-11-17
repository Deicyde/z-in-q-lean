import BadChartPrimes

namespace EllipticHeight.Primitive
open QuadraticInt Lean.Grind
attribute [local instance] Ring.intCast Semiring.natCast
local infixl:65 " +₂ " => plus
local infixl:70 " *₂ " => mul

private def minus (a b : R) : R := (a.1-b.1,a.2-b.2)

private theorem swap {a b : R} (p : coprime a b) : coprime b a := by
  obtain ⟨u,v,h⟩:=p
  exact ⟨v,u, (show b*₂v+₂a*₂u=a*₂u+₂b*₂v by apply Prod.ext <;> dsimp [plus,mul] <;> omega).trans h⟩

/-- Multiplication of two Bézout identities with the same first argument. -/
private theorem times_right {a b c : R} (p : coprime a b) (q : coprime a c) :
    coprime a (b*₂c) := by
  obtain ⟨u,v,h⟩:=p
  obtain ⟨w,z,k⟩:=q
  refine ⟨u*₂(a*₂w+₂c*₂z) +₂ (b*₂v)*₂w, v*₂z, ?_⟩
  calc _ = (a*₂u+₂b*₂v)*₂(a*₂w+₂c*₂z) := by apply Prod.ext <;> dsimp [mul,plus] <;> grobner
       _ = _ := by rw [h,k]; rfl

private theorem factor_right {a b f : R} (p : coprime a b) (d : divides f b) : coprime a f := by
  obtain ⟨c,rfl⟩:=d
  obtain ⟨u,v,h⟩:=p
  exact ⟨u,c*₂v,(show a*₂u+₂f*₂(c*₂v)=a*₂u+₂(f*₂c)*₂v by
    apply Prod.ext <;> dsimp [plus,mul] <;> grobner).trans h⟩

private theorem shear {a b : R} (p : coprime a b) (k : R) : coprime (a+₂b*₂k) b := by
  obtain ⟨u,v,h⟩:=p
  exact ⟨u,minus v (k*₂u),(show (a+₂b*₂k)*₂u+₂b*₂minus v (k*₂u)=a*₂u+₂b*₂v by
    apply Prod.ext <;> dsimp [plus,mul,minus] <;> grobner).trans h⟩

private theorem subtract_right {a b c : R} (p : coprime a b) (eq : b=a+₂c) : coprime a c := by
  obtain ⟨u,v,h⟩:=p
  rw [eq] at h
  exact ⟨u+₂v,v,(show a*₂(u+₂v)+₂c*₂v=a*₂u+₂(a+₂c)*₂v by
    apply Prod.ext <;> dsimp [plus,mul] <;> grobner).trans h⟩

private theorem square_left {a b : R} (h : coprime a b) : coprime (sq a) b :=
  swap (times_right (swap h) (swap h))

private theorem square_right {a b : R} (h : coprime a b) : coprime a (sq b) :=
  times_right h h

/-- Inverting the nonzero residue of a at (3−√2) lifts to an integral
Bézout identity between a and 3−√2. -/
theorem bezout_delta {a : R} (unit : ¬divides delta a) : coprime a delta := by
  let q : Int := a.1+3*a.2
  have nz : (q:Fin 7)≠0 := fun h=>unit ((delta_divides a).mpr h)
  have fermat : ∀ t:Fin 7, t≠0 → t^6=1 := by decide
  have f:=fermat (q:Fin 7) nz
  let u : R := (q^5,0)
  let rem : R := minus (1,0) (a*₂u)
  have rem_eq : rem.1+3*rem.2=1-q^6 := by dsimp [rem,minus,mul,u,q]; grobner
  have dz : divides delta rem := by
    apply (delta_divides rem).mpr
    change ((rem.1+3*rem.2:Int):Fin 7)=0
    rw [rem_eq,Ring.intCast_sub,Ring.intCast_pow,f]; decide
  obtain ⟨v,h⟩:=dz
  refine ⟨u,v,?_⟩
  rw [←h]
  apply Prod.ext <;> dsimp [rem,minus,plus,mul] <;> grobner

def term (x y : R) := sq x +₂ sq delta *₂ sq y
def other (x y : R) := minus (sq x) (sq delta *₂ sq y)
def top (x y : R) := sq (term x y)
def bottom (x y : R) := (((4,0):R)*₂x)*₂y*₂other x y

/-- The chart and its doubles stay in this state without removing any common factor. -/
def State (x y : R) := coprime x y ∧ divides rho y ∧ coprime x delta

/-- A single raw homogeneous duplication over Z[√2], including both bad primes.
The first conclusion is exactly ∃ u v, F*u+G*v=1 in the quadratic integer ring. -/
theorem step {x y : R} (state : State x y) : State (top x y) (bottom x y) := by
  obtain ⟨xy,dy,xd⟩:=state
  let D:=sq delta
  let w:=term x y
  have wy : coprime w y := by
    have h : w=sq x+₂y*₂(D*₂y) := by
      apply Prod.ext <;> dsimp [w,term,D,sq,plus,mul] <;> grobner
    rw [h]; exact shear (square_left xy) _
  have wx : coprime w x := by
    have h : w=D*₂sq y+₂x*₂x := by
      apply Prod.ext <;> dsimp [w,term,D,sq,plus,mul] <;> grobner
    rw [h]
    exact shear (swap (times_right (square_right xd) (square_right xy))) _
  have wd : coprime w delta := by
    have h : w=sq x+₂delta*₂(delta*₂sq y) := by
      apply Prod.ext <;> dsimp [w,term,sq,plus,mul] <;> grobner
    rw [h]; exact shear (square_left xd) _
  have wr := factor_right wy dy
  have w2 : coprime w ((2,0):R) := square_right wr
  have w4 : coprime w ((4,0):R) := square_right w2
  have wo : coprime w (other x y) := by
    apply subtract_right (times_right w2 (square_right wx))
    apply Prod.ext <;> dsimp [w,term,other,minus,sq,plus,mul] <;> grobner
  have pr : coprime (top x y) (bottom x y) :=
    square_left (times_right (times_right (times_right w4 wx) wy) wo)
  have db : divides rho (bottom x y) := by
    refine ⟨(((0,2):R)*₂x)*₂y*₂other x y,?_⟩
    unfold bottom
    generalize other x y = z
    apply Prod.ext <;> dsimp [rho,mul] <;> grobner
  exact ⟨pr,db,square_left wd⟩

def iterate : Nat → R → R → R×R
  | 0,x,y => (x,y)
  | n+1,x,y => let p:=iterate n x y; (top p.1 p.2,bottom p.1 p.2)

theorem iterate_state (n : Nat) {x y : R} (s : State x y) :
    State (iterate n x y).1 (iterate n x y).2 := by
  induction n with
  | zero => exact s
  | succ n ih => exact step ih

theorem start {a b : R} (pr : coprime a b) (denom : divides rho b)
    (num : ¬divides delta a) : State (sq a) (sq b) := by
  obtain ⟨u,h⟩:=denom
  have d : divides rho (sq b) := by
    refine ⟨u*₂b,?_⟩
    conv => lhs; unfold sq; lhs; rw [h]
    apply Prod.ext <;> dsimp [mul,rho] <;> grobner
  exact ⟨square_right (square_left pr),d,square_left (bezout_delta num)⟩

/-- Every primitive weighted chart, and every raw doubled pair obtained from it,
has an integral Bézout identity. No restriction on the iteration count. -/
theorem chart_iterate {a b c : R} (pr : coprime a b) (h : chart a b c) (n : Nat) :
    coprime (iterate n (sq a) (sq b)).1 (iterate n (sq a) (sq b)).2 :=
  (iterate_state n (start pr (dyadic_denominator h) (no_seven_numerator pr h))).1

/-- The raw denominator on a signed chart is precisely the square of 2abc. -/
theorem chart_denominator_square {a b c : R} (h : chart a b c) :
    bottom (sq a) (sq b)=sq ((((2,0):R)*₂a)*₂b*₂c) := by
  let t:=sq delta *₂ fourth b
  have q : sq (delta*₂sq b)=t := by
    apply Prod.ext <;> dsimp [t,delta,sq,fourth,mul] <;> grobner
  change plus (sq c) (sq (delta*₂sq b))=fourth a at h
  rw [q] at h
  have sub : other (sq a) (sq b)=sq c := by
    change minus (fourth a) t=sq c
    rw [←h]
    apply Prod.ext <;> dsimp [minus,plus] <;> omega
  unfold bottom
  rw [sub]
  apply Prod.ext <;> dsimp [sq,mul] <;> grobner

#print axioms bezout_delta
#print axioms step
#print axioms iterate_state
#print axioms start
#print axioms chart_iterate
#print axioms chart_denominator_square
end EllipticHeight.Primitive
