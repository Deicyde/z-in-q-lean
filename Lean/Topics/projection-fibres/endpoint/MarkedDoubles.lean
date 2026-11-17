import SexticOrder

namespace ProjectionFibres.Marked
open StructuralReduction BinaryQuartic ProgressionWitnesses.SingleContact

private theorem twoPrime : Prime 2 := prime_of_finite (by decide) (by decide)
abbrev v := primeOrder 2 twoPrime

def onCurve (n x y : Rat) : Prop := y^2=x*(x-n)*(x+3*n)

/-- The usual tangent on the full two-torsion model. -/
def double (n : Rat) (p : Rat × Rat) : Rat × Rat :=
  let (x,y):=p
  let m:=(3*x^2+4*n*x-3*n^2)/(2*y)
  let X:=m^2-2*n-2*x
  (X,m*(x-X)-y)

private theorem tangent {n x y m : Rat} (c : onCurve n x y)
    (line : m*(2*y)=3*x^2+4*n*x-3*n^2) :
    let X:=m^2-2*n-2*x
    onCurve n X (m*(x-X)-y) ∧ 4*y^2*X=(x^2+3*n^2)^2 := by
  unfold onCurve at *
  dsimp
  constructor <;> grobner

private theorem dominates {a b : Rat} (a0 : a≠0) (b0 : b≠0) (lt : v.ord a<v.ord b) :
    a+b≠0 ∧ v.ord (a+b)=v.ord a := by
  obtain ⟨nz,ord⟩:=v.addUnequal a b a0 b0 (Int.ne_of_lt lt)
  exact ⟨nz,ord.trans (Int.min_eq_left (by omega))⟩

/-- A negative 2-adic order drops by exactly two at every doubling. -/
theorem double_depth {n x y : Rat} (n0 : n≠0) (integral : 0≤v.ord n)
    (c : onCurve n x y) (x0 : x≠0) (negative : v.ord x<0) :
    onCurve n (double n (x,y)).1 (double n (x,y)).2 ∧
    (double n (x,y)).1≠0 ∧ v.ord (double n (x,y)).1=v.ord x-2 := by
  have o3 : v.ord 3=0 := order_nat_unit (n:=3) twoPrime (by decide)
  have o4 : v.ord 4=2 := by
    have h:=v.mul 2 2 (by decide) (by decide)
    have one : v.ord 2=1 := order_prime twoPrime
    rw [one] at h
    rw [show (4:Rat)=2*2 by decide +kernel]
    exact h
  have three : ∀ {b : Rat}, b≠0 → v.ord (3*b)=v.ord b := by
    intro b nz
    rw [v.mul _ _ (by decide) nz,o3,Int.zero_add]
  have m1 : x-n≠0 ∧ v.ord (x-n)=v.ord x := by
    rw [Rat.sub_eq_add_neg]
    apply dominates x0 (by grind)
    rw [v.neg _ n0];omega
  have m2:=dominates (b:=3*n) x0 (by grind [Rat.mul_eq_zero]) (by rw [three n0];omega)
  have ynz : y≠0 := by
    intro h
    have rhs : x*(x-n)*(x+3*n)≠0 := by grind [Rat.mul_eq_zero]
    exact rhs (by rw [←c,h];decide)
  obtain ⟨xn,ox⟩:=power_order v x0 2
  obtain ⟨nn,on⟩:=power_order v n0 2
  obtain ⟨un,ou⟩:=dominates (b:=3*n^2) xn (by grind [Rat.mul_eq_zero]) (by rw [three nn,ox,on];omega)
  obtain ⟨sn,os⟩:=power_order v un 2
  let m:=(3*x^2+4*n*x-3*n^2)/(2*y)
  have slope : m*(2*y)=3*x^2+4*n*x-3*n^2 := Rat.div_mul_cancel (by grind [Rat.mul_eq_zero])
  obtain ⟨next,identity⟩:=tangent c slope
  let X:=m^2-2*n-2*x
  change onCurve n X _ ∧ X≠0 ∧ v.ord X=_
  have X0 : X≠0 := fun z=>sn (by rw [←identity,show m^2-2*n-2*x=0 from z,Rat.mul_zero])
  refine ⟨next,X0,?_⟩
  have y2 : y^2≠0 := (power_order v ynz 2).1
  have oy : v.ord (y^2)=3*v.ord x := by
    rw [c,v.mul _ _ (by grind [Rat.mul_eq_zero]) m2.1,v.mul _ _ x0 m1.1,m1.2,m2.2];omega
  change 4*y^2*X=_ at identity
  have eq := congrArg v.ord identity
  rw [v.mul _ _ (by grind [Rat.mul_eq_zero]) X0,v.mul _ _ (by decide) y2,o4,oy,os,ou,ox] at eq
  omega

def beta : Rat := 412690661369
def twist : Rat := 66596377080407144678843471
def U : Rat := 508306873/40
def V : Rat := 1016345177/40
def W : Rat := 8666503888749/40
def base : Rat × Rat := (beta*U^2,beta*U*V*W)

theorem marked_base : onCurve twist base.1 base.2 ∧ base.1-twist=W^2 ∧
    base.1+3*twist=beta*V^2 := by unfold onCurve;decide +kernel

private theorem initial : v.ord base.1= -6 := by
  have b : v.ord beta=0 := order_nat_unit (n:=412690661369) twoPrime (by decide)
  have u : v.ord 508306873=0 := order_nat_unit (n:=508306873) twoPrime (by decide)
  have forty : v.ord 40=3 := by decide +kernel
  have quot:=v.div 508306873 40 (by decide) (by decide)
  rw [u,forty] at quot
  change v.ord (beta*U^2)=_
  rw [v.mul _ _ (by decide +kernel) (by decide +kernel),(power_order v (a:=U) (by decide +kernel) 2).2,b]
  change v.ord U= -3 at quot
  omega

def orbit : Nat → Rat × Rat
  | 0=>base
  | k+1=>double twist (orbit k)

/-- The tangent iterates are genuine rational points with pairwise distinct abscissas. -/
theorem orbit_depth (k : Nat) : onCurve twist (orbit k).1 (orbit k).2 ∧
    (orbit k).1≠0 ∧ order 2 (orbit k).1= -6-2*(k:Int) := by
  induction k with
  | zero=>exact ⟨marked_base.1,by decide +kernel,initial⟩
  | succ k ih=>
    have unit : v.ord twist=0 := order_nat_unit (n:=66596377080407144678843471) twoPrime (by decide)
    have last : v.ord (orbit k).1= -6-2*(k:Int) := ih.2.2
    obtain ⟨c,z,e⟩:=double_depth (by decide : twist≠0) (by omega) ih.1 ih.2.1 (by omega)
    refine ⟨c,z,?_⟩
    change v.ord (double twist ((orbit k).1,(orbit k).2)).1=_
    rw [e,last];omega

theorem different_abscissas {i j : Nat} (h : (orbit i).1=(orbit j).1) : i=j := by
  have e:=congrArg (order 2) h
  rw [(orbit_depth i).2.2,(orbit_depth j).2.2] at e
  omega

#print axioms double_depth
#print axioms marked_base
#print axioms orbit_depth
#print axioms different_abscissas
end ProjectionFibres.Marked
