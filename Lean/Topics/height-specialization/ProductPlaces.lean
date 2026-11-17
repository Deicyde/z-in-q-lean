import ChordDepth
import GroupPoints

namespace HeightSpecialization
open Lean.Grind StructuralReduction ProjectionFibres WitnessTransfer
attribute [local instance] Semiring.natCast Ring.intCast

/-- If an odd multiple vanishes, no multiple can equal a point of exact order two. -/
theorem odd_annihilator {G : Type} [IntModule G] {P T : G} {n : Int}
    (odd : n%2=1) (vanish : n • P=0) (two : (2:Int) • T=0) (nonzero : T≠0)
    (m : Int) : m • P≠T := by
  intro eq
  have killed : n • T=0 := by rw [←eq, scalar_comm, vanish, IntModule.zsmul_zero]
  have n_eq : n=(n/2)*2+1 := by omega
  rw [n_eq, IntModule.add_zsmul, IntModule.mul_zsmul, two, IntModule.zsmul_zero,
    IntModule.one_zsmul, AddCommMonoid.zero_add] at killed
  exact nonzero killed

/-- At a unit coefficient the reductions of a pole and a zero lie respectively
at the identity and at the distinguished two-torsion point. -/
theorem common_sign {G : Type} [IntModule G] {P T : G} {n v : Fin 4 → Int}
    (odd : ∀ i, n i%2=1) (two : (2:Int) • T=0) (live : T≠0)
    (pole : ∀ i, v i<0 → n i • P=0) (zero : ∀ i, 0<v i → n i • P=T) :
    (∀ i, 0≤v i) ∨ (∀ i, v i≤0) := by
  classical
  by_cases h : ∃ i, v i<0
  · obtain ⟨i,hi⟩:=h
    right
    intro j
    exact Int.le_of_not_gt fun hj=>odd_annihilator (odd i) (pole i hi) two live (n j) (zero j hj)
  · left
    intro i
    exact Int.le_of_not_gt fun hi=>h ⟨i,hi⟩

def polePart (v : Int) := max 0 (-v)

theorem local_product_height (v : Fin 4 → Int) (same : (∀ i, 0≤v i) ∨ (∀ i, v i≤0)) :
    polePart (v 0+v 1+v 2+v 3)=polePart (v 0)+polePart (v 1)+polePart (v 2)+polePart (v 3) := by
  rcases same with h|h
  all_goals
    have h0:=h 0; have h1:=h 1; have h2:=h 2; have h3:=h 3
    unfold polePart
    omega

/-- At an odd place with v(D)=2 every affine double of nonzero abscissa
has nonpositive abscissa valuation on y²=x(x²−D). -/
theorem bad_double {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K)
    {D x y X : K} (d0 : D≠0) (dval : w.val D=2)
    (two : (2:K)≠0) (twoUnit : w.val (2:K)=0)
    (x0 : x≠0) (y0 : y≠0) (X0 : X≠0)
    (curve : y*y=x*(x*x-D)) (dup : (2*y)*(2*y)*X=(x*x+D)*(x*x+D)) :
    w.val X≤0 := by
  let c:=x*x-D
  let e:=x*x+D
  have xx:=(w.product x0 x0)
  have yy:=(w.product y0 y0)
  have ty:=(w.product two y0)
  have tty:=w.product ty.1 ty.1
  have left:=w.product tty.1 X0
  have cn : c≠0 := by
    intro h
    change x*x-D=0 at h
    exact yy.1 (by rw [curve,h,Semiring.mul_zero])
  have en : e≠0 := by
    intro h
    change x*x+D=0 at h
    exact left.1 (by rw [dup,h,Semiring.mul_zero])
  have cy:=congrArg w.val curve
  change w.val (y*y)=w.val (x*c) at cy
  rw [yy.2,w.mul _ _ x0 cn] at cy
  have eq:=congrArg w.val dup
  change w.val ((2*y)*(2*y)*X)=w.val (e*e) at eq
  rw [left.2,tty.2,ty.2,twoUnit,w.mul _ _ en en] at eq
  have dn : -D≠0 := by intro h; apply d0; grobner
  have diff : c=x*x+(-D) := by dsimp [c];grobner
  have nd:=w.neg D d0
  by_cases small : w.val (x*x)<2
  · have vc:=(w.dominates xx.1 (b:= -D) (fun _=>by omega)).2
    have ve:=(w.dominates xx.1 (b:= D) (fun _=>by omega)).2
    rw [←diff] at vc
    change w.val e=w.val (x*x) at ve
    have vx:=xx.2;omega
  by_cases big : 2<w.val (x*x)
  · have vc:=(w.dominates dn (b:=x*x) (fun _=>by omega)).2
    have ve:=(w.dominates d0 (b:=x*x) (fun _=>by omega)).2
    rw [AddCommMonoid.add_comm,←diff] at vc
    rw [AddCommMonoid.add_comm] at ve
    change w.val e=w.val D at ve
    have vx:=xx.2;omega
  have vx:=xx.2
  have dv : 2≤w.val c := deep_sub w (d:=2) (fun _=>by omega) (fun _=>by omega) cn
  have twoD:=w.product two d0
  have vc : 2<w.val c := by omega
  have ve:=(w.dominates twoD.1 (b:=c) (fun _=>by rw [twoD.2,twoUnit,dval];omega)).2
  have add : 2*D+c=e := by dsimp [c,e];grobner
  rw [add,twoD.2,twoUnit,dval] at ve
  omega

#print axioms odd_annihilator
#print axioms common_sign
#print axioms local_product_height
#print axioms bad_double
end HeightSpecialization
