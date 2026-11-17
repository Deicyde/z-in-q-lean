import IntegralJet
import ContactRadicals

namespace WitnessTransfer.Local
open Lean.Grind IndependentIndices
attribute [local instance] Semiring.natCast Ring.intCast
variable {O : Type} [CommRing O]

/-- x,y are the numerator and reference parameters. nx and ry are the unit
factors J(x)/x and J_ref(y)/y, including at the zero numerator. -/
structure Side (O : Type) [CommRing O] where
  x : O
  y : O
  nx : O
  ry : O
  nx_unit : unit nx
  ry_unit : unit ry
  regular : ∀ a b : O,y*a=y*b→a=b

def ratio (s : Side O) (l : O) := s.y*s.ry*l=s.x*s.nx

structure Tangent (s : Side O) (m a : Int) where
  rx : O
  ry : O
  same : s.x*((m:O)+s.x*rx)=s.y*((a:O)+s.y*ry)

private theorem integral_on_unit (s : Side O) {a m} (t : Tangent s m a)
    (hu : unit ((m:O)+s.x*t.rx)) : ∃ l : O,ratio s l := by
  obtain ⟨v,hv⟩:=hu
  obtain ⟨u,hu⟩:=s.ry_unit
  have xeq : s.x=s.y*(((a:O)+s.y*t.ry)*v) := by
    calc _=s.x*(((m:O)+s.x*t.rx)*v) := by rw [CommSemiring.mul_comm _ v,hv];grobner
         _=(s.x*((m:O)+s.x*t.rx))*v := (Semiring.mul_assoc ..).symm
         _=_ := by rw [t.same,Semiring.mul_assoc]
  refine ⟨(((a:O)+s.y*t.ry)*v)*s.nx*u,?_⟩
  unfold ratio
  rw [xeq]
  calc _=s.y*(((a:O)+s.y*t.ry)*v)*s.nx*(u*s.ry) := by grobner
       _=_ := by rw [hu];grobner

def crossEq (s t : Side O) (delta : O) :=
    (s.x*s.nx)*(t.y*t.ry)-(t.x*t.nx)*(s.y*s.ry)=(s.y*s.ry)*(t.y*t.ry)*delta

private theorem carry (s t : Side O) {l delta : O} (left : ratio s l)
    (cross : crossEq s t delta) : ratio t (l-delta) := by
  unfold ratio at left ⊢
  unfold crossEq at cross
  rw [← left] at cross
  have swap {A : Type} [CommRing A] (d e x l r : A)
      (h : d*l*e-x*d=d*e*r) : d*(e*(l-r))=d*x := by grobner
  have e:=swap _ _ _ _ _ cross
  apply cancel_unit s.ry_unit
  apply s.regular
  simpa only [Semiring.mul_assoc] using e

/-- A residue field and the local-ring unit test. It may be split or inert. -/
structure Place (O k : Type) [CommRing O] [Field k] where
  residue : RingMap O k
  liftUnit : ∀ a : O,residue.map a≠0→unit a
  two : (2:k)≠0

theorem two_sides {k : Type} [Field k] (p : Place O k) (s t : Side O) (m u n : Int)
    (sx : p.residue.map s.x=0) (tx : p.residue.map t.x=0)
    (first : Tangent s m (2*u)) (second : Tangent t (m-2) (2*(u-n)))
    (delta : O) (cross : crossEq s t delta) :
    ∃ l l' : O,ratio s l ∧ ratio t l' ∧ l-l'=delta := by
  have unitSide (side : Side O) (a h : Int) (obs : Tangent side a h)
      (zero : p.residue.map side.x=0) (nz : (a:k)≠0) : ∃ l,ratio side l := by
    apply integral_on_unit side obs
    apply p.liftUnit
    rw [p.residue.add,p.residue.mul,p.residue.int,zero]
    intro h0;apply nz;grobner
  by_cases nz : (m:k)=0
  · have alt : ((m-2:Int):k)≠0 := by
      rw [Ring.intCast_sub,Ring.intCast_ofNat,nz];intro eq;exact p.two (by grobner)
    obtain ⟨r,hr⟩:=unitSide t _ _ second tx alt
    have rev : crossEq t s (-delta) := by
      unfold crossEq at cross ⊢
      have reverse {A : Type} [CommRing A] (a b c d v : A)
          (h : a*d-b*c=c*d*v) : b*c-a*d=d*c*(-v) := by grobner
      exact reverse _ _ _ _ _ cross
    exact ⟨r-(-delta),r,carry t s hr rev,hr,by grobner⟩
  · obtain ⟨l,hl⟩:=unitSide s _ _ first sx nz
    exact ⟨l,l-delta,hl,carry s t hl cross,by grobner⟩

theorem parameter_depth (s : Side O) {l : O} (div : ratio s l) : ∃ z : O,s.x=s.y*z := by
  obtain ⟨v,hv⟩:=s.nx_unit
  refine ⟨s.ry*l*v,?_⟩
  calc
    _=s.x*(s.nx*v) := by rw [CommSemiring.mul_comm _ v,hv];grobner
    _=(s.x*s.nx)*v := (Semiring.mul_assoc ..).symm
    _=_ := by rw [← div];grobner

/-- Two evaluations at the same group multiple, before division by the reference.
Mixed reference charts contribute correction*y^(d+1). -/
structure AtMultiple (s : Side O) (m a : Int) (d : Nat) where
  value : O
  correction : O
  num : ∃ k : O,value-(m:O)*(s.x*s.nx)=s.x^(d+1)*k
  ref : ∃ k : O,value-(a:O)*(s.y*s.ry+s.y^(d+1)*correction)=s.y^(d+1)*k

/-- The residual has d powers of the reference left after exact cancellation
of the nonzero parameter, including at multipliers divisible by p. -/
theorem cancel_reference (s : Side O) {m a d} (v : AtMultiple s m a d) {l : O} (hl : ratio s l) :
    ∃ r : O,s.ry*((m:O)*l-(a:O))=s.y^d*r := by
  obtain ⟨t,ht⟩:=parameter_depth s hl
  obtain ⟨i,hi⟩:=v.num
  obtain ⟨j,hj⟩:=v.ref
  have eqn : (m:O)*(s.y*s.ry*l)+s.x^(d+1)*i=
      (a:O)*(s.y*s.ry+s.y^(d+1)*v.correction)+s.y^(d+1)*j := by
    rw [hl];grobner
  rw [ht,CommSemiring.mul_pow,Semiring.pow_succ s.y d] at eqn
  refine ⟨(a:O)*v.correction+j-t^(d+1)*i,s.regular _ _ ?_⟩
  have balance {A : Type} [CommRing A] (m a y v l yd z i j c : A)
      (h : m*(y*v*l)+(yd*y)*z*i=a*(y*v+(yd*y)*c)+(yd*y)*j) :
      y*(v*(m*l-a))=y*(yd*(a*c+j-z*i)) := by grobner
  exact balance _ _ _ _ _ _ _ _ _ _ eqn

end WitnessTransfer.Local
