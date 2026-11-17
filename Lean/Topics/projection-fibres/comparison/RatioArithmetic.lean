import DetectorArithmetic
import ContactResidues
namespace ProjectionFibres.Comparison
open StructuralReduction Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

def Q.sub (a b : Q) : Q := ⟨a.a*b.d-b.a*a.d,a.b*b.d-b.b*a.d,a.d*b.d⟩
def two : Q := Q.constant 2 0
def Q.lucas (a t y : Q) : Q :=
  let u:=a.sub two
  (((t.mul t).sub ((a.mul u).mul (t.mul y))).add ((u.mul y).mul (u.mul y))).sub one

theorem Q.nz_sub {x y : Q} (a : x.d≠0) (b : y.d≠0) : (x.sub y).d≠0 := fun z=>(Rat.mul_eq_zero.mp z).elim a b
variable {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K) (r : K)
theorem Q.eval_sub (a b : Q) (ua : a.d≠0) (ub : b.d≠0) :
    (a.sub b).eval w r=a.eval w r-b.eval w r := by
  have h:=(a.sub b).clears w r (Q.nz_sub ua ub)
  change (a.sub b).eval w r*w.incl.map (a.d*b.d)=_ at h
  rw [w.incl.mul] at h
  have aa:=a.clears w r ua
  have bb:=b.clears w r ub
  unfold Q.num Q.sub at h
  simp only [w.incl.sub,w.incl.mul] at h
  unfold Q.num at aa bb
  have t : ((a.sub b).eval w r-(a.eval w r-b.eval w r))*(w.incl.map a.d*w.incl.map b.d)=0 := by unfold Q.sub;grobner
  have dif:=(Field.of_mul_eq_zero t).resolve_right (w.product (w.agrees _ ua).1 (w.agrees _ ub).1).1
  grobner

theorem evaluatedDiff {a b y : Q} (eq : y.same (a.sub b)) (ua : a.d≠0) (ub : b.d≠0) (uy : y.d≠0) :
    y.eval w r=a.eval w r-b.eval w r :=
  (Q.eval_same w r eq uy (Q.nz_sub ua ub)).trans (Q.eval_sub w r a b ua ub)

theorem evaluatedLucas {a b c y : Q} (root : r^2=2) (eq : y.same (Q.lucas a b c))
    (ua : a.d≠0) (ub : b.d≠0) (uc : c.d≠0) (uy : y.d≠0) :
    y.eval w r=IndependentIndices.lucas (a.eval w r) (b.eval w r) (c.eval w r) := by
  have units : two.d≠0 := by decide
  have ounit : one.d≠0 := by decide
  have a2:=Q.nz_sub ua units
  have ab:=Q.nz_mul ua a2
  have prod:=Q.nz_mul ub uc
  have ua2:=Q.nz_mul a2 uc
  have U:=Q.nz_mul ab prod
  have V:=Q.nz_mul ub ub
  have E:=Q.nz_sub V U
  have S:=Q.nz_mul ua2 ua2
  have T:=Q.nz_add E S
  have ev:=Q.eval_same w r eq uy (Q.nz_sub T ounit)
  unfold Q.lucas at ev
  rw [Q.eval_sub w r _ _ T ounit,Q.eval_add w r _ _ E S,Q.eval_sub w r _ _ V U,
      Q.eval_mul w r root _ _ ub ub,Q.eval_mul w r root _ _ ab prod,Q.eval_mul w r root _ _ ua a2,
      Q.eval_mul w r root _ _ ub uc,Q.eval_mul w r root _ _ ua2 ua2,Q.eval_mul w r root _ _ a2 uc,
      Q.eval_sub w r _ _ ua units,eval_one] at ev
  have k : two.eval w r=2 := by
    rw [two,Q.eval_constant,w.incl.zero]
    have twoMap : w.incl.map 2=(2:K) := by
      calc _=w.incl.map ((2:Int):Rat) := congrArg _ (by decide)
           _=((2:Int):K) := w.incl.int 2
           _=2 := by grobner
    rw [twoMap];grobner
  rw [k] at ev
  unfold IndependentIndices.lucas;grobner

end ProjectionFibres.Comparison
