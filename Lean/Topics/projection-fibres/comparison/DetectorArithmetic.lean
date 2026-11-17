import QuadraticValues
namespace ProjectionFibres.Comparison
open StructuralReduction Lean.Grind WitnessTransfer
attribute [local instance] Semiring.natCast Ring.intCast

def C : Q := Q.constant 102 51
def one : Q := Q.constant 1 0
def cy (a : Q) := C.mul (a.mul a)
def boundEq (y z : Q) := (z.mul (one.add (cy y))).same (cy y)
def factorEq (z q f : Q) := f.same (one.add (q.mul (z.mul z)))
def productEq (a b r : Q) := r.same (a.mul b)
def traceEq (a t : Q) := (t.mul (a.mul a.conjugate)).same (a.add a.conjugate)

theorem Q.nz_add {x y : Q} (a : x.d≠0) (b : y.d≠0) : (x.add y).d≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim a b
theorem Q.nz_mul {x y : Q} (a : x.d≠0) (b : y.d≠0) : (x.mul y).d≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim a b

variable {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K) (r : K)
theorem eval_one : one.eval w r=1 := by
  rw [one,Q.eval_constant,w.incl.one,w.incl.zero];grobner
theorem eval_cy (root : r^2=2) {y : Q} (uy : y.d≠0) :
    (cy y).eval w r=scaled (C.eval w r) (y.eval w r) := by
  rw [cy,Q.eval_mul w r root _ _ (by decide) (Q.nz_mul uy uy),Q.eval_mul w r root _ _ uy uy]
  rfl

theorem evaluatedBound (root : r^2=2) {y z : Q} (id : boundEq y z)
    (uy : y.d≠0) (uz : z.d≠0) :
    1+scaled (C.eval w r) (y.eval w r)≠0 ∧ z.eval w r=bounded (C.eval w r) (y.eval w r) := by
  have nz : (cy y).d≠0:=Q.nz_mul (by decide : C.d≠0) (Q.nz_mul uy uy)
  have den := Q.nz_add (by decide : one.d≠0) nz
  have eq:=Q.eval_same w r id (Q.nz_mul uz den) nz
  rw [Q.eval_mul w r root _ _ uz den,Q.eval_add w r _ _ (by decide) nz,eval_one,eval_cy w r root uy] at eq
  have reg : 1+scaled (C.eval w r) (y.eval w r)≠0 := by
    intro bad
    rw [bad,Semiring.mul_zero] at eq
    rw [←eq,AddCommMonoid.add_zero] at bad
    exact Field.zero_ne_one bad.symm
  have divide {a b d : K} (nd : d≠0) (relation : a*d=b) : a=b/d := by
    calc a=a*(d*d⁻¹) := by rw [Field.mul_inv_cancel nd,Semiring.mul_one]
         _=(a*d)*d⁻¹ := by grobner
         _=b/d := by rw [relation,Field.div_eq_mul_inv]
  exact ⟨reg,divide reg eq⟩

theorem evaluatedFactor (root : r^2=2) {z q f : Q} (id : factorEq z q f)
    (uz : z.d≠0) (uq : q.d≠0) (uf : f.d≠0) :
    f.eval w r=1+q.eval w r*((z.eval w r)*(z.eval w r)) := by
  have zz:=Q.nz_mul uz uz
  have u:=Q.nz_mul uq zz
  have eq:=Q.eval_same w r id uf (Q.nz_add (by decide : one.d≠0) u)
  rw [Q.eval_add w r _ _ (by decide) u,eval_one,Q.eval_mul w r root _ _ uq zz,Q.eval_mul w r root _ _ uz uz] at eq
  exact eq

theorem evaluatedProduct (root : r^2=2) {a b c : Q} (id : productEq a b c)
    (ua : a.d≠0) (ub : b.d≠0) (uc : c.d≠0) :
    c.eval w r=a.eval w r*b.eval w r := by
  exact (Q.eval_same w r id uc (Q.nz_mul ua ub)).trans (Q.eval_mul w r root a b ua ub)

theorem evaluatedTrace (root : r^2=2) {a t : Q} (id : traceEq a t)
    (ua : a.d≠0) (ut : t.d≠0) :
    t.eval w r*(a.eval w r*a.eval w (-r))=a.eval w r+a.eval w (-r) := by
  have ca : a.conjugate.d≠0:=ua
  have u:=Q.nz_mul ua ca
  have eq:=Q.eval_same w r id (Q.nz_mul ut u) (Q.nz_add ua ca)
  rw [Q.eval_mul w r root _ _ ut u,Q.eval_mul w r root _ _ ua ca,Q.eval_add w r _ _ ua ca,
      Q.eval_conjugate w r a ua] at eq
  exact eq

end ProjectionFibres.Comparison
