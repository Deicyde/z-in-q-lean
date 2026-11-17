import PairResidues

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} [NeZero p]

def IntegralPair (p : Nat) [NeZero p] (x : Q2) := ∃ r : Residues p, PairRed p x r

theorem IntegralPair.mul {a b : Q2} (h : IntegralPair p a) (k : IntegralPair p b) :
    IntegralPair p (times a b) := by
  obtain ⟨r,hr⟩:=h
  obtain ⟨s,hs⟩:=k
  exact ⟨mulR r s,hr.mul hs⟩

theorem PairRed.zero_mul {a b : Q2} (h : PairRed p a (0,0)) (k : IntegralPair p b) :
    PairRed p (times a b) (0,0) := by
  obtain ⟨s,hs⟩:=k
  simpa [mulR,Semiring.mul_zero,Semiring.zero_mul,AddCommMonoid.zero_add] using h.mul hs

theorem PairRed.one_mul {a b : Q2} (h : PairRed p a (1,0)) (k : PairRed p b (1,0)) :
    PairRed p (times a b) (1,0) := by
  simpa [mulR,Semiring.mul_zero,Semiring.one_mul,Semiring.zero_mul,AddCommMonoid.add_zero] using h.mul k

theorem PairRed.one_plus {a : Q2} (h : PairRed p a (0,0)) :
    PairRed p (plus (1,0) a) (1,0) := by
  simpa [addR,AddCommMonoid.add_zero] using pairOne.add h

private theorem one_plus_tail {q a : Q2} (h : PairRed p q (0,0)) (k : IntegralPair p a) :
    PairRed p (plus (1,0) (times (sq q) a)) (1,0) :=
  ((h.zero_mul ⟨_,h⟩).zero_mul k).one_plus

/-- The cleared division-polynomial identity produces a principal unit on the
actual rational pair. Both q and q/m reduce coefficientwise to zero. -/
theorem even_multiplier {q h A B y : Q2} {m : Rat} (hp : 1<p)
    (q0 : PairRed p q (0,0)) (h0 : PairRed p h (0,0)) (split : q=scale m h)
    (aInt : IntegralPair p A) (bInt : IntegralPair p B)
    (value : times y (plus (1,0) (times (sq q) A))=
      times q (plus (m^2,0) (times (sq q) B))) :
    ∃ u, PairRed p u (1,0) ∧ y=times (scale (m^2) q) u := by
  let a:=plus (1,0) (times (sq q) A)
  let b:=plus (1,0) (times (sq h) B)
  have ar : PairRed p a (1,0) := one_plus_tail q0 aInt
  have br : PairRed p b (1,0) := one_plus_tail h0 bInt
  obtain ⟨nz,ir⟩:=ar.invOne hp
  have rhs : times q (plus (m^2,0) (times (sq q) B))=times (scale (m^2) q) b := by
    rw [split]
    apply Prod.ext <;> dsimp [b,scale,plus,sq,times] <;> grobner
  have e : times y a=times (scale (m^2) q) b := value.trans rhs
  refine ⟨times b (inverse a),br.one_mul ir,?_⟩
  calc y=times (times y a) (inverse a) := by rw [tm_assoc,inverse_clears nz,tm_one]
       _=times (scale (m^2) q) (times b (inverse a)) := by rw [e,tm_assoc]

/-- Integer polynomials, in increasing coefficient order. -/
def eval (l : List Int) (z : Q2) : Q2 :=
  match l with
  | [] => (0,0)
  | a::t => plus ((a:Rat),0) (times z (eval t z))

theorem eval_integral (l : List Int) {z : Q2} (hz : IntegralPair p z) :
    IntegralPair p (eval l z) := by
  obtain ⟨s,hs⟩:=hz
  induction l with
  | nil => exact ⟨(0,0),pairZero⟩
  | cons a l ih =>
    obtain ⟨r,hr⟩:=ih
    have ar : PairRed p ((a:Rat),0) ((a:Fin p),0) := ⟨redInt a,redZero⟩
    exact ⟨_,ar.add (hs.mul hr)⟩

/-- Specialization to A=1+z·a(z), B=m²+z·b(z), z=Dq². The
integer coefficient lists and the actual integral D suffice for every tail. -/
theorem binary_multiplier (hp : 1<p) (m : Int) (a b : List Int) {q h D y : Q2}
    (q0 : PairRed p q (0,0)) (h0 : PairRed p h (0,0)) (split : q=scale (m:Rat) h)
    (Dint : IntegralPair p D)
    (value : let z:=times D (sq q)
      times y (eval (1::a) z)=times q (eval ((m*m)::b) z)) :
    ∃ u, PairRed p u (1,0) ∧ y=times (scale ((m:Rat)^2) q) u := by
  let z:=times D (sq q)
  have qi : IntegralPair p q := ⟨_,q0⟩
  have zi : IntegralPair p z := Dint.mul (qi.mul qi)
  apply even_multiplier hp q0 h0 split (Dint.mul (eval_integral a zi)) (Dint.mul (eval_integral b zi))
  have rotate (c w : Q2) :
      plus c (times z w)=plus c (times (sq q) (times D w)) := by
    apply Prod.ext <;> dsimp [z,plus,sq,times] <;> grobner
  change times y (plus (1,0) (times z (eval a z)))=
    times q (plus ((↑(m*m):Rat),0) (times z (eval b z))) at value
  rw [rotate,rotate] at value
  have cast : (↑(m*m):Rat)=(m:Rat)^2 := by rw [Rat.intCast_mul]; grobner
  rw [cast] at value
  exact value

theorem compose {q r s a b : Q2} {m n : Rat} (u : PairRed p a (1,0)) (v : PairRed p b (1,0))
    (first : r=times (scale (m^2) q) a) (second : s=times (scale (n^2) r) b) :
    PairRed p (times a b) (1,0) ∧ s=times (scale ((m*n)^2) q) (times a b) := by
  refine ⟨u.one_mul v,?_⟩
  rw [second,first]
  apply Prod.ext <;> dsimp [times,scale] <;> grobner

#print axioms even_multiplier
#print axioms binary_multiplier
#print axioms compose
end Prime23
