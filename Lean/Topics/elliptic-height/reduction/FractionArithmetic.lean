import ReducedPair
import ComparisonChart

namespace EllipticHeight.Reduction
open QuadraticInt
open PhysicalProjection.Comparison (Q2 times)

private theorem clear_coordinate (v : Rat) : v*(v.den:Rat)=(v.num:Rat) := by
  have rep:=Rat.num_divInt_den v
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at rep
  calc v*(v.den:Rat) = ((v.num:Rat)/(v.den:Rat))*(v.den:Rat) := by rw [rep]
       _ = _ := Rat.div_mul_cancel (fun eq=>v.den_nz (Rat.natCast_inj.mp eq))

private theorem cancel_scalar (u v k : Rat) (nz : k≠0) (h : u*k=v*k) : u=v := by
  have z : (u-v)*k=0 := by grobner
  have diff:=(Rat.mul_eq_zero.mp z).resolve_right nz
  grobner

private theorem cross_from_factors (g a b p d : R)
    (hn : p=mul g a) (hd : d=mul g b) : mul a d=mul p b := by
  rw [hn,hd]
  apply Prod.ext <;> dsimp [mul] <;> grobner

private theorem drop_common_denominator (h : Q2) (n : Nat) (p a b : R)
    (pos : 0<n) (hp : h.1*(n:Rat)=(p.1:Rat)) (hq : h.2*(n:Rat)=(p.2:Rat))
    (cross : mul a ((n:Int),0)=mul p b) :
    times h ((b.1:Rat),(b.2:Rat))=((a.1:Rat),(a.2:Rat)) := by
  have nz : (n:Rat)≠0 := fun eq=>Nat.ne_of_gt pos (Rat.natCast_inj.mp eq)
  obtain ⟨first,second⟩:=Prod.ext_iff.mp cross
  have f : a.1*(n:Int)=p.1*b.1+2*p.2*b.2 := by simpa [mul] using first
  have s : a.2*(n:Int)=p.1*b.2+p.2*b.1 := by simpa [mul] using second
  let lift (u : Int) := (u:Rat)
  have v:=congrArg lift f
  have w:=congrArg lift s
  dsimp [lift] at v w
  simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_natCast] at v w
  apply Prod.ext <;> apply cancel_scalar _ _ (n:Rat) nz <;> dsimp [times] <;> grobner

/-- Reducing the two cleared integral coordinates gives a denominator and
numerator in the actual integral basis with a Bézout identity. -/
theorem primitive_coefficients (h : Q2) :
    ∃ a b : R, b≠(0,0) ∧ times h ((b.1:Rat),(b.2:Rat))=((a.1:Rat),(a.2:Rat)) ∧ coprime a b := by
  let n:=h.1.den*h.2.den
  let p:R:=(h.1.num*(h.2.den:Int),h.2.num*(h.1.den:Int))
  let d:R:=((n:Int),0)
  have pos : 0<n := Nat.mul_pos h.1.den_pos h.2.den_pos
  have one:=clear_coordinate h.1
  have two:=clear_coordinate h.2
  have hp : h.1*(n:Rat)=(p.1:Rat) := by
    dsimp [n,p]
    rw [Rat.natCast_mul,Rat.intCast_mul,Rat.intCast_natCast,←Rat.mul_assoc,one]
  have hq : h.2*(n:Rat)=(p.2:Rat) := by
    dsimp [n,p]
    rw [Rat.natCast_mul,Rat.intCast_mul,Rat.intCast_natCast,Rat.mul_comm (h.1.den:Rat),
      ←Rat.mul_assoc,two]
  obtain ⟨g,a,b,hn,hd,pr⟩:=reduce_pair p d
  refine ⟨a,b,?_,drop_common_denominator h n p a b pos hp hq (cross_from_factors g a b p d hn hd),pr⟩
  intro bz
  have eq:=congrArg Prod.fst hd
  rw [bz] at eq
  have dead : (n:Int)=0 := by simpa [d,mul] using eq
  omega

#print axioms primitive_coefficients
end EllipticHeight.Reduction
