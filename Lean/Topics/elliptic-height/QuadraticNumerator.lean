import Std

namespace EllipticHeight
namespace QuadraticInt

/-- Coefficients in the integral basis 1, √2. -/
abbrev R := Int × Int
def plus (a b : R) : R := (a.1+b.1,a.2+b.2)
def mul (a b : R) : R := (a.1*b.1+2*a.2*b.2,a.1*b.2+a.2*b.1)
def conj (a : R) : R := (a.1,-a.2)
def norm (a : R) : Int := a.1^2-2*a.2^2
def tr (a : R) : Int := 2*a.1
def divides (a b : R) : Prop := ∃ q, b=mul a q
def coprime (a b : R) : Prop := ∃ u v, plus (mul a u) (mul b v)=(1,0)

theorem mul_norm (a b : R) : norm (mul a b)=norm a*norm b := by
  unfold norm mul
  grobner

theorem norm_dvd {a b : R} (h : divides a b) : (norm a).natAbs ∣ (norm b).natAbs := by
  obtain ⟨q,rfl⟩:=h
  exact ⟨(norm q).natAbs,by rw [mul_norm,Int.natAbs_mul]⟩

private theorem cancel_identity (z a b c u v : R) :
    plus (mul z (plus (mul a u) (mul b v))) (mul (mul a c) v)=
    plus (mul a (plus (mul z u) (mul c v))) (mul (mul z b) v) := by
  apply Prod.ext <;> dsimp [plus,mul] <;> grobner

/-- Clear the denominator of a product and retain a numerator coprime to it. -/
theorem cancel_denominator {a b z c : R} (pr : coprime a b) (eq : mul z b=mul a c) :
    divides a z := by
  obtain ⟨u,v,bez⟩:=pr
  refine ⟨plus (mul z u) (mul c v),?_⟩
  have h:=cancel_identity z a b c u v
  rw [bez,eq] at h
  apply Prod.ext
  · have e:=congrArg Prod.fst h
    change (z.1*1+2*z.2*0)+_=_+_ at e
    omega
  · have e:=congrArg Prod.snd h
    change (z.1*0+z.2*1)+_=_+_ at e
    omega

private theorem trace_square (w x : R) :
    tr (mul w x)^2 = tr x * tr (mul (mul w w) x) - 8*w.2^2*norm x := by
  unfold tr mul norm
  grobner

/-- The coefficients of Norm(bX-a) generate the unit ideal in the rational
integers whenever a and b generate the unit ideal in the quadratic integers. -/
theorem primitive_norm_form {a b : R} (pr : coprime a b) :
    ∃ i j k : Int, norm a*i + tr (mul a (conj b))*j + norm b*k=1 := by
  obtain ⟨u,v,bez⟩:=pr
  let x:=mul a (conj b)
  let w:=mul u (conj v)
  let h:=norm a*norm u+norm b*norm v
  let t:=tr (mul w x)
  have e : h+t=1 := by
    have q:=congrArg norm bez
    dsimp [h,t,w,x,norm,mul,plus,tr,conj] at q ⊢
    grobner
  have nx : norm x=norm a*norm b := by
    dsimp only [x]
    rw [mul_norm]
    dsimp [norm,conj]
    grobner
  have s:=trace_square w x
  change t^2=tr x*tr (mul (mul w w) x)-8*w.2^2*norm x at s
  rw [nx] at s
  refine ⟨norm u*(h+2*t)-8*w.2^2*norm b,tr (mul (mul w w) x),norm v*(h+2*t),?_⟩
  change norm a*_+tr x*_+norm b*_=1
  have hs : (h+t)^2=1 := by rw [e];decide
  have eh : h=norm a*norm u+norm b*norm v := rfl
  grobner

end QuadraticInt
end EllipticHeight

#print axioms EllipticHeight.QuadraticInt.mul_norm
#print axioms EllipticHeight.QuadraticInt.norm_dvd
#print axioms EllipticHeight.QuadraticInt.cancel_denominator
#print axioms EllipticHeight.QuadraticInt.primitive_norm_form
