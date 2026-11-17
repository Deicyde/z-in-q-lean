import PrimitiveDouble
import SignedOrder

namespace EllipticHeight
open QuadraticInt PhysicalOrder

/-- Integral coefficient pairs in Mathlib's quadratic order. -/
def asOrder (a : QuadraticInt.R) : PhysicalOrder.O := ⟨a.1,a.2⟩

theorem asOrder_norm (a : R) : (asOrder a).norm=QuadraticInt.norm a := by
  change a.1*a.1-2*a.2*a.2=a.1^2-2*a.2^2
  ring

private theorem map_plus (a b : R) : asOrder (plus a b)=asOrder a+asOrder b := rfl
private theorem order_mul (a b : R) : asOrder (mul a b)=asOrder a*asOrder b := by
  rfl
private theorem map_square (a : R) : asOrder (sq a)=(asOrder a)^2 := by
  unfold QuadraticInt.sq
  rw [order_mul,pow_two]
private theorem delta_square : (asOrder delta)^2=D := by decide

private theorem map_raw (a b : R) :
    asOrder (Primitive.top a b)=rawA (asOrder a) (asOrder b) ∧
    asOrder (Primitive.bottom a b)=rawB (asOrder a) (asOrder b) := by
  have other : asOrder (Primitive.other a b)=asOrder (sq a)-asOrder (mul (sq delta) (sq b)) := rfl
  constructor
  · simp only [Primitive.top,Primitive.term,map_square,map_plus,order_mul,delta_square,rawA]
  · simp only [Primitive.bottom,order_mul,map_square,other,delta_square,rawB]
    rfl

private theorem chart_in_order {a b c : R} (h : chart a b c) :
    (asOrder c)^2+D*(asOrder b)^4=(asOrder a)^4 := by
  have e:=congrArg asOrder h
  change asOrder (plus (sq c) (sq (mul delta (sq b))))=asOrder (sq (sq a)) at e
  simp only [map_plus,map_square,order_mul,mul_pow,delta_square] at e
  linear_combination e

theorem bezout_in_order {a b : R} (h : coprime a b) :
    SignedOrder.Primitive (asOrder a) (asOrder b) := by
  obtain ⟨u,v,bez⟩:=h
  refine ⟨asOrder u,asOrder v,?_⟩
  have e:=congrArg asOrder bez
  change asOrder (plus (mul a u) (mul b v))=1 at e
  rw [map_plus,order_mul,order_mul] at e
  linear_combination e

/-- Integral signed charts with the homogeneous addition and doubling equations. -/
structure IntegralOrbit (A B : ℕ → O) (n : ℕ) : Prop where
  charts : ∀ i, ∃ a b c : R, coprime a b ∧ chart a b c ∧ A i=asOrder (sq a) ∧ B i=asOrder (sq b)
  origin : B 0=0
  generator : A 1*B1=B 1*A1
  doubleCross : ∀ i, rawA (A i) (B i)*B (2*i)=rawB (A i) (B i)*A (2*i)
  addition : ∀ j : ℕ, j+2≤n →
    let a := A (2*(j+2)); let b := B (2*(j+2))
    let c := A (2*j); let e := B (2*j)
    let i := 4*(j+1)
    (a*c+D*b*e)^2*(A i*B 4+B i*A 4)=(2*(a*e+b*c)*(a*c-D*b*e))*(A i*A 4) ∧
    (a*c+D*b*e)^2*(B i*B 4)=(a*e-b*c)^2*(A i*A 4)

theorem IntegralOrbit.signed {A B : ℕ → O} {n : ℕ} (g : IntegralOrbit A B n) :
    SignedOrder.SignedCoordinates A B n := by
  refine { primitive:=?_, origin:=g.origin, generator:=g.generator, quartic:=?_,
           doubleCross:=g.doubleCross, rawPrimitive:=?_,
           middle:=fun j hj=>(g.addition j hj).1, bottom:=fun j hj=>(g.addition j hj).2 }
  · intro i
    obtain ⟨a,b,c,p,h,ha,hb⟩:=g.charts i
    rw [ha,hb]
    exact bezout_in_order (Primitive.chart_iterate p h 0)
  · intro i f
    obtain ⟨a,b,c,_,h,ha,hb⟩:=g.charts i
    rw [ha,hb,map_square,map_square]
    exact SignedOrder.quartic_of_chart _ _ _ (chart_in_order h) f
  · intro i
    obtain ⟨a,b,c,p,h,ha,hb⟩:=g.charts (2*i)
    rw [ha,hb,←(map_raw (sq a) (sq b)).1,←(map_raw (sq a) (sq b)).2]
    exact bezout_in_order (Primitive.chart_iterate p h 1)

theorem IntegralOrbit.bound {A B : ℕ → O} {n : ℕ} (g : IntegralOrbit A B n) :
    (41^(n^2))^2 ≤ (A n).norm.natAbs := by
  by_cases hn : n=0
  · subst n
    have h:=g.signed.coordinates.origin
    obtain ⟨one,_,_⟩:=generator_masses
    change (41^(0^2))^2 ≤ NormBounds.mass realNorm (A 0)
    rw [h,one]
    decide
  · exact SignedOrder.signed_numerator_index A B n hn g.signed

end EllipticHeight
#print axioms EllipticHeight.asOrder_norm
#print axioms EllipticHeight.IntegralOrbit.signed
#print axioms EllipticHeight.IntegralOrbit.bound
