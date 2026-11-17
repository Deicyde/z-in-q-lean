import RootOrdinate
import QuadraticNumerator
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The field and order use the same basis 1,√2 as the stored rational pairs. -/
namespace EllipticOrbit.Field
open PhysicalProjection.Comparison (Q2)

abbrev K := QuadraticAlgebra ℚ 2 0
abbrev O := Zsqrtd (2 : ℤ)

instance twoIrrational : Fact (∀ q : ℚ, q^2 ≠ (2:ℚ)+0*q) :=
  ⟨fun q=>by simpa using CircuitTransport.Quadratic.two_nonsquare q⟩

def r : K := QuadraticAlgebra.omega
def delta : K := ⟨3,-1⟩
def D : K := ⟨11,-6⟩

theorem r_sq : r^2=2 := by rw [pow_two]; exact QuadraticAlgebra.omega_mul_omega_eq_mk
theorem delta_eq : delta=3-r := by
  ext <;> norm_num [delta,r,QuadraticAlgebra.omega,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
theorem D_eq : D=11-6*r := by
  ext <;> norm_num [D,r,QuadraticAlgebra.omega,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
theorem delta_sq : delta^2=D := by ext <;> norm_num [delta,D,pow_two]
theorem D_ne_zero : D≠0 := by decide

def ofPair (q : Q2) : K := ⟨q.1,q.2⟩
def coeffs (z : K) : Q2 := (z.re,z.im)

@[simp] theorem ofPair_coeffs (z : K) : ofPair (coeffs z)=z := rfl
@[simp] theorem coeffs_ofPair (q : Q2) : coeffs (ofPair q)=q := rfl
theorem ofPair_injective : Function.Injective ofPair := fun _ _ h=>congrArg coeffs h

theorem ofPair_mul (p q : Q2) :
    ofPair (PhysicalProjection.Comparison.times p q)=ofPair p*ofPair q := by
  ext <;> simp [ofPair,PhysicalProjection.Comparison.times]
theorem ofPair_sub (p q : Q2) :
    ofPair (PhysicalProjection.RootOrdinate.sub p q)=ofPair p-ofPair q := rfl
theorem ofPair_sq (q : Q2) : ofPair (PhysicalProjection.Comparison.sq q)=(ofPair q)^2 :=
  (ofPair_mul q q).trans (pow_two _).symm
theorem ofPair_fourth (q : Q2) : ofPair (PhysicalProjection.RootOrdinate.fourth q)=(ofPair q)^4 := by
  unfold PhysicalProjection.RootOrdinate.fourth
  rw [ofPair_sq,ofPair_sq]; ring
theorem root_iff (h j : Q2) : PhysicalProjection.RootOrdinate.root h j ↔
    (ofPair j)^2=(ofPair h)^4-D := by
  unfold PhysicalProjection.RootOrdinate.root
  rw [←ofPair_injective.eq_iff,ofPair_sq,ofPair_sub,ofPair_fourth]
  rfl

def orderMap : O →+* K where
  toFun a := ⟨(a.re:ℚ),(a.im:ℚ)⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

theorem orderMap_injective : Function.Injective orderMap := by
  intro a b eq
  have re:=congrArg QuadraticAlgebra.re eq
  have im:=congrArg QuadraticAlgebra.im eq
  change (a.re:ℚ)=(b.re:ℚ) at re
  change (a.im:ℚ)=(b.im:ℚ) at im
  ext
  · exact_mod_cast re
  · exact_mod_cast im

def asOrder (q : EllipticHeight.QuadraticInt.R) : O := ⟨q.1,q.2⟩
theorem order_compat (q : EllipticHeight.QuadraticInt.R) :
    orderMap (asOrder q)=ofPair ((q.1:ℚ),(q.2:ℚ)) := rfl
theorem order_norm (q : EllipticHeight.QuadraticInt.R) :
    (asOrder q).norm=EllipticHeight.QuadraticInt.norm q := by
  change q.1*q.1-2*q.2*q.2=q.1^2-2*q.2^2
  ring
theorem fraction_iff (z : Q2) (a b : EllipticHeight.QuadraticInt.R) :
    PhysicalProjection.Comparison.times z ((b.1:ℚ),(b.2:ℚ))=((a.1:ℚ),(a.2:ℚ)) ↔
    ofPair z*orderMap (asOrder b)=orderMap (asOrder a) := by
  rw [←ofPair_injective.eq_iff,ofPair_mul,order_compat,order_compat]

theorem square_plus_D_ne_zero (z : K) : z^2+D≠0 := by
  intro eq
  have hr:=congrArg QuadraticAlgebra.re eq
  simp only [pow_two,QuadraticAlgebra.re_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.re_zero,D] at hr
  nlinarith [sq_nonneg z.re,sq_nonneg z.im]

#print axioms r_sq
#print axioms delta_sq
#print axioms ofPair_mul
#print axioms root_iff
#print axioms orderMap
#print axioms orderMap_injective
#print axioms order_norm
#print axioms fraction_iff
#print axioms square_plus_D_ne_zero
end EllipticOrbit.Field
