import LocalKummerFibre
import ZInQKernel.Model.Descent.Kummer
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization ZInQ.Descent WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

noncomputable section
variable {l : ℕ} {e : ℚ}

def derivativeAt (l : ℕ) (e : ℚ) : ℚ := 3*e^2+4*l*e-3*(l:ℚ)^2

def rootClass (l : ℕ) (e : ℚ) : RationalPoint l → SqClass ℚ
  | .zero => 1
  | .some x _ _ => if x=e then sqc (derivativeAt l e) else sqc (x-e)

@[simp] theorem zero_class : rootClass l e 0 = 1 := rfl
theorem at_affine {x y : ℚ} (h : (twistCurve l).toAffine.Nonsingular x y) :
    rootClass l e (.some x y h) = if x=e then sqc (derivativeAt l e) else sqc (x-e) := rfl
theorem class_neg (P : RationalPoint l) : rootClass l e (-P)=rootClass l e P := by
  cases P <;> rfl

theorem neg_y (x y : ℚ) : (twistCurve l).toAffine.negY x y= -y := by
  simp [Affine.negY,twistCurve,WeierstrassCurve.toAffine]
theorem equation {x y : ℚ} : (twistCurve l).toAffine.Equation x y ↔ y^2=x*(x-l)*(x+3*l) := by
  rw [Affine.equation_iff]
  simp [twistCurve,WeierstrassCurve.toAffine]
  constructor <;> intro h <;> linear_combination h

variable (he : e*(e-l)*(e+3*l)=0) (dne : derivativeAt l e ≠ 0)
include he dne

private theorem regular_root : (twistCurve l).toAffine.Nonsingular e 0 := by
    rw [nonsingular_iff,Affine.equation_iff]
    simp [twistCurve,WeierstrassCurve.toAffine,derivativeAt] at dne ⊢
    constructor
    · linear_combination -he
    · exact fun h => dne (by linear_combination -h)

def rootPoint : RationalPoint l := .some e 0 (regular_root he dne)

private theorem at_root {x y : ℚ} (h : (twistCurve l).toAffine.Nonsingular x y) (hx : x=e) :
    Point.some x y h = rootPoint he dne := by
  subst x
  have eq := equation.mp h.1
  rw [he] at eq
  have e0 : y=0 := by nlinarith
  subst y
  rfl

private theorem add_root_x {x y : ℚ} (h : (twistCurve l).toAffine.Nonsingular x y) (hx : x≠e) :
    ∃ Y h', Point.some x y h+rootPoint he dne = .some (e+derivativeAt l e/(x-e)) Y h' := by
  unfold rootPoint
  rw [Point.add_of_X_ne hx]
  have ex : (twistCurve l).toAffine.addX x e ((twistCurve l).toAffine.slope x e y 0) =
      e+derivativeAt l e/(x-e) := by
    rw [Affine.slope_of_X_ne hx]
    simp [Affine.addX,twistCurve,WeierstrassCurve.toAffine,derivativeAt]
    field_simp [sub_ne_zero.mpr hx]
    linear_combination equation.mp h.1 + he
  have hn := nonsingular_add h (regular_root he dne) (fun hxy => hx hxy.left)
  rw [ex] at hn
  exact ⟨_,hn,by simp only [Point.some.injEq];exact ⟨ex,trivial⟩⟩

private theorem class_add_root (P : RationalPoint l) :
    rootClass l e (P+rootPoint he dne)=rootClass l e P*sqc (derivativeAt l e) := by
  rcases P with _|⟨x,y,h⟩
  · change rootClass l e (0+rootPoint he dne)=1*_
    rw [zero_add,one_mul]
    simp [rootPoint,at_affine]
  · by_cases hx : x=e
    · rw [at_root he dne h hx]
      unfold rootPoint
      rw [Point.add_self_of_Y_eq (by rw [neg_y,neg_zero])]
      simp [at_affine,SqClass.mul_self]
    · obtain ⟨Y,h',eq⟩ := add_root_x he dne h hx
      have n₁ := sub_ne_zero.mpr hx
      have xne : e+derivativeAt l e/(x-e)≠e := fun H => (div_ne_zero dne n₁) (by linarith)
      rw [eq,at_affine,at_affine,ite_eq_right xne,ite_eq_right hx,add_sub_cancel_left,sqc_div dne n₁,mul_comm]

omit dne in
/-- The value of the chord or tangent at e, squared. The Mathlib cubic
factorization includes the tangent case automatically. -/
theorem chord_identity {x u y v : ℚ} (P : (twistCurve l).toAffine.Nonsingular x y)
    (Q : (twistCurve l).toAffine.Nonsingular u v)
    (h : ¬(x=u ∧ y=(twistCurve l).toAffine.negY u v)) :
    let m := (twistCurve l).toAffine.slope x u y v
    (x-e)*(u-e)*((twistCurve l).toAffine.addX x u m-e)=(y-m*(x-e))^2 := by
  let m := (twistCurve l).toAffine.slope x u y v
  let z := (twistCurve l).toAffine.addX x u m
  have poly : (twistCurve l).toAffine.addPolynomial x y m =
      -((Polynomial.X-Polynomial.C x)*(Polynomial.X-Polynomial.C u)*(Polynomial.X-Polynomial.C z)) :=
    addPolynomial_slope P.1 Q.1 h
  rw [addPolynomial_eq] at poly
  have H:=congrArg (Polynomial.eval e) poly
  simp only [Cubic.toPoly,Polynomial.eval_neg,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_pow,
    twistCurve,WeierstrassCurve.toAffine] at H
  change (x-e)*(u-e)*(z-e)=(y-m*(x-e))^2
  linear_combination -H - he

set_option maxHeartbeats 600000 in
theorem class_add (P Q : RationalPoint l) :
    rootClass l e (P+Q)=rootClass l e P*rootClass l e Q := by
  rcases P with _|⟨x,y,hx⟩
  · change rootClass l e (0+Q)=1*_
    simp
  rcases Q with _|⟨u,v,hu⟩
  · change rootClass l e (_+0)=_*1
    simp
  by_cases xe : x=e
  · rw [at_root he dne hx xe,add_comm,class_add_root he dne]
    simp [rootPoint,at_affine,mul_comm]
  by_cases ue : u=e
  · rw [at_root he dne hu ue,class_add_root he dne]
    simp [rootPoint,at_affine]
  by_cases h : x=u ∧ y=(twistCurve l).toAffine.negY u v
  · rw [Point.add_of_Y_eq h.1 h.2,zero_class,at_affine,at_affine,ite_eq_right xe,ite_eq_right ue,h.1,
      SqClass.mul_self]
  have key := chord_identity (l := l) (e := e) he hx hu h
  rw [Point.add_some h]
  let m : ℚ := (twistCurve l).toAffine.slope x u y v
  let z : ℚ := (twistCurve l).toAffine.addX x u m
  change rootClass l e (.some z _ _)=_
  by_cases ze : z=e
  · have sum : Point.some x y hx + Point.some u v hu=rootPoint he dne := by
      rw [Point.add_some h];exact at_root he dne _ ze
    have Q : Point.some u v hu= -Point.some x y hx+rootPoint he dne := by rw [←sum];abel
    rw [at_root he dne _ ze,Q,class_add_root he dne,class_neg,←mul_assoc,SqClass.mul_self,one_mul]
    simp [rootPoint,at_affine]
  · rw [at_affine,at_affine,at_affine,ite_eq_right xe,ite_eq_right ue,ite_eq_right ze]
    have nz := mul_ne_zero (sub_ne_zero.mpr xe) (sub_ne_zero.mpr ue)
    change (x-e)*(u-e)*(z-e)=(y-m*(x-e))^2 at key
    have nn : y-m*(x-e)≠0 := by
      intro zero
      rw [zero,zero_pow (by decide)] at key
      exact (mul_ne_zero nz (sub_ne_zero.mpr ze)) key
    have id : z-e=(x-e)*(u-e)*((y-m*(x-e))/((x-e)*(u-e)))^2 := by
      rw [div_pow,←key];field_simp
    rw [id,sqc_mul_sq _ (div_ne_zero nn nz),sqc_mul (sub_ne_zero.mpr xe) (sub_ne_zero.mpr ue)]

end
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.chord_identity
#print axioms Sun28.MarkedDescent.class_add
