import ChartJets

namespace WitnessTransfer
open Lean.Grind IndependentIndices.ChartJets
attribute [local instance] Ring.intCast
variable {A : Type} [CommRing A]

private theorem eval_add (x : A) (a b : Poly) : val x (add a b)=val x a+val x b := by
  induction a generalizing b with
  | nil => simp only [add,val]; grobner
  | cons i a ih => cases b with
    | nil => simp only [add,val]; grobner
    | cons j b => simp only [add,val,ih,Ring.intCast_add]; grobner

private theorem eval_neg (x : A) (a : Poly) : val x (neg a)= -val x a := by
  induction a with
  | nil => simp only [neg,List.map_nil,val];grobner
  | cons a as ih =>
    change ((-a:Int):A)+x*(val x (neg as))= -((a:A)+x*val x as)
    rw [ih,Ring.intCast_neg];grobner

private theorem eval_pow (x : A) (a : Poly) (k : Nat) : val x (power a k)=(val x a)^k := by
  induction k with
  | zero => simp only [power,val,Ring.intCast_one,Semiring.pow_zero];grobner
  | succ k ih => simp only [power,mul_val,ih,Semiring.pow_succ]

theorem n_formula (x : A) : val x n=16*x*(1-x)^2 := by
  simp only [n,val,Ring.intCast_neg];grobner
theorem d_formula (x : A) : val x d=(1+x)^4 := by
  simp only [d,val];grobner
theorem s_formula (x : A) : val x s=1-6*x+x^2 := by
  simp only [s,val,Ring.intCast_neg];grobner

/-- Homogenization stays valid when d has zero divisors, since the only
substitution used is d w' = n. -/
private theorem hom_value (x y : A) (m) (a : Poly) (i : Nat)
    (point : val x d*y=val x n) (fits : i+a.length≤m+1) :
    val x (hom m a i)=(val x d)^m*y^i*val y a := by
  induction a generalizing i with
  | nil => simp only [hom,val]; grobner
  | cons c cs ih =>
    have hle : i≤m := by simp at fits;omega
    have fac : (val x n)^i*(val x d)^(m-i)=(val x d)^m*y^i := by
      rw [← point,CommSemiring.mul_pow,show m=i+(m-i) from by omega,Semiring.pow_add]
      simp only [Nat.add_sub_cancel_left]
      grobner
    rw [hom,eval_add,mul_val,mul_val,eval_pow,eval_pow,fac,ih (i+1) (by simp at fits;omega)]
    simp only [val,Semiring.pow_succ];grobner

theorem defect_value (x y : A) (m) (a q : Poly) (point : val x d*y=val x n)
    (ha : a.length≤m+1) (hq : q.length≤m+1) :
    val x (defect m a q)=(val x d)^m*
      ((1-x^2)*val y a*val x q-(1-6*x+x^2)*val y q*val x a) := by
  rw [defect,eval_add,eval_neg,mul_val,mul_val,mul_val,mul_val,
      hom_value x y m a 0 point (by omega),hom_value x y m q 0 point (by omega),s_formula]
  simp only [val,Semiring.pow_zero,Ring.intCast_neg,Ring.intCast_one,Ring.intCast_zero];grobner

theorem mixed_value (w : A) : val w mixed=val w pNumer*15-val w short*val w pDenom := by
  rw [mixed,eval_add,eval_neg,mul_val,mul_val]
  simp only [val];grobner

end WitnessTransfer
