import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-! An odd monic equation over the field of a single simple branch point.
The change of variables rescales both coordinates and needs no square root. -/
open Polynomial
namespace ZInQBlueprint.TorsionHeight
noncomputable section
variable {K : Type*} [Field K]

def oddPolynomial (f : K[X]) (a : K) : K[X] :=
  let g := taylor a f
  let c := f.derivative.eval a
  X^5 + C (g.coeff 2) * X^4 + C (c * g.coeff 3) * X^3 +
    C (c^2 * g.coeff 4) * X^2 + C (c^3 * g.coeff 5) * X + C (c^4 * g.coeff 6)

theorem oddPolynomial_monic_degree (f : K[X]) (a : K) :
    (oddPolynomial f a).Monic ∧ (oddPolynomial f a).natDegree = 5 := by
  let g := taylor a f
  let c := f.derivative.eval a
  let low : K[X] := C (g.coeff 2) * X^4 + C (c * g.coeff 3) * X^3 +
    C (c^2 * g.coeff 4) * X^2 + C (c^3 * g.coeff 5) * X + C (c^4 * g.coeff 6)
  have hl : low.natDegree < 5 := by
    dsimp only [low]
    compute_degree
    decide
  have he : oddPolynomial f a = X^5 + low := by
    dsimp only [oddPolynomial,low,c,g]; ring
  have ht : low.natDegree < ((X:K[X])^5).natDegree := by simpa using hl
  rw [he]; exact ⟨(monic_X_pow 5).add_of_left (degree_lt_degree ht), (natDegree_add_eq_left_of_natDegree_lt ht).trans (by simp)⟩

private theorem shifted_eval {f : K[X]} {a x : K} (hd : f.natDegree ≤ 6)
    (ha : f.IsRoot a) :
    f.eval x = (f.derivative.eval a)*(x-a) + (taylor a f).coeff 2*(x-a)^2 +
      (taylor a f).coeff 3*(x-a)^3 + (taylor a f).coeff 4*(x-a)^4 +
      (taylor a f).coeff 5*(x-a)^5 + (taylor a f).coeff 6*(x-a)^6 := by
  have deg : (taylor a f).natDegree < 7 := by rw [natDegree_taylor]; omega
  calc
    f.eval x = (taylor a f).eval (x-a) := (taylor_eval_sub a f x).symm
    _ = _ := by
      rw [eval_eq_sum_range' deg]; simp [Finset.sum_range_succ,ha.eq_zero]

/-- Polynomial identity on the open complement of the marked fibre. -/
theorem odd_evaluation {f : K[X]} {a x : K} (hd : f.natDegree ≤ 6) (ha : f.IsRoot a)
    (hx : x ≠ a) :
    (oddPolynomial f a).eval (f.derivative.eval a / (x-a)) * (x-a)^6 =
      (f.derivative.eval a)^4 * f.eval x := by
  have h := sub_ne_zero.mpr hx
  rw [shifted_eval hd ha]
  simp only [oddPolynomial,eval_add,eval_pow,eval_mul,eval_X,eval_C]
  field_simp [h]

/-- Isomorphism of affine point sets off the two indicated fibres over the same field. -/
def oddOpenEquiv {f : K[X]} {a : K} (hd : f.natDegree ≤ 6) (ha : f.IsRoot a)
    (hs : f.derivative.eval a ≠ 0) :
    {p : K × K // p.2^2 = f.eval p.1 ∧ p.1 ≠ a} ≃
    {p : K × K // p.2^2 = (oddPolynomial f a).eval p.1 ∧ p.1 ≠ 0} where
  toFun p := by
    let t := p.1.1 - a
    have ht : t ≠ 0 := sub_ne_zero.mpr p.2.2
    let c := f.derivative.eval a
    refine ⟨(c/t, c^2 * p.1.2 / t^3), ?_, div_ne_zero hs ht⟩
    have H := odd_evaluation hd ha p.2.2
    change (oddPolynomial f a).eval (c/t) * t^6 = c^4 * f.eval p.1.1 at H
    rw [←p.2.1] at H
    rw [div_pow, mul_pow]
    apply (div_eq_iff (pow_ne_zero _ (pow_ne_zero 3 ht))).2
    linear_combination -H
  invFun p := by
    let c := f.derivative.eval a
    let z := p.1.1
    have hz : z ≠ 0 := p.2.2
    have hca : a+c/z ≠ a := by
      intro h; have := div_ne_zero hs hz
      apply this; simpa using sub_eq_zero.mpr h
    refine ⟨(a+c/z, c*p.1.2/z^3), ?_, hca⟩
    have H := odd_evaluation hd ha hca
    have hcancel : a+c/z-a = c/z := by ring
    have hc : c ≠ 0 := hs
    have hinv : c/(c/z) = z := by field_simp [hc,hz]
    change (oddPolynomial f a).eval (c/(a+c/z-a)) * (a+c/z-a)^6 =
        c^4*f.eval (a+c/z) at H
    rw [hcancel,hinv,←p.2.1] at H
    change (c*p.1.2/z^3)^2 = _
    field_simp [hz] at H ⊢
    linear_combination H
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [hs,sub_ne_zero.mpr p.2.2]; ring
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [hs,p.2.2] <;> ring

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.oddPolynomial_monic_degree
#print axioms ZInQBlueprint.TorsionHeight.odd_evaluation
#print axioms ZInQBlueprint.TorsionHeight.oddOpenEquiv
