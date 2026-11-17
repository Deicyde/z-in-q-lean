import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Evaluation away from the finite set of poles, for simultaneous polynomial identities. -/
open Filter
namespace Sun28.PointConstruction
noncomputable section
abbrev Functions := RatFunc ℚ
abbrev Germs := Germ (cofinite : Filter ℚ) ℚ

def value (f:Functions) (x:ℚ) : ℚ := RatFunc.eval (RingHom.id ℚ) x f

private lemma regular (f:Functions) : ∀ᶠ x:ℚ in cofinite, f.denom.eval₂ (RingHom.id ℚ) x ≠ 0 := by
  simpa only [Polynomial.eval₂_id] using Polynomial.eventually_eval_ne_zero_cofinite f.denom_ne_zero

/-- Common specialization for all rational inputs outside a finite set. -/
def evaluate : Functions →+* Germs where
  toFun f := ↑(value f)
  map_zero' := by apply Germ.coe_eq.mpr; exact Eventually.of_forall (fun x=>RatFunc.eval_zero _ _)
  map_one' := by apply Germ.coe_eq.mpr; exact Eventually.of_forall (fun x=>RatFunc.eval_one _ _)
  map_add' f g := by
    change ((value (f+g)):Germs) = ↑(fun x => value f x + value g x)
    apply Germ.coe_eq.mpr
    filter_upwards [regular f,regular g] with x hf hg
    exact RatFunc.eval_add _ _ hf hg
  map_mul' f g := by
    change ((value (f*g)):Germs) = ↑(fun x => value f x * value g x)
    apply Germ.coe_eq.mpr
    filter_upwards [regular f,regular g] with x hf hg
    exact RatFunc.eval_mul _ _ hf hg

theorem eventually_nonzero {f:Functions} (h:f≠0) : ∀ᶠ x:ℚ in cofinite, value f x ≠ 0 := by
  filter_upwards [regular f,Polynomial.eventually_eval_ne_zero_cofinite (RatFunc.num_ne_zero h)] with x hd hn
  change f.num.eval₂ (RingHom.id ℚ) x / f.denom.eval₂ (RingHom.id ℚ) x ≠ 0
  apply div_ne_zero _ hd
  simpa only [Polynomial.eval₂_id] using hn

theorem evaluate_constant (c:ℚ) : evaluate (RatFunc.C c) = (↑(fun _ : ℚ => c):Germs) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun x => RatFunc.eval_C _ _)

theorem evaluate_variable : evaluate RatFunc.X = (↑(fun x:ℚ => x):Germs) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun x => by simp [value])

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.eventually_nonzero
#print axioms Sun28.PointConstruction.evaluate_constant
#print axioms Sun28.PointConstruction.evaluate_variable
