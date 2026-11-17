import SeparatedCompiler
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Nonmonic equations of degree at most two are scaled to monic ones.
The resultant compiler then supplies the final rational coordinate. -/

open ZInQBlueprint.SunResultant ZInQBlueprint.SunResultant.ParamTower
open Sun28.Branches MvPolynomial
namespace WidthTower
noncomputable section

theorem linear_scale {a b x : ℚ} : a*x + b = 0 ↔ a*x = -b := by constructor <;> intro h <;> linarith

theorem quadratic_scale {a b c x : ℚ} (ha : a ≠ 0) :
    (a*x)^2 + b*(a*x) + a*c = 0 ↔ a*x^2+b*x+c = 0 := by
  rw [show (a*x)^2 + b*(a*x) + a*c = a*(a*x^2+b*x+c) by ring, mul_eq_zero]
  simp [ha]

theorem forced_leading {a b x : ℚ} (hb : b ≠ 0) (h : a*x+b=0) : a ≠ 0 := by
  rintro rfl
  exact hb (by simpa using h)

private def swapFirst (n : ℕ) : Fin (n+2) → Fin (n+2) :=
  Fin.cases 1 (Fin.cases 0 (fun i : Fin n => i.succ.succ))

/-- Put the rational input first and the locator second. -/
def inputPolynomial {n l : ℕ} (T : ParamTower (Poly (n+1)) l)
    (eqs guards : List (Sun28.Compiler.Test (n+1) l)) : Poly (n+2) :=
  rename (swapFirst n) (Sun28.Compiler.polynomial T eqs guards)

attribute [local irreducible] Sun28.Compiler.polynomial Sun28.Compiler.Solutions in
set_option maxHeartbeats 2000000 in
theorem input_projection {n l : ℕ} (T : ParamTower (Poly (n+1)) l)
    (eqs guards : List (Sun28.Compiler.Test (n+1) l)) (t : ℚ) :
    (∃ w : Fin (n+1) → ℚ, value (Fin.cases t w) (inputPolynomial T eqs guards) = 0) ↔
      ∃ z : Fin n → ℚ, Sun28.Compiler.Solutions T eqs guards (Fin.cases t z) := by
  have perm (u : ℚ) (z : Fin n → ℚ) :
      value (Fin.cases t (Fin.cases u z)) (inputPolynomial T eqs guards) =
      value (Fin.cases u (Fin.cases t z)) (Sun28.Compiler.polynomial T eqs guards) := by
    unfold inputPolynomial value
    change eval₂ _ _ (rename _ _) = eval₂ _ _ _
    rw [eval₂_rename]
    congr 1; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  constructor
  · rintro ⟨w,hw⟩
    have split : Fin.cases (w 0) (Fin.tail w) = w := funext (Fin.cases rfl (fun _ => rfl))
    refine ⟨Fin.tail w,(Sun28.Compiler.polynomial_spec T eqs guards _).mp ⟨w 0,?_⟩⟩
    rw [← perm,split]; exact hw
  · rintro ⟨z,h⟩
    obtain ⟨v,hv⟩ := (Sun28.Compiler.polynomial_spec T eqs guards (Fin.cases t z)).mpr h
    refine ⟨Fin.cases v z, ?_⟩
    rw [perm]
    exact hv

end
end WidthTower
#print axioms WidthTower.quadratic_scale
#print axioms WidthTower.input_projection
