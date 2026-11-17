import Mathlib

/-! The analytic inequalities below apply to every reduced Siegel matrix of genus two.
The two nontrivial theta estimates are inputs from Streng's bounds on the reduced domain. -/
namespace SixContactHP
noncomputable section
open Finset Real

/-- Product of the squared norms of the ten even theta nulls, grouped
as (0,1,2,3,12,15), (4,6) and (8,9) in Streng's numbering. -/
def chiNorm (s : Fin 6 → ℂ) (x y : Fin 2 → ℂ) : ℝ :=
  (∏ i, ‖s i‖^2)*(∏ i, ‖x i‖^2)*(∏ i, ‖y i‖^2)

/-- Uniform constant for the full Habegger--Pazuki archimedean logarithm. -/
def archConstant : ℝ := 2^20*3^8*120^2

private theorem theta_product {n : ℕ} (s : Fin n → ℂ) {B : ℝ}
    (hb : ∀ i, ‖s i‖ ≤ B) : (∏ i, ‖s i‖^2) ≤ (B^2)^n := by
  calc
    _ ≤ ∏ _i : Fin n, B^2 := by
      gcongr with i _
      exact hb i
    _ = _ := by simp

private theorem exp_four (y : ℝ) : Real.exp (-(π*y)/4)^4 = Real.exp (-(π*y)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem moment_five {y : ℝ} (hy : 0 ≤ y) :
    (π*y)^5 * Real.exp (-(π*y)) ≤ 120 := by
  have h := Real.pow_div_factorial_le_exp (π*y) (mul_nonneg Real.pi_pos.le hy) 5
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg]
  calc
    (π*y)^5 * (Real.exp (π*y))⁻¹ = (π*y)^5 / Real.exp (π*y) := by ring
    _ ≤ 120 := (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)

/-- Streng's reduced-period estimates control the product for any such period matrix.
There is no choice of a labelling of branch points in the height. -/
theorem theta_envelope (s : Fin 6 → ℂ) (x y : Fin 2 → ℂ) (y₁ y₂ : ℝ)
    (hs : ∀ i, ‖s i‖ ≤ 2)
    (hx : ∀ i, ‖x i‖ ≤ 3 * Real.exp (-(π*y₁)/4))
    (hy : ∀ i, ‖y i‖ ≤ 3 * Real.exp (-(π*y₂)/4)) :
    chiNorm s x y ≤ 2^12 * 3^8 * Real.exp (-(π*y₁)) * Real.exp (-(π*y₂)) := by
  have hs' := theta_product s hs
  have hx' := theta_product x hx
  have hy' := theta_product y hy
  unfold chiNorm
  calc
    _ ≤ ((2:ℝ)^2)^6 * ((3 * Real.exp (-(π*y₁)/4))^2)^2 *
        ((3 * Real.exp (-(π*y₂)/4))^2)^2 := by gcongr
    _ = _ := by
      conv_rhs => rw [← exp_four y₁, ← exp_four y₂]
      ring

theorem hp_arch_bound (s : Fin 6 → ℂ) (x y : Fin 2 → ℂ) {y₁ y₂ y₃ : ℝ}
    (h₁ : 0 ≤ y₁) (h₂ : 0 ≤ y₂) (hdet : 0 ≤ y₁*y₂-y₃^2)
    (hs : ∀ i, ‖s i‖ ≤ 2)
    (hx : ∀ i, ‖x i‖ ≤ 3 * Real.exp (-(π*y₁)/4))
    (hy : ∀ i, ‖y i‖ ≤ 3 * Real.exp (-(π*y₂)/4)) :
    2^8 * π^10 * chiNorm s x y * (y₁*y₂-y₃^2)^5 ≤ archConstant := by
  have he := theta_envelope s x y y₁ y₂ hs hx hy
  have hd : (y₁*y₂-y₃^2)^5 ≤ (y₁*y₂)^5 :=
    pow_le_pow_left₀ hdet (sub_le_self _ (sq_nonneg _)) 5
  calc
    _ ≤ 2^8 * π^10 * (2^12 * 3^8 * Real.exp (-(π*y₁)) * Real.exp (-(π*y₂))) *
        (y₁*y₂)^5 := by gcongr
    _ = (2^20*3^8)*(((π*y₁)^5 * Real.exp (-(π*y₁))) *
        ((π*y₂)^5 * Real.exp (-(π*y₂)))) := by ring
    _ ≤ (2^20*3^8) * (120*120) := by
      gcongr
      · exact moment_five h₁
      · exact moment_five h₂
    _ = _ := by norm_num [archConstant]

theorem archConstant_lt : archConstant < 2^47 := by norm_num [archConstant]

end
end SixContactHP

#print axioms SixContactHP.theta_envelope
#print axioms SixContactHP.hp_arch_bound
#print axioms SixContactHP.archConstant_lt

