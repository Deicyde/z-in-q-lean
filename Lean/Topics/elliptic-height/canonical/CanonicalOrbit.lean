import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace EllipticHeight.Canonical

open Filter Set
open scoped Topology

/-- The two error bounds can come from different sets of points. -/
theorem iterate_lower (a : ℕ → ℝ) (L : ℝ) (step : ∀ k, 4 * a k - L ≤ a (k + 1))
    (k : ℕ) : 4 ^ k * (a 0 - L / 3) ≤ a k - L / 3 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith [step k]

theorem iterate_upper (a : ℕ → ℝ) (U : ℝ) (step : ∀ k, a (k + 1) ≤ 4 * a k + U)
    (k : ℕ) : a k + U / 3 ≤ 4 ^ k * (a 0 + U / 3) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith [step k]

/-- The real limit exists from duplication alone. The factor 2 in the usual
Néron--Tate normalization is absorbed into the value H of this limit. -/
theorem exists_canonical_limit (a : ℕ → ℝ) (L U : ℝ)
    (lo : ∀ k, 4 * a k - L ≤ a (k + 1))
    (hi : ∀ k, a (k + 1) ≤ 4 * a k + U) :
    ∃ H : ℝ, Tendsto (fun k : ℕ => a k / 4 ^ k) atTop (𝓝 H) ∧
      a 0 - L / 3 ≤ H ∧ H ≤ a 0 + U / 3 := by
  let f (k : ℕ) : ℝ := (a k - L / 3) / 4 ^ k
  have gap : 0 ≤ L + U := by linarith [lo 0, hi 0]
  have mono : Monotone f := monotone_nat_of_le_succ fun k => by
    dsimp [f]
    rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have s := mul_le_mul_of_nonneg_right (lo k) (by positivity : (0 : ℝ) ≤ 4 ^ k)
    nlinarith
  have bounded (k : ℕ) : f k ≤ a 0 + U / 3 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ k)).2
    linarith [iterate_upper a U hi k]
  have above : BddAbove (range f) := ⟨_, fun _ ⟨k, hk⟩ => hk ▸ bounded k⟩
  let H := ⨆ k, f k
  have lim : Tendsto f atTop (𝓝 H) := tendsto_atTop_ciSup mono above
  have dec : Tendsto (fun k : ℕ => (4 : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have small := dec.const_mul (L / 3)
  have norm : (fun k : ℕ => a k / 4 ^ k) = fun k => f k + (L / 3) * (4 : ℝ)⁻¹ ^ k := by
    funext k
    show a k / 4 ^ k = (a k - L / 3) / 4 ^ k + L / 3 * (4 : ℝ)⁻¹ ^ k
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow]
    ring
  refine ⟨H, norm ▸ ?_, ?_, ciSup_le bounded⟩
  · simpa only [mul_zero, add_zero] using lim.add small
  · simpa [f] using (le_ciSup above 0)

private theorem nonpos_of_bounded_scaled (d B : ℝ) (h : ∀ k : ℕ, 4 ^ k * d ≤ B) : d ≤ 0 := by
  by_contra! positive
  obtain ⟨k, hk⟩ := exists_nat_gt (B / d)
  have bound (j : ℕ) : (j : ℝ) ≤ 4 ^ j := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [Nat.cast_succ, pow_succ]
      have g : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      linarith
  have := mul_le_mul_of_nonneg_right (bound k) positive.le
  exact (not_lt_of_ge ((this.trans (h k)))) ((div_lt_iff₀ positive).1 hk)

/-- A one-sided bounded multiplication discrepancy at the doubling iterates
suffices. The witness B may depend on the multiplier, without any estimate. -/
theorem transfer (a b : ℕ → ℝ) (L U w : ℝ) (hw : 0 ≤ w)
    (lo : ∀ k, 4 * a k - L ≤ a (k + 1))
    (hi : ∀ k, b (k + 1) ≤ 4 * b k + U)
    (degree : ∃ B : ℝ, ∀ k, w * a k ≤ b k + B) :
    w * (a 0 - L / 3) - U / 3 ≤ b 0 := by
  obtain ⟨B, degree⟩ := degree
  have scaled := nonpos_of_bounded_scaled
    (w * (a 0 - L / 3) - (b 0 + U / 3)) (B - U / 3 - w * (L / 3)) (fun k => by
      have lb := mul_le_mul_of_nonneg_left (iterate_lower a L lo k) hw
      have ub := iterate_upper b U hi k
      nlinarith only [lb, ub, degree k])
  linarith

/-- A global multiplication bound on the orbit implies the required one-sided comparison. -/
def MultiplicationBound (h : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ B : ℝ, ∀ k : ℕ, (n : ℝ) ^ 2 * h (2 ^ k) ≤ h (2 ^ k * n) + B

/-- It suffices to lower-bound the second differences on dyadic points.
The finite error C is uniform in k; the resulting error for [n] may grow with n. -/
theorem multiplication_of_parallelogram (h : ℕ → ℝ) (origin : h 0 = 0) (C : ℝ)
    (lower : ∀ k j : ℕ, 2 * h (2^k * (j+1)) + 2 * h (2^k) - C ≤
      h (2^k * (j+2)) + h (2^k * j)) (n : ℕ) : MultiplicationBound h n := by
  refine ⟨(n:ℝ) * ((n:ℝ)-1) / 2 * C, fun k => ?_⟩
  let d (j : ℕ) : ℝ := h (2^k * j) - ((j:ℝ)^2 * h (2^k) - (j:ℝ) * ((j:ℝ)-1) / 2 * C)
  have inc (j : ℕ) : d j ≤ d (j+1) := by
    induction j with
    | zero => simp [d, origin]
    | succ j ih =>
      change d (j+1) ≤ d (j+2)
      dsimp only [d] at ih ⊢
      push_cast at ih ⊢
      nlinarith only [ih, lower k j]
  have hdn := (monotone_nat_of_le_succ inc) (Nat.zero_le n)
  simp only [d, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero,
    zero_div, sub_zero, origin] at hdn
  linarith

private theorem manuscript_margin :
    1 ≤ Real.log 41 - Real.log 392 / 3 - Real.log 676 / 12 := by
  have t := Real.log_le_log (x := (2:ℝ)^20 * 392^4 * 676) (y := (41:ℝ)^12)
    (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at t
  norm_num1 at t
  linarith [Real.log_two_gt_d9]

/-- The manuscript bounds already give the coefficient 1 with no additive loss. -/
theorem baseline_index (h : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) (hP : h 1 = Real.log 41)
    (lo : ∀ k : ℕ, 4 * h (2 ^ k) - Real.log 392 ≤ h (2 ^ (k + 1)))
    (hi : ∀ k : ℕ, h (2 ^ (k + 1) * n) ≤ 4 * h (2 ^ k * n) + Real.log 676)
    (degree : MultiplicationBound h n) : (n : ℝ) ^ 2 ≤ h n := by
  by_cases one : n = 1
  · subst n
    rw [hP]
    have e := Real.log_le_log (x := (2 : ℝ)^2) (y := 41) (by norm_num) (by norm_num)
    rw [Real.log_pow] at e
    norm_num at e ⊢
    linarith [Real.log_two_gt_d9]
  have two : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have sq : (4 : ℝ) ≤ (n : ℝ)^2 := by nlinarith [sq_nonneg ((n : ℝ)-2)]
  have r := transfer (fun k : ℕ => h (2^k)) (fun k : ℕ => h (2^k*n))
    (Real.log 392) (Real.log 676) ((n : ℝ)^2) (sq_nonneg _) lo hi degree
  simp only [pow_zero, one_mul, hP] at r
  have m := mul_le_mul_of_nonneg_left manuscript_margin (sq_nonneg (n : ℝ))
  have u := mul_nonneg (sub_nonneg.2 sq) (Real.log_pos (by norm_num : (1:ℝ)<676)).le
  nlinarith only [m, u, r]

private theorem sharp_margin :
    Real.log 4 ≤ 3 * Real.log 4905889 - 12 * Real.log 41 := by
  have t := Real.log_le_log (x := (4 : ℝ)*41^12) (y := (4905889 : ℝ)^3)
    (by positivity) (by norm_num)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at t
  norm_num1 at t
  linarith

/-- For the orbit with no base-ideal loss, a single explicit double gives
a lower bound with the sharp possible common base 41, attained at n = 1. -/
theorem sharp_index (h : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0)
    (hP : h 1 = Real.log 41) (h2P : h 2 = Real.log 4905889)
    (lo : ∀ k : ℕ, 4 * h (2 ^ (k + 1)) ≤ h (2 ^ (k + 2)))
    (hi : ∀ k : ℕ, h (2 ^ (k + 1) * n) ≤ 4 * h (2 ^ k * n) + Real.log 4)
    (degree : MultiplicationBound h n) : (n : ℝ)^2 * Real.log 41 ≤ h n := by
  by_cases one : n = 1
  · subst n; simp [hP]
  have two : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have sq : (4 : ℝ) ≤ (n : ℝ)^2 := by nlinarith [sq_nonneg ((n : ℝ)-2)]
  obtain ⟨B, cmp⟩ := degree
  have comp : ∃ c : ℝ, ∀ k : ℕ, (n : ℝ)^2 * h (2 ^ (k + 1)) ≤ h (2 ^ (k + 1) * n) + c :=
    ⟨B, fun k => cmp (k+1)⟩
  have r := transfer (fun k : ℕ => h (2 ^ (k+1))) (fun k : ℕ => h (2 ^ (k+1)*n))
    0 (Real.log 4) ((n : ℝ)^2) (sq_nonneg _) (by simpa using lo) (fun k => hi (k+1)) comp
  simp only [Nat.zero_add, pow_one, zero_div, sub_zero, h2P] at r
  have init := hi 0
  simp only [Nat.zero_add, pow_one, pow_zero, one_mul] at init
  have m := mul_le_mul_of_nonneg_left sharp_margin (sq_nonneg (n : ℝ))
  have u := mul_nonneg (sub_nonneg.2 sq) (Real.log_pos (by norm_num : (1:ℝ)<4)).le
  nlinarith only [m, u, r, init]

/-- Multiplicative statement in the ordinary Weil-height normalization H = exp h. -/
theorem multiplicative_index (h : ℕ → ℝ) (n : ℕ)
    (bound : (n : ℝ)^2 * Real.log 41 ≤ h n) : (41 : ℝ) ^ (n^2) ≤ Real.exp (h n) := by
  apply (Real.log_le_iff_le_exp (by positivity)).1
  rw [Real.log_pow, Nat.cast_pow]
  exact bound

/-- Exact dyadic duplication and a generator value in isolation cannot
control a different odd orbit. This explicitly fails at the multiplier 3. -/
theorem doubling_alone :
    ∃ h : ℕ → ℝ, h 1 = Real.log 41 ∧ (∀ n, h (2*n) = 4*h n) ∧ h 3 = 0 := by
  let h (n : ℕ) : ℝ := if 3 ∣ n then 0 else (n : ℝ)^2 * Real.log 41
  refine ⟨h, ?_, ?_, ?_⟩
  · norm_num [h]
  · intro n
    have hdiv : 3 ∣ 2*n ↔ 3 ∣ n := by omega
    by_cases three : 3∣n
    · simp [h, hdiv, three]
    · simp [h, hdiv, three]; ring
  · norm_num [h]

#print axioms exists_canonical_limit
#print axioms transfer
#print axioms multiplication_of_parallelogram
#print axioms baseline_index
#print axioms sharp_index
#print axioms multiplicative_index
#print axioms doubling_alone
end EllipticHeight.Canonical
