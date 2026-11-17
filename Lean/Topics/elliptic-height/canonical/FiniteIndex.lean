import SymmetricNumerator

namespace EllipticHeight.FiniteIndex
open EllipticHeight.Canonical

/-- Only the second differences through n are required. Subtract the quadratic
barrier and telescope its nonnegative first differences. -/
theorem second_differences (a : ℕ → ℝ) (n : ℕ) (C : ℝ) (origin : a 0 = 0)
    (second : ∀ j : ℕ, j+2 ≤ n → 2*a (j+1)+2*a 1-C ≤ a (j+2)+a j) :
    (n:ℝ)^2*a 1 - (n:ℝ)*((n:ℝ)-1)*C/2 ≤ a n := by
  let d (j : ℕ) : ℝ := a j - ((j:ℝ)^2*a 1 - (j:ℝ)*((j:ℝ)-1)*C/2)
  have inc (j : ℕ) : j+1 ≤ n → d j ≤ d (j+1) := by
    induction j with
    | zero => intro _; simp [d,origin]
    | succ j ih =>
      intro bound
      change d (j+1) ≤ d (j+2)
      have prev := ih (by omega)
      dsimp only [d] at prev ⊢
      push_cast at prev ⊢
      nlinarith only [prev, second j bound]
  have growth (j : ℕ) : j ≤ n → 0 ≤ d j := by
    induction j with
    | zero => intro _; simp [d,origin]
    | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (inc j hj)
  have e := growth n (le_refl _)
  dsimp only [d] at e
  linarith

/-- One application of the upper addition law at each j, together with lower
duplication for 2(j+1)P and 2P, produces the second differences for h(2jP). -/
theorem even_second (h : ℕ → ℝ) (j : ℕ) (U : ℝ)
    (lowerMid : 4*h (2*(j+1)) ≤ h (4*(j+1)))
    (lowerBase : 4*h 2 ≤ h 4)
    (pair : h (4*(j+1))+h 4 ≤ 2*h (2*(j+2))+2*h (2*j)+U) :
    2*h (2*(j+1))+2*h 2-U/2 ≤ h (2*(j+2))+h (2*j) := by linarith

/-- The finite estimate uses only heights through 4(n−1) and one upper doubling. -/
theorem finite_bound (h : ℕ → ℝ) (n : ℕ) (U : ℝ) (origin : h 0 = 0)
    (lower : ∀ j : ℕ, j+2 ≤ n → 4*h (2*(j+1)) ≤ h (4*(j+1)))
    (baseDouble : 4*h 2 ≤ h 4)
    (pair : ∀ j : ℕ, j+2 ≤ n →
      h (4*(j+1))+h 4 ≤ 2*h (2*(j+2))+2*h (2*j)+U)
    (upper : h (2*n) ≤ 4*h n+U) :
    (n:ℝ)^2*h 2/4 - ((n:ℝ)*((n:ℝ)-1)+4)*U/16 ≤ h n := by
  have e := second_differences (fun i => h (2*i)) n (U/2) (by simpa using origin)
    (fun j hj => by simpa only [Nat.mul_one] using even_second h j U (lower j hj) baseDouble (pair j hj))
  simp only [Nat.mul_one] at e
  linarith

/-- Exact integer certificate at the worst finite index n=2. -/
theorem margin : 3*Real.log 4 ≤ 8*Real.log 4905889-32*Real.log 41 := by
  have cmp := Real.log_le_log (x := (4:ℝ)^3 * 41^32) (y := (4905889:ℝ)^8)
    (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at cmp
  norm_num1 at cmp
  linarith

theorem sharp_finite (h : ℕ → ℝ) (n : ℕ) (nonzero : n ≠ 0) (origin : h 0 = 0)
    (base : h 1 = Real.log 41) (firstDouble : h 2 = Real.log 4905889)
    (lower : ∀ j : ℕ, j+2 ≤ n → 4*h (2*(j+1)) ≤ h (4*(j+1)))
    (baseDouble : 4*h 2 ≤ h 4)
    (pair : ∀ j : ℕ, j+2 ≤ n →
      h (4*(j+1))+h 4 ≤ 2*h (2*(j+2))+2*h (2*j)+Real.log 4)
    (upper : h (2*n) ≤ 4*h n+Real.log 4) : (n:ℝ)^2 * Real.log 41 ≤ h n := by
  by_cases one : n = 1
  · subst n; simp [base]
  have two : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have loss : 2*((n:ℝ)*((n:ℝ)-1)+4) ≤ 3*(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-2)]
  have res := finite_bound h n (Real.log 4) origin lower baseDouble pair upper
  rw [firstDouble] at res
  have a := mul_le_mul_of_nonneg_right loss (Real.log_pos (by norm_num : (1:ℝ)<4)).le
  have b := mul_le_mul_of_nonneg_left margin (sq_nonneg (n:ℝ))
  nlinarith only [res,a,b]

/-- Interface for primitive integral numerators W(i) = |Norm(A_i)|.
All inequalities in the statement, including the bound for the circuit row,
are over natural numbers. The requested comparisons only cover j+2 ≤ n. -/
theorem integer_numerator_index (W : ℕ → ℕ) (n : ℕ) (nonzero : n ≠ 0)
    (positive : ∀ i, 0 < W i) (origin : W 0 = 1)
    (base : W 1=41^2) (firstDouble : W 2=4905889^2)
    (lower : ∀ j : ℕ, j+2 ≤ n → W (2*(j+1))^4 ≤ W (4*(j+1)))
    (baseDouble : W 2^4 ≤ W 4)
    (pair : ∀ j : ℕ, j+2 ≤ n →
      W (4*(j+1))*W 4 ≤ 16*W (2*(j+2))^2*W (2*j)^2)
    (upper : W (2*n) ≤ 16*W n^4) : (41^(n^2))^2 ≤ W n := by
  let h (i : ℕ) : ℝ := Real.log (W i : ℝ)/2
  have pos (i : ℕ) : 0 < (W i : ℝ) := by exact_mod_cast positive i
  have log16 : Real.log (16:ℝ) = 2*Real.log 4 := by
    rw [show (16:ℝ)=(4:ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  have down (a b : ℕ) (z : W a^4 ≤ W b) : 4*h a ≤ h b := by
    have cmp : (W a:ℝ)^4 ≤ W b := by exact_mod_cast z
    have e := Real.log_le_log (pow_pos (pos a) 4) cmp
    rw [Real.log_pow] at e
    norm_num1 at e
    dsimp [h]
    linarith
  have zup : (W (2*n):ℝ) ≤ 16*(W n:ℝ)^4 := by exact_mod_cast upper
  have up := Real.log_le_log (pos (2*n)) zup
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ (pos n).ne'), Real.log_pow, log16] at up
  norm_num1 at up
  have zi : (W 1 : ℝ) = (41:ℝ)^2 := by exact_mod_cast base
  have zii : (W 2 : ℝ) = (4905889:ℝ)^2 := by exact_mod_cast firstDouble
  have hone : h 1=Real.log 41 := by dsimp [h]; rw [zi, Real.log_pow]; norm_num
  have htwo : h 2=Real.log 4905889 := by dsimp [h]; rw [zii, Real.log_pow]; norm_num
  have bound := sharp_finite h n nonzero (by simp [h,origin]) hone htwo
    (fun j hj => down _ _ (lower j hj)) (down 2 4 baseDouble) (fun j hj => by
      let a := 4*(j+1)
      let b := 2*(j+2)
      let c := 2*j
      have cmp : (W a:ℝ)*(W 4:ℝ) ≤ 16*(W b:ℝ)^2*(W c:ℝ)^2 := by exact_mod_cast pair j hj
      have e := Real.log_le_log (mul_pos (pos a) (pos 4)) cmp
      rw [Real.log_mul (pos _).ne' (pos _).ne',
        Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ (pos b).ne')) (pow_ne_zero _ (pos c).ne'),
        Real.log_mul (by norm_num) (pow_ne_zero _ (pos b).ne'), Real.log_pow, Real.log_pow, log16] at e
      norm_num1 at e
      change h a+h 4 ≤ 2*h b+2*h c+Real.log 4
      dsimp only [h]
      linarith) (by dsimp only [h]; linarith)
  have realBound : ((41:ℝ)^(n^2))^2 ≤ (W n:ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (pos n)).1
    rw [Real.log_pow, Real.log_pow, Nat.cast_pow]
    norm_num1
    dsimp only [h] at bound
    linarith
  exact_mod_cast realBound

#print axioms second_differences
#print axioms even_second
#print axioms finite_bound
#print axioms margin
#print axioms sharp_finite
#print axioms integer_numerator_index
end EllipticHeight.FiniteIndex
