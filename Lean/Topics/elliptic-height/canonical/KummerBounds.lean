import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace EllipticHeight.Kummer

/-- Homogeneous coordinates of the double on the Kummer line of y² = x³ − D x. -/
def F (D a b : ℝ) : ℝ := (a ^ 2 + D * b ^ 2) ^ 2
def G (D a b : ℝ) : ℝ := 4 * (a * b) * (a ^ 2 - D * b ^ 2)
def size (a b : ℝ) : ℝ := max (a ^ 2) (b ^ 2)

private theorem ab_le_size (a b : ℝ) : |a*b| ≤ size a b := by
  have ha := le_max_left (a^2) (b^2)
  have hb := le_max_right (a^2) (b^2)
  apply abs_le.2
  dsimp only [size]
  constructor <;> nlinarith [sq_nonneg (a+b), sq_nonneg (a-b)]

theorem size_square (a b : ℝ) : (max |a| |b|)^2 = size a b := by
  rcases le_total |a| |b| with h | h
  · have e := pow_le_pow_left₀ (abs_nonneg a) h 2
    simp only [sq_abs] at e
    simp [max_eq_right h, size, max_eq_right e]
  · have e := pow_le_pow_left₀ (abs_nonneg b) h 2
    simp only [sq_abs] at e
    simp [max_eq_left h, size, max_eq_left e]

/-- At either embedding, all projective inputs have coefficient (1+D)². -/
theorem real_place (D a b : ℝ) (hd : 1 ≤ D) :
    (size a b)^2 ≤ max |F D a b| |G D a b| ∧
      max |F D a b| |G D a b| ≤ (1+D)^2 * (size a b)^2 := by
  let S := size a b
  have aa : a^2 ≤ S := le_max_left _ _
  have bb : b^2 ≤ S := le_max_right _ _
  have ss : 0 ≤ S := (sq_nonneg a).trans aa
  have d0 : 0 ≤ D := by linarith
  have db := mul_le_mul_of_nonneg_left bb d0
  have sa : S ≤ a^2+D*b^2 := max_le (by linarith [mul_nonneg d0 (sq_nonneg b)]) (by nlinarith [sq_nonneg a, mul_nonneg (sub_nonneg.2 hd) (sq_nonneg b)])
  have up : a^2+D*b^2 ≤ (1+D)*S := by nlinarith only [aa, db]
  have lowF : S^2 ≤ F D a b := pow_le_pow_left₀ ss sa 2
  have upF := pow_le_pow_left₀ (ss.trans sa) up 2
  have ds : S ≤ D*S := by nlinarith [mul_nonneg (sub_nonneg.2 hd) ss]
  have diff : |a^2-D*b^2| ≤ D*S := abs_le.2 ⟨by nlinarith [sq_nonneg a], by nlinarith [mul_nonneg d0 (sq_nonneg b)]⟩
  have gu := mul_le_mul (ab_le_size a b) diff (abs_nonneg _) ss
  have gc := mul_nonneg (sq_nonneg (D-1)) (sq_nonneg S)
  have signF : 0 ≤ F D a b := sq_nonneg _
  rw [abs_of_nonneg signF]
  refine ⟨lowF.trans (le_max_left ..), max_le ?_ ?_⟩
  · dsimp only [F]
    change _ ≤ (1+D)^2 * S^2
    nlinarith only [upF]
  · simp only [G, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [abs_mul] at gu
    change 4 * (|a| * |b|) * |a^2 - D*b^2| ≤ (1+D)^2 * S^2
    change |a| * |b| * |a^2-D*b^2| ≤ S*(D*S) at gu
    nlinarith only [gu, gc]

/-- The two local coefficients have geometric mean 72 for D = 11±6√2. -/
theorem conjugate_coefficients (s : ℝ) (hs : s^2 = 2) :
    1 ≤ 11-6*s ∧ 1 ≤ 11+6*s ∧
      (1+(11-6*s))^2 * (1+(11+6*s))^2 = 72^2 := by
  have prod : (1+(11-6*s)) * (1+(11+6*s)) = 72 := by nlinarith
  refine ⟨by nlinarith [sq_nonneg (s-2)], by nlinarith [sq_nonneg (s+2)], ?_⟩
  rw [← mul_pow, prod]

/-- On the real identity component x² ≥ D and D ≥ 1 give coefficient 4.
The homogeneous statement includes the input b = 0. -/
theorem expanding_place (D a b : ℝ) (hd : 1 ≤ D) (branch : D * b^2 ≤ a^2) :
    (size a b)^2 ≤ max |F D a b| |G D a b| ∧
      max |F D a b| |G D a b| ≤ 4 * (size a b)^2 := by
  refine ⟨(real_place D a b hd).1, ?_⟩
  have hD : 0 ≤ D := by linarith
  have hd2 := mul_nonneg (sub_nonneg.2 hd) (sq_nonneg b)
  have b2 : b^2 ≤ a^2 := by nlinarith
  have s : size a b = a^2 := max_eq_left b2
  rw [s]
  apply max_le
  · have sem : 0 ≤ a^2 + D*b^2 := by positivity
    have hi : a^2+D*b^2 ≤ 2*a^2 := by linarith
    have := pow_le_pow_left₀ sem hi 2
    dsimp only [F]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  · have ab := ab_le_size a b
    rw [s] at ab
    have d : |a^2-D*b^2| ≤ a^2 := by
      rw [abs_of_nonneg (sub_nonneg.2 branch)]
      nlinarith [mul_nonneg hD (sq_nonneg b)]
    have m := mul_le_mul ab d (abs_nonneg _) (sq_nonneg a)
    simp only [G, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [abs_mul] at m
    nlinarith only [m]

#print axioms size_square
#print axioms real_place
#print axioms conjugate_coefficients
#print axioms expanding_place
end EllipticHeight.Kummer
