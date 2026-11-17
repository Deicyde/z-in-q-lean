import MarkedHeights
import Mathlib.Tactic.Bound

namespace Sun28.Ordinary
open Height

/-- Uniform quartic bound on the full range used at the multiplier cutoff. -/
theorem lucas_abs_bound {s t z B : ℝ} (b : 2≤B) (hs : |s|≤B) (ht : |t|≤B) (hz : |z|≤B) :
    |lucas s t z|≤8*B^4 := by
  have B0 : 0≤B := by linarith
  have two : |s-2|≤2*B := by
    calc
      _ ≤ |s| + |(-2:ℝ)| := by simpa only [sub_eq_add_neg] using abs_add_le s (-2)
      _ ≤ _ := by norm_num; linarith
  have ts := pow_le_pow_left₀ (abs_nonneg t) ht 2
  have sz := pow_le_pow_left₀ (abs_nonneg (s-2)) two 2
  have zz := pow_le_pow_left₀ (abs_nonneg z) hz 2
  have mid : |s*(s-2)*t*z| ≤ (B*(2*B)*B*B) := by
    rw [abs_mul,abs_mul,abs_mul]
    bound
  have last : |(s-2)^2*z^2| ≤ (2*B)^2*B^2 := by
    rw [abs_mul,abs_pow,abs_pow]
    bound
  have first : |t^2|≤B^2 := by simpa only [abs_pow] using ts
  have tri (a b c d : ℝ) : |a-b+c-d|≤|a|+|b|+|c|+|d| := by
    simp only [sub_eq_add_neg]
    calc
      _ ≤ |a+-b+c|+|-d| := abs_add_le _ _
      _ ≤ (|a+-b|+|c|)+|-d| := by gcongr; apply abs_add_le
      _ ≤ ((|a|+|-b|)+|c|)+|-d| := by gcongr; apply abs_add_le
      _ = _ := by simp
  have B2 : 1≤B^2 := one_le_pow₀ (by linarith) (n:=2)
  have B4 : B^2≤B^4 := by nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr B2)]
  calc
    |lucas s t z| ≤ |t^2|+|s*(s-2)*t*z|+|(s-2)^2*z^2|+|1| := tri _ _ _ _
    _ ≤ _ := by rw [abs_one]; nlinarith only [first,mid,last,B2,B4]

theorem lucas_small_exception : |lucas (-1:ℤ) 1 (-1)|=12 := by norm_num [lucas]

/-- The explicit multiplier places every admissible tuple in the valid quartic range. -/
theorem actual_cutoff {D S c hβ : ℝ} (dp : 1≤D) (sc : 0≤S) (n : Fin 4 → ℤ)
    (hc : (Sun28.multiplier D (numeratorConstant D) S : ℝ)≤c) (size : c-1≤ indexSize n)
    (ordinary : lucas (n 1) (n 2) (n 3)≠0 → (indexSize n)^2≤D*
      (1+|((lucas (n 1) (n 2) (n 3):ℤ):ℝ)|^(3/8:ℝ)))
    (scalar : hβ≤S*Real.sqrt c) :
    lucas (n 1) (n 2) (n 3)=0 ∧ numeratorConstant D+3*hβ<c-4 := by
  have m8 := (Sun28.multiplier_spec (K:=numeratorConstant D) (zero_le_one.trans dp) sc).2.1
  have m8r : (8:ℝ)≤Sun28.multiplier D (numeratorConstant D) S := by exact_mod_cast m8
  have big : 2≤ indexSize n := by linarith
  have bnd (i : Fin 4) : |(n i:ℝ)|≤ indexSize n := by
    fin_cases i <;> simp [indexSize]
  have h := lucas_abs_bound big (bnd 1) (bnd 2) (bnd 3)
  have p : ((lucas (n 1) (n 2) (n 3):ℤ):ℝ)=lucas (n 1:ℝ) (n 2:ℝ) (n 3:ℝ) := by
    simp [lucas]
  apply cutoff_from_ordinary dp sc hc size _ ordinary scalar
  rw [p]
  linarith [show 0≤(indexSize n)^4 by positivity]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.lucas_abs_bound
#print axioms Sun28.Ordinary.lucas_small_exception
#print axioms Sun28.Ordinary.actual_cutoff
