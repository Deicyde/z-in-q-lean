import PoleHeightExact
import ZInQKernel.MainLiterature

/-! The degree-twelve height comparison from the exact denominator, with explicit loss. -/
namespace ZInQBlueprint.PoleNorm
open ZInQ
noncomputable section

private theorem param_integral (u : ℚ) (hu : u ≠ 0) :
    parameter u = ((5*u.num+120*(u.den:ℤ):ℤ):ℚ)/(u.num:ℚ) := by
  have ha : u.num ≠ 0 := fun h => hu (Rat.zero_of_num_zero h)
  have hb : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  have har : (u.num:ℚ) ≠ 0 := by exact_mod_cast ha
  unfold parameter
  push_cast
  conv_lhs => rw [← Rat.num_div_den u]
  field_simp [har,hb]

/-- The common scale of the pair 5a+120b,a divides the determinant 120. -/
theorem denominator_scale (u : ℚ) (hu : u ≠ 0) :
    ∃ c : ℤ, c ∣ 120 ∧
      5*u.num+120*(u.den:ℤ) = c*(parameter u).num ∧ u.num=c*((parameter u).den:ℤ) := by
  have ha : u.num ≠ 0 := fun h => hu (Rat.zero_of_num_zero h)
  obtain ⟨c,hm,hn⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den (5*u.num+120*(u.den:ℤ)) ha
  rw [←param_integral u hu] at hm hn
  have hcop : IsCoprime u.num (u.den:ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact u.reduced
  obtain ⟨x,y,hxy⟩ := hcop
  refine ⟨c, ⟨(120*x-5*y)*(parameter u).den+y*(parameter u).num, ?_⟩,hm,hn⟩
  linear_combination -(120:ℤ)*hxy + (120*x-5*y)*hn+y*hm

theorem factor_le (p q : ℤ) : factor p q ≤ 12 := by
  unfold factor dyadicFactor triadicFactor
  split <;> split <;> decide

private theorem both_even_forbidden {x y : ℤ} (hc : IsCoprime x y) :
    ¬ (2:ℤ) ∣ x ∨ ¬ (2:ℤ) ∣ y := by
  obtain ⟨a,b,h⟩ := hc
  by_contra! bad
  have h₂ : (2:ℤ) ∣ a*x+b*y :=
    dvd_add (dvd_mul_of_dvd_right bad.1 a) (dvd_mul_of_dvd_right bad.2 b)
  rw [h] at h₂
  norm_num at h₂

private theorem abs_proper_divisor {c : ℤ} (hc : c ∣ 120) :
    |c| ≤ 60 ∨ |c| = 120 := by
  obtain ⟨k,hk⟩ := (abs_dvd _ _).mpr hc
  have hkpos : 0<k := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg c) h
    omega
  rcases eq_or_lt_of_le (show 1≤k by omega) with h₁|h₂
  · right
    rw [← h₁,mul_one] at hk
    exact hk.symm
  · left
    have := mul_le_mul_of_nonneg_left (show 2 ≤ k by omega) (abs_nonneg c)
    omega

/-- The dyadic correction cannot occur when the change of coordinates cancels 120. -/
theorem scale_factor_bound {a b c p q : ℤ} (hab : IsCoprime a b) (hc : c ∣ 120)
    (h₁ : 5*a+120*b=c*p) (h₂ : a=c*q) : c^2*factor p q ≤ 43200 := by
  rcases abs_proper_divisor hc with small|full
  · have hc2 : c^2 ≤ 3600 := by nlinarith [sq_abs c,abs_nonneg c]
    exact (mul_le_mul hc2 (factor_le p q) (factor_pos p q).le (by norm_num)).trans_eq (by norm_num)
  · have alt : c=120 ∨ c= -120 := by
      rcases le_or_gt 0 c with pos|neg
      · exact Or.inl (by simpa [abs_of_nonneg pos] using full)
      · exact Or.inr (by rw [abs_of_neg neg] at full; omega)
    have even_a : (2:ℤ) ∣ a := by rcases alt with hc|hc <;> rw [hc] at h₂ <;> omega
    have odd_b := (both_even_forbidden hab).resolve_left (not_not.mpr even_a)
    have hd : dyadicFactor p q = 1 := by
      unfold dyadicFactor
      apply ite_eq_right
      rintro ⟨hp,hq⟩
      apply odd_b
      rcases alt with hc|hc <;> rw [hc] at h₁ h₂ <;> omega
    have h3 : triadicFactor p ≤ 3 := by unfold triadicFactor; split <;> decide
    unfold factor
    rw [hd,one_mul]
    rcases alt with hc|hc <;> rw [hc] <;> nlinarith

/-- For the original primitive parameter, H² ≤ 14400 times the denominator root. -/
theorem height_square_le (u : ℚ) (hu : u ≠ 0) :
    (max |u.num| (u.den:ℤ))^2 ≤ 14400*denominatorRoot u := by
  obtain ⟨c,hc,hp,hq⟩ := denominator_scale u hu
  let p := (parameter u).num
  let q := ((parameter u).den:ℤ)
  let a := u.num
  let b := (u.den:ℤ)
  change 5*a+120*b=c*p at hp
  change a=c*q at hq
  have hab : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact (parameter u).reduced
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact u.reduced
  have eN : c^2*norm p q=(5*a+120*b)^2+3*a^2 := by
    rw [hp,hq]
    unfold norm
    ring
  have hl : (max |a| b)^2*3 ≤ c^2*norm p q := by
    rw [eN]
    rcases le_total |a| b with h|h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (7*a+150*b),sq_nonneg b]
    · rw [max_eq_left h,sq_abs]
      nlinarith [sq_nonneg (5*a+120*b)]
  rw [norm_eq hab, ← mul_assoc] at hl
  have upper := mul_le_mul_of_nonneg_right (scale_factor_bound hcop hc hp hq)
    (reduced_pos hab (by dsimp [q]; exact_mod_cast (parameter u).den_pos)).le
  change (max |a| b)^2 ≤ 14400*reduced p q
  omega

theorem sharp_parameter_height (u : ℚ) (hu : u ≠ 0) :
    12 * ratHeight u ≤ ratHeight (JHeight.Jmap u) + 6*Real.log 14400 := by
  let H := max |u.num| (u.den:ℤ)
  have hH : 0 < H := (by exact_mod_cast u.den_pos : (0:ℤ)<u.den).trans_le (le_max_right ..)
  have hR : 0 < denominatorRoot u := root_pos u
  have hsq : (H:ℝ)^2 ≤ 14400*(denominatorRoot u:ℝ) := by exact_mod_cast height_square_le u hu
  have hlog := Real.log_le_log (by positivity : 0<(H:ℝ)^2) hsq
  rw [Real.log_pow,Real.log_mul (by norm_num) (by exact_mod_cast hR.ne')] at hlog
  have hHid : ratHeight u=Real.log (H:ℝ) := by
    unfold ratHeight H
    push_cast
    rfl
  rw [hHid,j_height_exact u hu]
  norm_num at hlog
  linarith

/-- Direct application to the merged bounded polynomial theorem. -/
theorem frozen_of_denominator_and_literature
    (height : ∀ u : ℚ, u ∉ contactSet →
      6*Real.log (denominatorRoot u:ℝ) ≤ (40*10000*2^24+22:ℝ) *
        JHeight.heightX heightD * (contactSupport Mult.S_mul u:ℝ)^24)
    (tyz : Literature.TYZThm35ReadingA) (hecke : Literature.HeckeContinuation)
    (sign : Literature.FunctionalEquation5) (gz : Literature.GrossZagier) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    (sixContact_of_denominator height) tyz hecke sign gz

end
end ZInQBlueprint.PoleNorm
#print axioms ZInQBlueprint.PoleNorm.denominator_scale
#print axioms ZInQBlueprint.PoleNorm.scale_factor_bound
#print axioms ZInQBlueprint.PoleNorm.height_square_le
#print axioms ZInQBlueprint.PoleNorm.sharp_parameter_height
#print axioms ZInQBlueprint.PoleNorm.frozen_of_denominator_and_literature
