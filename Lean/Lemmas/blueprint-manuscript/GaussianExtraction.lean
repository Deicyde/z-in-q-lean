import ManuscriptArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Extraction of one simultaneous prime tuple from the positive joint Gaussian
count. All prescribed ray classes and pairwise local conditions are inherited
from the support of the weights. -/
namespace ManuscriptV15.Arithmetic
open Filter
open scoped BigOperators Topology

/-- At strip exponent 1/4, slow decay forces the integer part of τ(X)√X
to be positive for all sufficiently large X. -/
private theorem eventually_positive_width {k : ℕ} {τ : ℝ → ℝ}
    (hpos : ∀ X, 0 < τ X)
    (hslow : Tendsto (fun X => τ X * Real.exp ((1/2-(1/4:ℝ))*Real.log X) /
      (Real.log X)^k) atTop atTop) :
    ∀ᶠ X : ℝ in atTop, 0 < ⌊τ X * Real.sqrt X⌋₊ := by
  filter_upwards [hslow.eventually_ge_atTop 1, eventually_ge_atTop (Real.exp 1)]
    with X hg hX
  have hXp : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlog : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hpow : 1 ≤ (Real.log X)^k := one_le_pow₀ hlog
  have hroot : Real.exp ((1/2-(1/4:ℝ))*Real.log X) ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXp]
    apply Real.exp_le_exp.mpr
    linarith
  have h1 : (Real.log X)^k ≤ τ X * Real.exp ((1/2-(1/4:ℝ))*Real.log X) := by
    simpa using (le_div_iff₀ (by positivity : 0<(Real.log X)^k)).mp hg
  apply Nat.floor_pos.mpr
  exact hpow.trans (h1.trans (mul_le_mul_of_nonneg_left hroot (hpos X).le))

/-- A single positive count produces parameters with arbitrarily large u/w²
and primes above any prescribed threshold. No numerical value of the
asymptotic constants or of the diagonal cutoff is required. -/
theorem gaussianTuples_of_count (count : GaussianCount) : GaussianTuples := by
  classical
  intro k hk c hc q M hq hM oddM sfM h7 H Y hH hY
  obtain ⟨c₀,C,τ,hc₀,_,ht,_,hzero,hslow,hcount⟩ :=
    count k hk c hc q M hq hM oddM sfM h7 (1/4) (by norm_num) (by norm_num)
  have small (B : ℝ) : ∀ᶠ X : ℝ in atTop, B*(τ X)^2 < 1/4 := by
    have h : Tendsto (fun X => B*(τ X)^2) atTop (𝓝 (B*(0:ℝ)^2)) :=
      tendsto_const_nhds.mul (hzero.pow 2)
    exact h.eventually_lt_const (by norm_num)
  have hcoeff : ∀ᶠ X : ℝ in atTop, ∀ i : Fin k, |(c i : ℝ)| * (τ X)^2 < 1/4 :=
    Filter.eventually_all.mpr (fun i => small |(c i : ℝ)|)
  have large := (eventually_gt_atTop (4*Y)).and ((small H).and
    (hcoeff.and ((eventually_positive_width ht hslow).and hcount)))
  obtain ⟨X,hXY,hsmall,hco,hwidth,hcount⟩ := large.exists
  let T := ⌊τ X * Real.sqrt X⌋₊
  have hX : 0 < X := by linarith
  obtain ⟨ω,_,support,mass⟩ := hcount
  obtain ⟨u,w,huω⟩ : ∃ u w : ℕ, ω u w ≠ 0 := by
    by_contra! hall
    have hsum : (∑ u ∈ Finset.range (⌊X⌋₊+1),
      ∑ w ∈ Finset.range (T+1), ω u w) = 0 := by simp [hall]
    rw [hsum] at mass
    have hm : 0 < c₀*X*(T:ℝ) := mul_pos (mul_pos hc₀ hX) (by exact_mod_cast hwidth)
    exact hm.not_ge mass
  obtain ⟨hux,_,hw,hwT,p,pattern⟩ := support u w huω
  have hu : 0 < u := by
    have : (0:ℝ)<u := by linarith
    exact_mod_cast this
  have hw' : 0 < (w:ℝ) := by exact_mod_cast hw
  have hwle : (w:ℝ) ≤ τ X * Real.sqrt X := by
    exact (show (w:ℝ) ≤ (T:ℝ) by exact_mod_cast hwT).trans
      (Nat.floor_le (mul_nonneg (ht X).le (Real.sqrt_nonneg X)))
  have hwsq : (w:ℝ)^2 ≤ (τ X)^2*X := by
    calc (w:ℝ)^2 ≤ (τ X * Real.sqrt X)^2 :=
           (sq_le_sq₀ hw'.le (mul_nonneg (ht X).le (Real.sqrt_nonneg X))).mpr hwle
         _ = _ := by rw [mul_pow,Real.sq_sqrt hX.le]
  have bound {B : ℝ} (hB : 0 ≤ B) (hsmallB : B*(τ X)^2 < 1/4) :
      B*(w:ℝ)^2 < X/4 := by
    calc B*(w:ℝ)^2 ≤ B*((τ X)^2*X) := mul_le_mul_of_nonneg_left hwsq hB
         _ = B*(τ X)^2*X := by ring
         _ < (1/4)*X := mul_lt_mul_of_pos_right hsmallB hX
         _ = X/4 := by ring
  refine ⟨u,w,hu,hw,(lt_div_iff₀ (sq_pos_of_pos hw')).mpr (by linarith [bound hH.le hsmall]),
    p,pattern,?_⟩
  obtain ⟨_,π,hπ,_⟩ := pattern
  intro j
  have heq : (p j:ℝ) = (u:ℝ)+(c j:ℝ)*(w:ℝ)^2 := by exact_mod_cast (hπ j).1
  have lower := mul_le_mul_of_nonneg_right (neg_abs_le (c j:ℝ)) (sq_nonneg (w:ℝ))
  rw [heq]
  linarith [bound (abs_nonneg (c j:ℝ)) (hco j)]

end ManuscriptV15.Arithmetic
#print axioms ManuscriptV15.Arithmetic.gaussianTuples_of_count
