import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! Explicit choices and elementary implications in Sun, arXiv:2611.14605v1, §§5–7. -/
namespace Sun28

/-- The path costs for the seven leaves of the scalar norm tree in §5. -/
def leafCost : List ℚ :=
  let left (c : ℚ) := c / 2
  let right (c : ℚ) := (c + 1) / 2
  let root : ℚ := 1 / 2
  [left (left (left root)), right (left (left root)),
   left (right (left root)), right (right (left root)), left (right root),
   left (right (right root)), right (right (right root))]

theorem scalar_leaf_costs :
    leafCost = [1/16,9/16,5/16,13/16,3/8,7/16,15/16] ∧
    ∀ c ∈ leafCost, c < 1 := by norm_num [leafCost]

/-- A direct numerical bound used in the first height contradiction. -/
theorem ordinary_cutoff {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hb : 9 * C < Real.sqrt B) :
    ¬ B^2 ≤ C * (1 + (10 * B^4) ^ (3/8 : ℝ)) := by
  have hB0 : 0 ≤ B := by linarith
  have h10 : (10:ℝ) ^ (3/8 : ℝ) ≤ 8 := by
    calc
      _ ≤ (16:ℝ) ^ (1/2 : ℝ) := by
        exact (Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 10) (by norm_num : (10:ℝ) ≤ 16)
          (by norm_num : (0:ℝ) ≤ 3/8)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
      _ ≤ _ := by rw [← Real.sqrt_eq_rpow]; norm_num
  have he : (B^4) ^ (3/8 : ℝ) = B * Real.sqrt B := by
    rw [← Real.rpow_natCast B 4, ← Real.rpow_mul hB0, Real.sqrt_eq_rpow,
      mul_comm B (B ^ (1/2 : ℝ)), ← Real.rpow_add_one (by linarith : B ≠ 0)]
    norm_num
  have hs : 1 ≤ Real.sqrt B := by
    simpa using Real.sqrt_le_sqrt hB
  have h1 : 1 ≤ B * Real.sqrt B := one_le_mul_of_one_le_of_one_le hB hs
  have hprod := mul_le_mul_of_nonneg_right h10 (by positivity : 0 ≤ B * Real.sqrt B)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) (by positivity),he]
  intro h
  have h2 := mul_le_mul_of_nonneg_left (show
    1 + (10:ℝ)^(3/8:ℝ) * (B * Real.sqrt B) ≤ 9*(B * Real.sqrt B) by linarith) hC
  have hm := mul_lt_mul_of_pos_right hb (by positivity : 0 < B * Real.sqrt B)
  nlinarith [Real.sq_sqrt hB0,congrArg (B * ·) (Real.sq_sqrt hB0)]

/-- A sufficient multiplier for both inequalities of §7, for supplied numerical bounds. -/
noncomputable def multiplier (C K S : ℝ) : ℕ :=
  6 * (2 + ⌈(9*C)^2 + 2 * (|K|+4) + (6*S)^2⌉₊)

theorem multiplier_spec {C K S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) :
    6 ∣ multiplier C K S ∧ 8 ≤ multiplier C K S ∧
    (∀ B : ℝ, (multiplier C K S : ℝ)-1 ≤ B →
        ¬ B^2 ≤ C * (1 + (10*B^4) ^ (3/8 : ℝ))) ∧
    (∀ c : ℝ, (multiplier C K S : ℝ) ≤ c →
        K + 3*S*Real.sqrt c < c-4) := by
  let Y := (9*C)^2 + 2*(|K|+4) + (6*S)^2
  have hy : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil _
  have hm : (multiplier C K S : ℝ) = 6*(2+(⌈Y⌉₊:ℝ)) := by simp [multiplier,Y]
  have h0 := abs_nonneg K
  have hK := le_abs_self K
  have hn : 0 ≤ (⌈Y⌉₊:ℝ) := by positivity
  have hmin : Y + 2 < (multiplier C K S : ℝ) := by linarith
  dsimp [Y] at hmin
  refine ⟨dvd_mul_right _ _,by simp [multiplier]; omega,?_,?_⟩
  · intro B hB
    have B1 : 1 ≤ B := by nlinarith [sq_nonneg (9*C),sq_nonneg (6*S)]
    apply ordinary_cutoff hC B1
    have hs := Real.sq_sqrt (by linarith : 0 ≤ B)
    nlinarith [sq_nonneg (6*S),Real.sqrt_nonneg B]
  · intro c hc
    have hc0 : 0 ≤ c := by nlinarith [sq_nonneg (9*C),sq_nonneg (6*S)]
    have hs := Real.sq_sqrt hc0
    have ha : 0 < Real.sqrt c := Real.sqrt_pos.2 (by nlinarith [sq_nonneg (9*C),sq_nonneg (6*S)])
    have hs' : 6*S < Real.sqrt c := by nlinarith [sq_nonneg (9*C)]
    have ht := mul_lt_mul_of_pos_right hs' ha
    nlinarith [sq_nonneg (9*C),sq_nonneg (6*S)]

/-- The denominator argument at the last line of Proposition 7.3. -/
theorem integral_input (x : ℚ) (n : ℤ) (hn : 2*x^2 + 3 = (n:ℚ)) :
    ∃ m : ℤ, x = (m:ℚ) := by
  let a := x.num
  let b := x.den
  have hq : x = (a:ℚ)/b := (Rat.num_div_den x).symm
  have hb : (b:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  rw [hq] at hn
  field_simp [hb] at hn
  have hz : (2:ℤ)*a^2+3*(b:ℤ)^2 = n*b^2 := by
    have he : (2:ℚ)*(a:ℚ)^2+3*(b:ℚ)^2 = (n:ℚ)*(b:ℚ)^2 := by nlinarith [hn]
    exact_mod_cast he
  have hd : (b:ℤ)^2 ∣ 2*a^2 := ⟨n-3,by linarith⟩
  have hnat : b^2 ∣ 2*a.natAbs^2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using (Int.natAbs_dvd_natAbs.mpr hd)
  have cop : b.Coprime a.natAbs := x.reduced.symm
  have small : b^2 ∣ 2 := (cop.pow_left 2 |>.pow_right 2).dvd_of_dvd_mul_right hnat
  have bs : b^2 ≤ 2 := Nat.le_of_dvd (by decide) small
  have b1 : b = 1 := by have := x.den_pos; change 0 < b at this; nlinarith
  exact ⟨a, by rw [hq,b1]; simp⟩

/-- Evaluation at the input followed by the twenty-eight witnesses. -/
def eval28 (F : MvPolynomial (Fin 29) ℤ) (x : ℚ) (y : Fin 28 → ℚ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cases x y) F

/-- Sun's Theorem 1.1, as a proposition. -/
def IntegerDefinition28 : Prop :=
  ∃ F : MvPolynomial (Fin 29) ℤ,
    ∀ x : ℚ, (∃ y : Fin 28 → ℚ, eval28 F x y = 0) ↔ ∃ m : ℤ, x = (m : ℚ)

/-- The pointwise transfer behind Propositions 7.3 and 7.4, followed by the
all-specializations eliminator of Proposition 10.1. The remaining arithmetic
is stated through its exact inequalities. -/
theorem projection_of_estimates {C K S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S)
    (certificate : ℚ → Prop) (F : MvPolynomial (Fin 29) ℤ)
    (compile : ∀ x, (∃ y, eval28 F x y = 0) ↔ certificate x)
    (complete : ∀ m : ℤ, certificate (m:ℚ))
    (sound : ∀ x, certificate x → ∃ (n Δ : ℤ) (B c hβ : ℝ),
      (multiplier C K S : ℝ) ≤ c ∧ c-1 ≤ B ∧ |(Δ:ℝ)| ≤ 10*B^4 ∧
      (Δ ≠ 0 → B^2 ≤ C*(1 + |(Δ:ℝ)| ^ (3/8:ℝ))) ∧
      (Δ = 0 → c-4 < Real.log B) ∧
      (2*x^2+3 ≠ (n:ℚ) → Real.log B ≤ K+3*hβ) ∧ hβ ≤ S*Real.sqrt c) :
    ∀ x, (∃ y, eval28 F x y = 0) ↔ ∃ m : ℤ, x = (m:ℚ) := by
  intro x
  rw [compile]
  constructor
  · intro hx
    obtain ⟨n,Δ,B,c,hβ,hc,hB,hΔ,hord,hluc,hnum,hsc⟩ := sound x hx
    obtain ⟨_,_,hcut,hscalar⟩ := multiplier_spec hC hS
    have hzero : Δ = 0 := by
      by_contra hd
      apply hcut B (by linarith)
      apply (hord hd).trans
      exact mul_le_mul_of_nonneg_left (add_le_add_right
        (Real.rpow_le_rpow (abs_nonneg _) hΔ (by norm_num : (0:ℝ) ≤ 3/8)) 1) hC
    apply integral_input x n
    by_contra hn
    linarith [hluc hzero,hnum hn,hscalar c hc]
  · rintro ⟨m,rfl⟩
    exact complete m

end Sun28
#print axioms Sun28.IntegerDefinition28
#print axioms Sun28.scalar_leaf_costs
#print axioms Sun28.ordinary_cutoff
#print axioms Sun28.multiplier_spec
#print axioms Sun28.integral_input
#print axioms Sun28.projection_of_estimates
