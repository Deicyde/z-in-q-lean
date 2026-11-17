import PatternSelection

namespace Sun28.FinitePattern
open Finset Filter Topology Sun28.ContactFactors Sun28.SinglePrime Sun28.ContactSieve
noncomputable section

/-- Sun's actual finite count chooses a smaller prime set, requiring both signs up to L. -/
def PaperThreshold (A : Fin 3 → ℚ) (d L : ℕ) (δ : ℝ) : Prop :=
  PatternThreshold A d L L δ

theorem mass_mono_base (A : Fin 3 → ℚ) {K L d N W : ℕ} (kl : K ≤ L) :
    patternMass A d L L N W ≤ patternMass A d K L N W := by
  have subset (p : ℕ) : commonPrime L L p → commonPrime K L p := by
    rintro ⟨prime,z,n,r16,r7,h⟩
    refine ⟨prime,z,n,r16,r7,?_⟩
    intro v prim odd seven vl
    obtain ⟨plus,minus⟩ := h v prim odd seven vl
    exact ⟨plus,fun vk => minus (vk.trans kl)⟩
  have non (K : ℕ) (m : ℤ) : 0 ≤ primeWeight K L m := by
    unfold primeWeight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.2.1.one_le)
    · rfl
  have le (m : ℤ) : primeWeight L L m ≤ primeWeight K L m := by
    by_cases old : 0 ≤ m ∧ commonPrime L L m.toNat
    · simp only [primeWeight,ite_eq_left old,ite_eq_left (And.intro old.1 (subset _ old.2)),le_refl]
    · rw [show primeWeight L L m = 0 from ite_eq_right old]
      exact non _ _
  unfold patternMass
  apply sum_le_sum
  intro q _
  exact Finset.prod_le_prod₀ (fun i _ => non _ _) (fun i _ => le _)

private theorem sqrt_dominates (k : ℕ) :
    ∀ᶠ L : ℕ in atTop, 0 < (Real.log (L : ℝ))^k ∧ (Real.log (L : ℝ))^k ≤ Real.sqrt L := by
  have lim := Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 k one_ne_zero
  have comp := lim.comp ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  have tail := comp.eventually_lt_const (show 0 < 1 / (2:ℝ)^k by positivity)
  filter_upwards [tail,eventually_gt_atTop (1:ℕ)] with L small large
  have one : 1 < (L:ℝ) := by exact_mod_cast large
  have pos : 0 < Real.sqrt (L:ℝ) := Real.sqrt_pos.2 (by linarith)
  have h : (Real.log (Real.sqrt L))^k / Real.sqrt L < 1 / (2:ℝ)^k := by
    simpa using small
  have compare := (div_lt_div_iff₀ pos (show 0 < (2:ℝ)^k by positivity)).mp h
  have log : Real.log (L:ℝ) = Real.log (Real.sqrt L) * 2 := by
    rw [Real.log_sqrt (by positivity)]; ring
  exact ⟨pow_pos (Real.log_pos one) _, by rw [log,mul_pow]; linarith⟩

/-- Only the source's lower half-estimate on its own common prime set is needed;
its complete asymptotic and declared singular series may be discarded. -/
def PaperInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∃ (m₀ : ℕ) (c₀ : ℝ), 0 < c₀ ∧
      ∀ L : ℕ,m₀ ≤ L →
        PaperThreshold (Sun28.RealPoleBounds.fixedScale n) d L
          (c₀ / (Real.log (L : ℝ))^(4*(shifts (Sun28.RealPoleBounds.fixedScale n)).card))

theorem lower_of_paper (paper : PaperInputs) : LowerInputs := by
  intro X c q n roots d dp B
  obtain ⟨m₀,c₀,pos,count⟩ := paper X c q n roots d dp
  let A := Sun28.RealPoleBounds.fixedScale n
  let k := 4*(shifts A).card
  obtain ⟨m₁,rate⟩ := eventually_atTop.mp (sqrt_dominates k)
  let K := max B (max m₀ m₁)
  refine ⟨K,c₀,le_max_left ..,pos,?_⟩
  intro m
  let L := max K m
  have kl : K ≤ L := le_max_left ..
  have lm₀ : m₀ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans kl)
  have lm₁ : m₁ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans kl)
  obtain ⟨up,le⟩ := rate L lm₁
  obtain ⟨ω,slow,low⟩ := count L lm₀
  refine ⟨L,le_refl _,ω,slow,?_⟩
  intro w grow short ready
  filter_upwards [low w grow short ready] with b hb
  apply le_trans _ ((le_trans hb) (mass_mono_base A kl))
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left pos.le up le) (by positivity)

end
end Sun28.FinitePattern
#print axioms Sun28.FinitePattern.mass_mono_base
#print axioms Sun28.FinitePattern.lower_of_paper
