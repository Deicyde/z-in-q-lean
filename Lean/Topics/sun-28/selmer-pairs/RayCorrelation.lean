import RayRows
import PaperPattern

namespace Sun28.RayDensity
open Finset Filter Topology Sun28.FinitePattern Sun28.ContactFactors Sun28.ContactSieve

def cutoffPrimes (L : ℕ) := (range (L+1)).filter fun p => p.Prime ∧ 11 ≤ p

/-- The explicit finite-fibre proportion dominates a fixed multiple of
(log L)^(-4k). Every position can prescribe its own rational norms. -/
theorem log_fraction {L k : ℕ} (hL : 2≤L) (lg : 1≤Real.log (L:ℝ))
    (t : Fin k → NormRow (cutoffPrimes L)) :
    (Real.exp (-48)/(64*10^4))^k/(Real.log (L:ℝ))^(4*k) ≤
      ∏ j : Fin k, fraction (cutoffPrimes L) (t j) := by
  have pos : 0 < Real.log (L:ℝ) := lt_of_lt_of_le zero_lt_one lg
  have primes (p : ℕ) (h : p∈cutoffPrimes L) : p.Prime ∧ 11≤p ∧ p≤L := by
    obtain ⟨hp,pr,low⟩ := mem_filter.mp h
    exact ⟨pr,low,Nat.le_of_lt_succ (mem_range.mp hp)⟩
  apply le_trans _ (k_row_fibres hL primes t)
  rw [pow_mul, ← div_pow]
  apply pow_le_pow_left₀ (by positivity)
  have one : 0 < 2*(1+4*Real.log L) := by positivity
  have den := pow_le_pow_left₀ one.le (show 2*(1+4*Real.log L) ≤ 10*Real.log L by linarith) 4
  rw [←div_mul_eq_div_div, mul_assoc, ←mul_pow]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    (mul_le_mul_of_nonneg_left den (by norm_num))

/-- Transfer still required from actual simultaneous prime values to a
product of finite fibre proportions, for the fixed base congruences. -/
def CorrelationInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∃ (m : ℕ) (α : ℝ), 0<α ∧ ∀ L≥m,
      let A := Sun28.RealPoleBounds.fixedScale n
      ∃ t : Fin (shifts A).card → NormRow (cutoffPrimes L),
        PaperThreshold A d L (α * ∏ j, fraction (cutoffPrimes L) (t j))

theorem paper_of_correlation (H : CorrelationInputs) : PaperInputs := by
  intro X c q n roots d dp
  obtain ⟨m,α,ap,low⟩ := H X c q n roots d dp
  let A := Sun28.RealPoleBounds.fixedScale n
  let k := (shifts A).card
  let c0 : ℝ := (Real.exp (-48)/(64*10^4))^k
  have pos : 0<c0 := by dsimp [c0]; positivity
  obtain ⟨m₁,ready⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  refine ⟨max m (max 2 m₁), α*c0, mul_pos ap pos, ?_⟩
  intro L high
  obtain ⟨t,ω,slow,count⟩ := low L ((le_max_left ..).trans high)
  have hL : 2≤L := (le_max_left ..).trans ((le_max_right ..).trans high)
  have hm : m₁≤L := (le_max_right ..).trans ((le_max_right ..).trans high)
  have eq := log_fraction hL (ready L hm) t
  refine ⟨ω,slow,fun w grow short good => ?_⟩
  filter_upwards [count w grow short good] with N bound
  apply le_trans _ bound
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left eq ap.le

end Sun28.RayDensity
#print axioms Sun28.RayDensity.log_fraction
#print axioms Sun28.RayDensity.paper_of_correlation
