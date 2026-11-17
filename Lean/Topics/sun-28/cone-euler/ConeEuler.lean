import EulerLower
import EulerWindow

namespace Sun28.ConeEuler
open Finset Filter Topology Sun28.ConeSieve Sun28.MediumSieve
noncomputable section

/-- The same constant and starting index apply to every excluded prime and
every density with the stated error, even if both depend on the window. -/
theorem sieve_primes (mertens : PublishedMertensFour) (A : Fin 3→ℚ) {B k : ℕ} {C : ℝ}
    (hb : 64≤B) (error : C≤B) (hc : 0≤C) (lo : 2≤k) (hi : k≤13) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ t : ℕ in atTop, ∀ (p : ℕ) (g : ℕ→ℝ), LocalApproximation B k C g →
      let P:=auxPrimes B (smallLevel t) p
      (∀ q∈P,q.Prime ∧ q≠p ∧ q≤level t ∧ 0≤g q ∧ g q<1 ∧ 1+2*odds g q≤q) ∧
      (2*∑ q∈P,g q*Real.log q≤Real.log (level t)) ∧
      c*(growthBound A t:ℝ)^k ≤ ∏ q∈P,(1+odds g q) := by
  obtain ⟨a,ap,prod⟩:=product_lower mertens hb error hc lo hi
  let b : ℝ:=Real.log 2/131072
  have bp : 0<b := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨a*b^k,mul_pos ap (pow_pos bp _),?_⟩
  filter_upwards [smallLevel_tendsto.eventually prod,scale_comparison A] with t lower scale
  intro p g approx
  refine ⟨?_,auxiliary_mean hb error hi approx,?_⟩
  · intro q h
    obtain ⟨prime,large,limited,ne⟩:=mem_auxPrimes.mp h
    obtain ⟨nn,_,u,v⟩:=local_size hb error hi approx prime large
    exact ⟨prime,ne,limited.trans (smallLevel_le t),nn,u,v⟩
  · have h:=pow_le_pow_left₀ (mul_nonneg bp.le (Nat.cast_nonneg (growthBound A t))) scale k
    calc a*b^k*(growthBound A t:ℝ)^k = a*(b*(growthBound A t:ℝ))^k := by ring
         _ ≤ a*(Real.log (smallLevel t))^k := mul_le_mul_of_nonneg_left h ap.le
         _ ≤ _ := lower p g approx

end
end Sun28.ConeEuler
#print axioms Sun28.ConeEuler.sieve_primes
