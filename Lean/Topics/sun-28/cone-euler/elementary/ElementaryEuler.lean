import ElementaryClasses
import EulerLower
import EulerWindow

namespace Sun28.ConeEuler.Elementary
open Finset Filter Topology Sun28.ConeSieve Sun28.MediumSieve
noncomputable section

def elementaryLoss (B k : ℕ) (C : ℝ) : ℝ :=
  ((k:ℝ)-2)*((B:ℝ)+2+8*squareSum)+2*(2*((B:ℝ)+2)+8*squareSum+Real.log (3/2))+C*squareSum

theorem elementary_product {B k : ℕ} {C : ℝ} (hb : 64≤B) (error : C≤B) (hc : 0≤C)
    (lo : 2≤k) (hi : k≤13) :
    ∀ (n : ℕ), 2≤n → ∀ (p : ℕ) (g : ℕ→ℝ), LocalApproximation B k C g →
      Real.exp (-elementaryLoss B k C)*(Real.log n)^k ≤ ∏ q∈auxPrimes B n p,(1+odds g q) := by
  intro n hn p g approx
  let P:=auxPrimes B n p
  have main:=first_order_lower (n:=n) (p:=p) (by omega : 2≤B) lo hn
  have lower:=logarithmic_lower (p:=p) (n:=n) hc approx hb error hi
  have logle : -elementaryLoss B k C+(k:ℝ)*Real.log (Real.log n) ≤ Real.log (∏ q∈P,(1+odds g q)) := by
    dsimp [elementaryLoss,P];linarith only [main,lower]
  have logpos : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have full : 0<∏ q∈P,(1+odds g q) := by
    apply prod_pos
    intro q h
    obtain ⟨prime,large,_,_⟩:=mem_auxPrimes.mp h
    obtain ⟨zero,_,small,_⟩:=local_size hb error hi approx prime large
    have nn : 0≤odds g q:=div_nonneg zero (sub_nonneg.mpr small.le)
    linarith
  have ex:=Real.exp_le_exp.mpr logle
  rwa [Real.exp_add,Real.exp_nat_mul,Real.exp_log logpos,Real.exp_log full] at ex

/-- The same constant and starting index apply to every excluded prime and
every density with the stated error, even if both depend on the window. -/
theorem sieve_primes (A : Fin 3→ℚ) {B k : ℕ} {C : ℝ}
    (hb : 64≤B) (error : C≤B) (hc : 0≤C) (lo : 2≤k) (hi : k≤13) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ t : ℕ in atTop, ∀ (p : ℕ) (g : ℕ→ℝ), LocalApproximation B k C g →
      let P:=auxPrimes B (smallLevel t) p
      (∀ q∈P,q.Prime ∧ q≠p ∧ q≤level t ∧ 0≤g q ∧ g q<1 ∧ 1+2*odds g q≤q) ∧
      (2*∑ q∈P,g q*Real.log q≤Real.log (level t)) ∧
      c*(growthBound A t:ℝ)^k ≤ ∏ q∈P,(1+odds g q) := by
  let a:=Real.exp (-elementaryLoss B k C)
  have ap : 0<a := Real.exp_pos _
  let b : ℝ:=Real.log 2/131072
  have bp : 0<b := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨a*b^k,mul_pos ap (pow_pos bp _),?_⟩
  filter_upwards [smallLevel_tendsto.eventually (eventually_ge_atTop (2:ℕ)),scale_comparison A] with t large scale
  intro p g approx
  refine ⟨?_,auxiliary_mean hb error hi approx,?_⟩
  · intro q h
    obtain ⟨prime,large,limited,ne⟩:=mem_auxPrimes.mp h
    obtain ⟨nn,_,u,v⟩:=local_size hb error hi approx prime large
    exact ⟨prime,ne,limited.trans (smallLevel_le t),nn,u,v⟩
  · have h:=pow_le_pow_left₀ (mul_nonneg bp.le (Nat.cast_nonneg (growthBound A t))) scale k
    calc a*b^k*(growthBound A t:ℝ)^k = a*(b*(growthBound A t:ℝ))^k := by ring
         _ ≤ a*(Real.log (smallLevel t))^k := mul_le_mul_of_nonneg_left h ap.le
         _ ≤ _ := elementary_product hb error hc lo hi _ large p g approx

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.elementary_product
#print axioms Sun28.ConeEuler.Elementary.sieve_primes
