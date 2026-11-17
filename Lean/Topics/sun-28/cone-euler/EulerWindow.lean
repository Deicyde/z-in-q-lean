import EulerPoint
import ConeScale

namespace Sun28.ConeEuler
open Finset Filter Topology Sun28.ConeSieve Sun28.MediumSieve Sun28.SinglePrime
noncomputable section

def smallLevel (t : ℕ) : ℕ := 2^(t/128)

theorem smallLevel_tendsto : Tendsto smallLevel atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (128*n)] with t ht
  have h : n≤t/128 := by omega
  calc n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
       _ ≤ smallLevel t := Nat.pow_le_pow_right (by decide) h

theorem smallLevel_le (t : ℕ) : smallLevel t≤level t :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)

theorem log_smallLevel (t : ℕ) : Real.log (smallLevel t)=(t/128:ℕ)*Real.log 2 := by
  unfold smallLevel;push_cast;rw [Real.log_pow]

theorem scale_comparison (A : Fin 3→ℚ) :
    ∀ᶠ t : ℕ in atTop,
      (Real.log 2/131072)*(growthBound A t:ℝ) ≤ Real.log (smallLevel t) := by
  filter_upwards [eventually_ge_atTop (envelope A+3),eventually_ge_atTop (256:ℕ)] with t large floor
  have a : growthBound A t≤402*t := by unfold growthBound growth;omega
  have b : t≤256*(t/128) := by omega
  have m : growthBound A t≤131072*(t/128) := by omega
  have m' : (growthBound A t:ℝ)≤131072*((t/128:ℕ):ℝ) := by exact_mod_cast m
  have lg : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have mul:=mul_le_mul_of_nonneg_left m' lg
  rw [log_smallLevel];linarith only [mul]

theorem auxiliary_mean {B k t p : ℕ} {C : ℝ} {g : ℕ→ℝ} (hb : 64≤B)
    (error : C≤B) (hi : k≤13) (approx : LocalApproximation B k C g) :
    2*(∑ q∈auxPrimes B (smallLevel t) p, g q*Real.log q)≤Real.log (level t) := by
  let P:=auxPrimes B (smallLevel t) p
  have sum : (∑ q∈P,g q*Real.log q) ≤ 16* ∑ q∈P,Real.log (q:ℝ)/q := by
    rw [mul_sum]
    apply sum_le_sum;intro q h
    obtain ⟨prime,large,_,_⟩:=mem_auxPrimes.mp h
    have nn : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast prime.one_lt.le)
    have bd:= (local_size hb error hi approx prime large).2.1
    exact (mul_le_mul_of_nonneg_right bd nn).trans_eq (by ring)
  have cap:=Sun28.FinitePattern.factorial_prime_sum (L:=smallLevel t) (by unfold smallLevel;positivity) P
    (fun q h=>⟨(mem_auxPrimes.mp h).1,(mem_auxPrimes.mp h).2.2.1⟩)
  have h : 64*(t/128)≤t := by omega
  have h' : (64:ℝ)*((t/128:ℕ):ℝ)≤t := by exact_mod_cast h
  have lim:=mul_le_mul_of_nonneg_right h' (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  rw [log_smallLevel] at cap
  change 2*(∑ q∈P,g q*Real.log q)≤Real.log ((2^t:ℕ):ℝ)
  push_cast
  rw [Real.log_pow]
  linarith only [sum,cap,lim]

end
end Sun28.ConeEuler
#print axioms Sun28.ConeEuler.smallLevel_tendsto
#print axioms Sun28.ConeEuler.smallLevel_le
#print axioms Sun28.ConeEuler.log_smallLevel
#print axioms Sun28.ConeEuler.scale_comparison
#print axioms Sun28.ConeEuler.auxiliary_mean
