import DivisorSums
import OriginalRows
import SignedSupport

/-! The intrinsic radical of the two signed sextic coefficients has the actual exceptional height cutoff. -/
namespace ZInQBlueprint.TwistCount
open Finset Height Sun28.FiveDescent Sun28.FiveMarkUnits Sun28.HeightFibres Sun28.Ordinary
open ZInQBlueprint.OriginalHeightCount
open scoped Classical
noncomputable section
attribute [local irreducible] glazerConstant24 oldCutoff cutoffProduct D E exceptions
set_option maxHeartbeats 120000
set_option maxRecDepth 12000

def supportSet (x : ℚ) := parameterPrimes (D x.num x.den) (E x.num x.den)
def label (x : ℚ) := primeProduct (supportSet x)

theorem label_factors (x : ℚ) : (label x).primeFactors=supportSet x := by
  change (∏ p ∈ supportSet x,p).primeFactors = supportSet x
  apply Nat.primeFactors_prod
  intro p hp
  rcases mem_union.mp hp with h|h <;> exact Nat.prime_of_mem_primeFactors h

theorem label_small {B K : ℕ} {x : ℚ} (hx : x∈exceptions B)
    (lim : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) : label x∈Icc 1 K := by
  obtain ⟨box,off,fail⟩:=(mem_exceptions x B).mp hx
  have cop : Int.gcd x.num (x.den:ℤ)=1 := by simpa [Int.gcd] using x.reduced.gcd_eq_one
  have radical := fixed_cost (D x.num x.den) (E x.num x.den)
  rw [←support_exact cop off] at radical
  change label x ≤ heightRadical x.num x.den at radical
  have pos : 0 < label x := by
    change 0 < ∏ p ∈ parameterPrimes (D x.num x.den) (E x.num x.den),p
    apply prod_pos;intro p hp
    rcases mem_union.mp hp with h|h <;> exact (Nat.prime_of_mem_primeFactors h).pos
  refine mem_Icc.mpr ⟨pos,?_⟩
  have lift : (heightRadical x.num x.den:ℝ)^24 ≤ 2^810*(heightRadical x.num x.den:ℝ)^24 := by
    have c : (1:ℝ) ≤ 2^810 := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right c
      (show 0≤(heightRadical x.num x.den:ℝ)^24 by positivity)
  have power : (label x:ℝ)^24≤(heightRadical x.num x.den:ℝ)^24 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast radical) _
  have cap := (power.trans (lift.trans (original_margin x.num x.den))).trans_lt fail
  rw [Rat.logHeight₁_eq_log_max] at cap
  have mp : 0 < max x.num.natAbs x.den := x.den_pos.trans_le (le_max_right ..)
  have up := Real.log_le_log (by exact_mod_cast mp : (0:ℝ)<(max x.num.natAbs x.den:ℕ))
    (by exact_mod_cast box : ((max x.num.natAbs x.den:ℕ):ℝ)≤B)
  by_contra! large
  have g : ((K+1:ℕ):ℝ)≤(label x:ℝ) := by exact_mod_cast large
  exact (not_le_of_gt ((cap.trans_le up).trans_le lim)) (pow_le_pow_left₀ (by positivity) g 24)

/-- Finite form of the external point count; it does not assert any bound for a height. -/
def SupportCount (a : ℕ) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (X : Finset ℚ), (∀ x∈X,offMarks x ∧ label x=m) →
    (X.card:ℝ)≤C*(a:ℝ)^omega m

theorem count_by_support (n B K : ℕ) {C : ℝ} (c : 0≤C) (fibres : SupportCount (n+1) C)
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    ((exceptions B).card:ℝ)≤C*(K:ℝ)*(1+Real.log (K:ℝ))^n := by
  let S:=exceptions B
  have maps : (S:Set ℚ).MapsTo label (Icc 1 K : Finset ℕ) :=
    fun x hx=>label_small hx threshold
  have eq := card_eq_sum_card_fiberwise (f:=label) (s:=S) (t:=Icc 1 K) maps
  have real : (S.card:ℝ) = ∑ m ∈ Icc 1 K, ((S.filter fun x=>label x=m).card:ℝ) := by exact_mod_cast eq
  calc
    ((exceptions B).card:ℝ) = _ := real
    _ ≤ ∑ m ∈ Icc 1 K, C*((n+1:ℕ):ℝ)^omega m := by
      apply sum_le_sum
      intro m _
      apply fibres
      intro x hx
      obtain ⟨ins,lab⟩:=mem_filter.mp hx
      exact ⟨((mem_exceptions x B).mp ins).2.1,lab⟩
    _ = C*∑ m ∈ Icc 1 K, (((n+1)^omega m:ℕ):ℝ) := by simp only [Nat.cast_pow,mul_sum]
    _ ≤ C*((K:ℝ)*(1+Real.log (K:ℝ))^n) := mul_le_mul_of_nonneg_left (sum_omega n K) c
    _ = _ := by ring

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.label_factors
#print axioms ZInQBlueprint.TwistCount.label_small
#print axioms ZInQBlueprint.TwistCount.count_by_support
