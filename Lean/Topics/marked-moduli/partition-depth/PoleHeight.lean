import NormalizedFibre
import LocalContactOrders
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The total contribution of pole orders and its dependence on the parameter height. -/
namespace ZInQBlueprint.BranchDepth
open ResidualFactors
noncomputable section

/-- Positive value of the integral pole form in lowest terms. -/
def poleNorm (u : ℚ) : ℕ := (poleForm u.num (u.den:ℤ)).natAbs

private theorem bounds (A B : ℝ) (hB : 0 < B) :
    0 < poleForm A B ∧ poleForm A B ≤ 3907*(max |A| B)^2 := by
  let H := max |A| B
  have hH : 0 ≤ H := (abs_nonneg A).trans (le_max_left ..)
  have hA : |A| ≤ H := le_max_left ..
  have hBH : B ≤ H := le_max_right ..
  have hAB : A*B ≤ H*H := mul_le_mul (le_abs_self A |>.trans hA) hBH hB.le hH
  have ha : A^2 ≤ H^2 := by
    rw [← sq_abs A]
    exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hb : B^2 ≤ H^2 := pow_le_pow_left₀ hB.le hBH 2
  unfold poleForm
  constructor
  · nlinarith [sq_nonneg (7*A+150*B),sq_pos_of_pos hB]
  · change _ ≤ 3907*H^2
    nlinarith

theorem pole_form_height (u : ℚ) :
    Real.log (poleNorm u) ≤ Real.log 3907+2*ZInQ.ratHeight u := by
  let A : ℝ := u.num
  let B : ℝ := u.den
  have hB : 0 < B := by dsimp [B]; exact_mod_cast u.den_pos
  have h := bounds A B hB
  have hc : (((poleForm u.num (u.den:ℤ)).natAbs : ℕ):ℝ) = poleForm A B := by
    have hZ : 0 < poleForm u.num (u.den:ℤ) := by
      dsimp [poleForm,A,B] at h ⊢
      exact_mod_cast h.1
    rw [Nat.cast_natAbs,abs_of_pos hZ]
    simp [A,B,poleForm]
  have hH : 0 < max |A| B := hB.trans_le (le_max_right ..)
  calc
    _ = Real.log (poleForm A B) := congrArg Real.log hc
    _ ≤ Real.log (3907*(max |A| B)^2) := Real.log_le_log h.1 h.2
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hH.ne'),Real.log_pow]; rfl

/-- On the actual pole charts, the local order is the exponent in the integer pole norm. -/
theorem pole_exponent (p : ℕ) [hprime : Fact p.Prime] (u : ℚ) (g : ℕ)
    (hg : IsDiscreteValuationRing.addVal ℤ_[p] (RationalClusters.G p u)=(g:ℕ∞)) :
    (poleNorm u).factorization p = g := by
  let z : ℤ := poleForm u.num (u.den:ℤ)
  have he : (z:ℤ_[p]) = RationalClusters.G p u := by
    simp [z,RationalClusters.G,poleForm]
  have h := ContactInvariant.rational_order_of_addVal (p:=p) (z:=z) g (he ▸ hg)
  rw [padicValRat.of_int,padicValInt,← Nat.factorization_def _ hprime.out] at h
  exact_mod_cast h

/-- The sum over any chosen subset of pole prime divisors is bounded by the parameter height.
The coefficient two is the logarithm of the local maximum with v(p)=1. -/
theorem pole_sum_height (u : ℚ) (s : Finset ℕ) (hs : s ⊆ (poleNorm u).primeFactors) :
    (∑ p ∈ s, 2*((poleNorm u).factorization p:ℝ)*Real.log p) ≤
       2*Real.log 3907+4*ZInQ.ratHeight u := by
  let n := poleNorm u
  have h : ∑ p ∈ s, (n.factorization p:ℝ)*Real.log p ≤ Real.log n := by
    rw [Real.log_nat_eq_sum_factorization]
    unfold Finsupp.sum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact hs
    · intro p hp _
      apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast (Nat.prime_of_mem_primeFactors (show p∈n.primeFactors from hp)).one_le
  calc
    _ = 2*(∑ p ∈ s, (n.factorization p:ℝ)*Real.log p) := by simp only [Finset.mul_sum,mul_assoc,n]
    _ ≤ 2*Real.log n := by linarith
    _ ≤ _ := by linarith [pole_form_height u]

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.pole_exponent
#print axioms ZInQBlueprint.BranchDepth.pole_form_height
#print axioms ZInQBlueprint.BranchDepth.pole_sum_height
