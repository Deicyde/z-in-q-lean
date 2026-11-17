import ElementaryEuler

namespace Sun28.ConeEuler.Elementary
open Finset Sun28.ConeSieve Sun28.MediumSieve Sun28.SinglePrime
noncomputable section

theorem squareSum_le_two : squareSum≤2 := by
  have sm : Summable (fun n : ℕ=>1/(n:ℝ)^2):=Real.summable_one_div_nat_pow.mpr (by decide)
  have stage : ∀ n : ℕ,(∑ i∈range (n+1+1),1/(i:ℝ)^2)≤2-1/((n:ℝ)+1) := by
    intro n;induction n with
    | zero => norm_num [sum_range_succ]
    | succ n ih =>
      rw [sum_range_succ (f:=fun i : ℕ=>1/(i:ℝ)^2) (n+1+1),Nat.cast_succ]
      push_cast
      have inv : 1/((n:ℝ)+1+1)^2 ≤ 1/((n:ℝ)+1)-1/((n:ℝ)+1+1) := by
        have a : (0:ℝ)< n+1:=by positivity
        have b : (0:ℝ)< n+1+1:=by positivity
        field_simp
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      linarith only [ih,inv]
  apply sm.tsum_le_of_sum_range_le
  intro n
  rcases n with _|(_|n)
  · simp
  · norm_num [sum_range_succ]
  · exact (stage n).trans (sub_le_self _ (by positivity))

theorem numerical_loss {B k : ℕ} (lo : 2≤k) (hi : k≤13) :
    elementaryLoss B k 50 ≤ 15*(B:ℝ)+339 := by
  have l : (2:ℝ)≤k:=by exact_mod_cast lo
  have u : (k:ℝ)≤13:=by exact_mod_cast hi
  have b1:=mul_le_mul_of_nonneg_left squareSum_le_two (sub_nonneg.mpr l)
  have b2:=mul_le_mul_of_nonneg_right u (Nat.cast_nonneg (α:=ℝ) B)
  have lg:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/2)
  dsimp [elementaryLoss];nlinarith only [squareSum_le_two,b1,b2,u,lg]

/-- Numeric density constant and a fixed starting row for the error 50 from the cone counts. -/
theorem numerical_sieve (A : Fin 3→ℚ) {B k t p : ℕ} {g : ℕ→ℝ} (hb : 64≤B)
    (lo : 2≤k) (hi : k≤13) (ht : max 256 (envelope A+3)≤t)
    (approx : LocalApproximation B k 50 g) :
    let P:=auxPrimes B (smallLevel t) p
    (∀ q∈P,q.Prime ∧ q≠p ∧ q≤level t ∧ 0≤g q ∧ g q<1 ∧ 1+2*odds g q≤q) ∧
    (2*∑ q∈P,g q*Real.log q ≤ Real.log (level t)) ∧
    Real.exp (-(15*(B:ℝ)+339))*(Real.log 2/131072)^k*(growthBound A t:ℝ)^k ≤
      ∏ q∈P,(1+odds g q) := by
  have error : (50:ℝ)≤B:=by exact_mod_cast (show 50≤B by omega)
  refine ⟨?_,auxiliary_mean hb error hi approx,?_⟩
  · intro q h
    obtain ⟨prime,large,limited,ne⟩:=mem_auxPrimes.mp h
    obtain ⟨nn,_,u,v⟩:=local_size hb error hi approx prime large
    exact ⟨prime,ne,limited.trans (smallLevel_le t),nn,u,v⟩
  · have large : envelope A+3≤t:=(le_max_right ..).trans ht
    have high : 256≤t:=(le_max_left ..).trans ht
    have cut : 2 ≤ smallLevel t := by
      change 2≤2^(t/128)
      exact (Nat.one_lt_pow (by omega : t/128≠0) (by decide))
    have budget : growthBound A t≤131072*(t/128) := by unfold growthBound growth;omega
    have cap : (growthBound A t:ℝ)≤131072*((t/128:ℕ):ℝ) := by exact_mod_cast budget
    have lg:=Real.log_nonneg (by norm_num : (1:ℝ)≤2)
    have scale : (Real.log 2/131072)*(growthBound A t:ℝ)≤Real.log (smallLevel t) := by
      rw [log_smallLevel];linarith only [mul_le_mul_of_nonneg_left cap lg]
    have pos : 0≤(Real.log 2/131072)*(growthBound A t:ℝ) := by positivity
    have pow:=pow_le_pow_left₀ pos scale k
    have coeff:=Real.exp_le_exp.mpr (neg_le_neg (numerical_loss (B:=B) lo hi))
    calc _ = Real.exp (-(15*(B:ℝ)+339))*((Real.log 2/131072)*(growthBound A t:ℝ))^k := by ring
         _ ≤ Real.exp (-elementaryLoss B k 50)*(Real.log (smallLevel t))^k :=
            mul_le_mul coeff pow (pow_nonneg pos k) (Real.exp_pos _).le
         _ ≤ _ := elementary_product hb error (by norm_num) lo hi _ cut p g approx

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.squareSum_le_two
#print axioms Sun28.ConeEuler.Elementary.numerical_loss
#print axioms Sun28.ConeEuler.Elementary.numerical_sieve
