import EulerPoint

namespace Sun28.ConeEuler
open Finset Filter Topology Sun28.ConeSieve
noncomputable section

theorem logarithmic_lower {B k n p : ℕ} {C : ℝ} {g : ℕ→ℝ} (hc : 0≤C)
    (approx : LocalApproximation B k C g) (hb : 64≤B) (error : C≤B) (dim : k≤13) :
    (∑ q∈auxPrimes B n p,dimension k q/q) - C*squareSum ≤
      Real.log (∏ q∈auxPrimes B n p,(1+odds g q)) := by
  let P:=auxPrimes B n p
  have regular (q : ℕ) (hq : q∈P) := local_size hb error dim approx
    (mem_auxPrimes.mp hq).1 (mem_auxPrimes.mp hq).2.1
  have pos (q : ℕ) (hq : q∈P) : 0<1+odds g q := by
    have posod : 0≤odds g q:=div_nonneg (regular q hq).1 (sub_nonneg.mpr (regular q hq).2.2.1.le)
    linarith
  change (∑ q∈P,dimension k q/q)-C*squareSum≤Real.log (∏ q∈P,(1+odds g q))
  rw [Real.log_prod (fun q h=> (pos q h).ne')]
  have sum := Finset.sum_le_sum (s:=P) (f:=fun q=>dimension k q/q-C/(q:ℝ)^2)
    (g:=fun q=>Real.log (1+odds g q)) (fun q h=>by
      obtain ⟨prime,large,_,_⟩:=mem_auxPrimes.mp h
      exact le_trans (by linarith only [(abs_le.mp (approx q prime large).2).1])
        (local_log (regular q h).2.2.1))
  rw [sum_sub_distrib] at sum
  linarith only [sum,error_budget P hc]

theorem product_lower {B k : ℕ} {C : ℝ} (mertens : PublishedMertensFour)
    (hb : 64≤B) (error : C≤B) (hc : 0≤C) (lo : 2≤k) (hi : k≤13) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) (g : ℕ→ℝ), LocalApproximation B k C g →
      c*(Real.log n)^k ≤ ∏ q∈auxPrimes B n p,(1+odds g q) := by
  obtain ⟨D₁,h₁⟩:=mertens_trimmed mertens B 1 (Or.inl rfl)
  obtain ⟨D₃,h₃⟩:=mertens_trimmed mertens B 3 (Or.inr rfl)
  let D:=((k:ℝ)+2)*D₁+((k:ℝ)-2)*D₃+C*squareSum
  refine ⟨Real.exp (-D),Real.exp_pos _,?_⟩
  filter_upwards [h₁,h₃,eventually_ge_atTop (2:ℕ)] with n h₁ h₃ hn
  intro p g approx
  let P:=auxPrimes B n p
  have lk : 0≤(k:ℝ)-2 := sub_nonneg.mpr (by exact_mod_cast lo)
  have one:=mul_le_mul_of_nonneg_left (h₁ p) (show 0≤(k:ℝ)+2 by positivity)
  have three:=mul_le_mul_of_nonneg_left (h₃ p) lk
  have result:=logarithmic_lower (p:=p) (n:=n) hc approx hb error hi
  rw [sum_dimensions (by omega : 2≤B)] at result
  have logle : -D+(k:ℝ)*Real.log (Real.log n) ≤ Real.log (∏ q∈P,(1+odds g q)) := by
    dsimp [D,P];linarith only [one,three,result]
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

end
end Sun28.ConeEuler
#print axioms Sun28.ConeEuler.logarithmic_lower
#print axioms Sun28.ConeEuler.product_lower
