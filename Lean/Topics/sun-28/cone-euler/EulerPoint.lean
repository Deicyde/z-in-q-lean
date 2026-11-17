import PrimeClasses
import ConeExpansion

namespace Sun28.ConeEuler
open Finset Filter Topology Sun28.ConeSieve
noncomputable section

def dimension (k q : ℕ) : ℝ := if q%4=1 then (k:ℝ)+2 else (k:ℝ)-2

def LocalApproximation (B k : ℕ) (C : ℝ) (g : ℕ→ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → B<q →
    0≤g q ∧ |g q - dimension k q / q| ≤ C / (q:ℝ)^2

theorem local_size {B k q : ℕ} {C : ℝ} {g : ℕ→ℝ} (high : 64≤B)
    (error : C≤B) (dim : k≤13) (approx : LocalApproximation B k C g)
    (prime : q.Prime) (large : B<q) :
    0≤g q ∧ g q≤16/(q:ℝ) ∧ g q<1 ∧ 1+2*odds g q≤q := by
  obtain ⟨non,close⟩:=approx q prime large
  have qp : (0:ℝ)<q := by exact_mod_cast prime.pos
  have ql : (64:ℝ)<q := by exact_mod_cast high.trans_lt large
  have cq : C≤q := error.trans (by exact_mod_cast large.le)
  have small : C/(q:ℝ)^2 ≤ 1/q := by
    apply (div_le_div_iff₀ (by positivity) qp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right cq qp.le]
  have lim : dimension k q ≤ 15 := by
    have hk : (k:ℝ)≤13 := by exact_mod_cast dim
    unfold dimension;split_ifs <;> linarith
  have app:= (abs_le.mp close).2
  have size : g q≤16/(q:ℝ) := by
    have a:=div_le_div_of_nonneg_right lim qp.le
    linarith only [app,small,a,show 15/(q:ℝ)+1/q=16/q by ring]
  have half : g q≤1/2 := size.trans ((div_le_iff₀ qp).mpr (by linarith))
  have one : g q<1 := by linarith
  have od : odds g q≤1 := (div_le_one (sub_pos.mpr one)).mpr (by linarith)
  refine ⟨non,size,one,?_⟩
  linarith

theorem sum_dimensions {B k n p : ℕ} (hb : 2≤B) :
    (∑ q∈auxPrimes B n p,dimension k q/q) =
    ((k:ℝ)+2)*classSum 1 (auxPrimes B n p) + ((k:ℝ)-2)*classSum 3 (auxPrimes B n p) := by
  unfold classSum
  rw [mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro q h
  obtain ⟨prime,large,_,_⟩:=mem_auxPrimes.mp h
  have odd := prime.eq_two_or_odd.resolve_left (by omega)
  by_cases split : q%4=1
  · simp [dimension,classWeight,split,div_eq_mul_inv]
  · have inert : q%4=3 := by omega
    simp [dimension,classWeight,inert,div_eq_mul_inv]

def squareSum : ℝ := ∑' n : ℕ, 1/(n:ℝ)^2

theorem error_budget (P : Finset ℕ) {C : ℝ} (hc : 0≤C) :
    (∑ q∈P,C/(q:ℝ)^2)≤C*squareSum := by
  have sm : Summable (fun n : ℕ => 1/(n:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by decide)
  have bound:=sm.sum_le_tsum P (fun _ _=>by positivity)
  calc _ = C*(∑ q∈P,1/(q:ℝ)^2) := by rw [mul_sum];apply sum_congr rfl;intro q _;ring
       _ ≤ _ := mul_le_mul_of_nonneg_left bound hc

theorem local_log {x : ℝ} (hx : x<1) :
    x≤Real.log (1+x/(1-x)) := by
  have h := sub_pos.mpr hx
  have e : 1+x/(1-x)=(1-x)⁻¹ := by field_simp;ring
  rw [e,Real.log_inv]
  linarith only [Real.log_le_sub_one_of_pos h]

end
end Sun28.ConeEuler
#print axioms Sun28.ConeEuler.local_size
#print axioms Sun28.ConeEuler.sum_dimensions
#print axioms Sun28.ConeEuler.error_budget
#print axioms Sun28.ConeEuler.local_log
