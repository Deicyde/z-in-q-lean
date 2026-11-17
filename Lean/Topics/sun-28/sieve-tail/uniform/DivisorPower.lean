import ActualTail
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Sun28.SieveTail.Uniform
noncomputable section
set_option exponentiation.threshold 512

/-- An elementary constant for the power form of the divisor bound. -/
def divisorConstant (k : ℕ) : ℕ := (2^(k*k))^(2^k)

private theorem successor (a : ℕ) : a+1 ≤ 2^a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ];omega

theorem small_prime_cost (a k : ℕ) (kp : 0 < k) :
    (a+1)^k ≤ 2^(k*k)*2^a := by
  have div := Nat.div_add_mod a k
  have modlt := Nat.mod_lt a kp
  have one : a+1 ≤ k*(a/k+1) := by
    rw [Nat.mul_add];omega
  have upper : k*(a/k+1) ≤ 2^k*2^(a/k) :=
    Nat.mul_le_mul (Nat.le_of_succ_le (successor k)) (successor (a/k))
  calc (a+1)^k ≤ (2^k*2^(a/k))^k := Nat.pow_le_pow_left (one.trans upper) _
       _ = 2^(k*k)*2^((a/k)*k) := by simp only [mul_pow,pow_mul]
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self a k))

theorem divisor_power {n : ℕ} (k : ℕ) (kp : 0 < k) (nn : n≠0) :
    n.divisors.card^k ≤ divisorConstant k*n := by
  classical
  let C := 2^(k*k)
  let F := n.primeFactors
  have cpos : 1≤C := by exact Nat.one_le_two_pow
  have per (p : ℕ) (hp : p∈F) :
      (n.factorization p+1)^k ≤ (if p<2^k then C else 1)*p^(n.factorization p) := by
    have prime:= Nat.prime_of_mem_primeFactors hp
    split_ifs with small
    · exact (small_prime_cost _ _ kp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left prime.two_le _))
    · rw [one_mul]
      calc _ ≤ (2^(n.factorization p))^k := Nat.pow_le_pow_left (successor _) _
           _ = (2^k)^(n.factorization p) := by simp only [←pow_mul,mul_comm]
           _ ≤ _ := Nat.pow_le_pow_left (Nat.le_of_not_gt small) _
  have size : (F.filter (fun p => p<2^k)).card≤2^k := by
    apply (Finset.card_le_card (t:=Finset.range (2^k)) ?_).trans_eq (Finset.card_range _)
    exact fun _ hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have units : (∏ p∈F,if p<2^k then C else 1)≤divisorConstant k := by
    rw [←Finset.prod_filter]
    simpa only [Finset.prod_const,divisorConstant,C] using Nat.pow_le_pow_right cpos size
  rw [Nat.card_divisors nn,←Finset.prod_pow]
  calc _ ≤ ∏ p∈F,((if p<2^k then C else 1)*p^(n.factorization p)) :=
           Finset.prod_le_prod per
       _ = (∏ p∈F,if p<2^k then C else 1)*(∏ p∈F,p^(n.factorization p)) := Finset.prod_mul_distrib
       _ ≤ divisorConstant k*n := by
          apply Nat.mul_le_mul units
          exact (Nat.prod_primeFactors_pow_factorization nn).symm.le

/-- Uniform dyadic weight for Sun’s large-prime cutoff. This is an
integer inequality with a fixed coefficient depending only on the two shifts. -/
theorem tau_row (κ : ℤ) (t V : ℕ) (small : V≤2^(200*t)) :
    (κ*(V:ℤ)^2).natAbs.divisors.card ≤ (divisorConstant 400*κ.natAbs+1)*2^t := by
  let n := (κ*(V:ℤ)^2).natAbs
  change n.divisors.card≤_
  by_cases zero : n=0
  · simp [zero]
  let C := divisorConstant 400*κ.natAbs
  have vcap : V^2≤(2^t)^400 := by
    apply (Nat.pow_le_pow_left small 2).trans_eq
    rw [←Nat.pow_mul,←Nat.pow_mul]
    congr 1
    omega
  have ncap : n≤κ.natAbs*(2^t)^400 := by
    simpa only [n,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using Nat.mul_le_mul_left κ.natAbs vcap
  have lim := (divisor_power 400 (by decide) zero).trans (Nat.mul_le_mul_left (divisorConstant 400) ncap)
  have keep := Nat.pow_le_pow_right (show 0<C+1 by omega) (show 1≤400 by decide)
  rw [pow_one] at keep
  have cn : C≤(C+1)^400 := (Nat.le_succ C).trans keep
  have out : n.divisors.card^400≤((C+1)*2^t)^400 := by
    rw [mul_pow]
    apply lim.trans
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ cn
  by_contra! hn
  exact (not_lt_of_ge out) (Nat.pow_lt_pow_left hn (by decide : 400≠0))

end
end Sun28.SieveTail.Uniform
#print axioms Sun28.SieveTail.Uniform.small_prime_cost
#print axioms Sun28.SieveTail.Uniform.divisor_power
#print axioms Sun28.SieveTail.Uniform.tau_row
