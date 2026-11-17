import ElementaryLocal
import Mathlib.Data.Nat.Prime.Factorial

namespace Sun28.ConeEuler.Elementary
open Finset ArithmeticFunction
noncomputable section

theorem factorial_primes (n : ℕ) : n.factorial.primeFactors=primesUpTo n := by
  ext p;rw [Nat.mem_primeFactors,mem_primesUpTo]
  constructor
  · rintro ⟨hp,div,_⟩;exact ⟨hp,hp.dvd_factorial.mp div⟩
  · rintro ⟨hp,le⟩;exact ⟨hp,hp.dvd_factorial.mpr le,Nat.factorial_ne_zero _⟩

/-- Finite Euler majorant by embedding [1,n] into the divisors of n!. -/
theorem finite_euler (f : ArithmeticFunction ℝ) (hm : f.IsMultiplicative)
    (non : ∀ m,0≤f m) (cap : ∀ p:ℕ,p.Prime → ∀ e:ℕ, f (p^e)≤e+1) (n : ℕ) :
    (∑ m∈Icc 1 n,f m/m) ≤ Real.exp ((∑ p∈primesUpTo n,f p/p) + 8*squareSum) := by
  let w:=weight f
  let F:ArithmeticFunction ℝ:=(zeta:ArithmeticFunction ℝ)*w
  have mult : F.IsMultiplicative:=isMultiplicative_zeta.natCast.mul (weight_mult hm)
  have wn (m : ℕ) : 0≤w m:=div_nonneg (non m) (Nat.cast_nonneg _)
  have sub : Icc 1 n⊆n.factorial.divisors := by
    intro m h
    obtain ⟨lo,hi⟩:=mem_Icc.mp h
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial lo hi,Nat.factorial_ne_zero n⟩
  have embed : (∑ m∈Icc 1 n,w m)≤F n.factorial := by
    dsimp only [F];rw [coe_zeta_mul_apply]
    exact sum_le_sum_of_subset_of_nonneg sub (fun m _ _=>wn m)
  have fn (p e : ℕ) : 0≤F (p^e) := by
    dsimp only [F];rw [coe_zeta_mul_apply];exact sum_nonneg fun m _=>wn m
  have each (p : ℕ) (hp : p.Prime) (e : ℕ) :
      F (p^e) ≤ Real.exp (f p/p+8/(p:ℝ)^2) := by
    have b (i : ℕ) : w (p^i)≤((i:ℝ)+1)/(p:ℝ)^i := by
      change f (p^i)/((p^i:ℕ):ℝ)≤_
      rw [Nat.cast_pow];exact div_le_div_of_nonneg_right (cap p hp i) (by positivity)
    have maj:=local_majorant (fun j=>w (p^j)) hp (by simpa using (weight_mult hm).1) (fun i=>wn _) b e
    change ((zeta:ArithmeticFunction ℝ)*w) (p^e)≤_
    rw [coe_zeta_mul_apply,Nat.sum_divisors_prime_pow hp]
    simp only [pow_one] at maj
    dsimp only [w,weight,coe_mk] at maj ⊢
    linarith only [maj,Real.add_one_le_exp (f p/p+8/(p:ℝ)^2)]
  have fact:=mult.multiplicative_factorization F (Nat.factorial_ne_zero n)
  change F n.factorial= ∏ p∈n.factorial.primeFactors,F (p^n.factorial.factorization p) at fact
  rw [factorial_primes] at fact
  rw [fact] at embed
  apply embed.trans
  calc _ ≤ ∏ p∈primesUpTo n,Real.exp (f p/p+8/(p:ℝ)^2) := prod_le_prod₀
           (fun p _=>fn p _) (fun p hp=>each p (mem_primesUpTo.mp hp).1 _)
       _ = Real.exp (∑ p∈primesUpTo n,(f p/p+8/(p:ℝ)^2)) := (Real.exp_sum _ _).symm
       _ ≤ _ := by rw [sum_add_distrib];exact Real.exp_le_exp.mpr (add_le_add_right (error_budget _ (by norm_num : (0:ℝ)≤8)) _)

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.factorial_primes
#print axioms Sun28.ConeEuler.Elementary.finite_euler
