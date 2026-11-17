import PrimeObstruction
import Mathlib.NumberTheory.SumTwoSquares

namespace Sun28.TwistPrimes

private theorem not_sum_three : ∀ x y : ZMod 4, x^2+y^2≠3 := by decide

/-- Each positive integer congruent to 3 modulo 4 has a prime divisor
congruent to 3 modulo 4 to odd order. -/
private theorem odd_order_prime {m : ℕ} (hm : m%4=3) :
    ∃ p : ℕ, p.Prime ∧ p∣m ∧ p%4=3 ∧ ¬Even (padicValNat p m) := by
  classical
  have no : ¬∃ x y : ℕ, m=x^2+y^2 := by
    rintro ⟨x,y,e⟩
    have one : (m:ZMod 4)=3 := (ZMod.natCast_eq_natCast_iff' _ 3 4).mpr hm
    rw [e,Nat.cast_add,Nat.cast_pow,Nat.cast_pow] at one
    exact not_sum_three x y one
  have neg := mt Nat.eq_sq_add_sq_iff.mpr no
  push Not at neg
  obtain ⟨p,mem,res,odd⟩ := neg
  exact ⟨p,Nat.prime_of_mem_primeFactors mem,Nat.dvd_of_mem_primeFactors mem,res,odd⟩

private theorem survive {a b θ h p : ℕ} (cp : a.Coprime b) (pp : p.Prime)
    (ap : p∣a) (odd : ¬Even (padicValNat p a)) (na : a≠0) (nb : b≠0)
    (eq : a*b=θ*h^2) : p∣θ := by
  let : Fact p.Prime := ⟨pp⟩
  have nθ : θ≠0 := by rintro rfl; simp [na,nb] at eq
  have nh : h≠0 := by rintro rfl; simp [na,nb] at eq
  have pb : ¬p∣b := fun d=>pp.not_dvd_one (cp ▸ Nat.dvd_gcd ap d)
  by_contra miss
  have vals := congrArg (padicValNat p) eq
  rw [padicValNat.mul na nb,padicValNat.eq_zero_of_not_dvd pb,padicValNat.mul nθ (pow_ne_zero _ nh),
    padicValNat.eq_zero_of_not_dvd miss,padicValNat.pow] at vals
  exact odd ⟨padicValNat p h,by omega⟩

/-- Every output of the positive integral family contains two distinct prime
divisors congruent to 3 modulo 4, one from each factor. No primality
assumption or analytic distribution is used. -/
theorem two_three_mod_four {β k θ h : ℕ} (hk : β<k^2) (bk : β.Coprime k)
    (six : 6∣k) (bm : β%24=17) (eq : (k^2-β)*(9*k^2-β)=θ*h^2) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ p%4=3 ∧ q%4=3 ∧
      p∣k^2-β ∧ q∣9*k^2-β ∧ p∣θ ∧ q∣θ := by
  have cp := factors_coprime hk bk six
  have even : 2∣k := (show 2∣6 by decide).trans six
  have div : 4∣k^2 := by simpa using pow_dvd_pow_of_dvd even 2
  have r : k^2%4=0 := Nat.mod_eq_zero_of_dvd div
  have s : (9*k^2)%4=0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right div 9)
  have nine : β<9*k^2 := by omega
  obtain ⟨p,pp,pa,pm,po⟩ := odd_order_prime (m:=k^2-β) (by omega)
  obtain ⟨q,qp,qb,qm,qo⟩ := odd_order_prime (m:=9*k^2-β) (by omega)
  have ne : p≠q := by rintro rfl; exact pp.not_dvd_one (cp ▸ Nat.dvd_gcd pa qb)
  exact ⟨p,q,pp,qp,ne,pm,qm,pa,qb,survive cp pp pa po (by omega) (by omega) eq,
    survive cp.symm qp qb qo (by omega) (by omega) ((Nat.mul_comm _ _).trans eq)⟩

theorem no_prime_output {β k θ h : ℕ} (hk : β<k^2) (bk : β.Coprime k)
    (six : 6∣k) (bm : β%24=17) (eq : (k^2-β)*(9*k^2-β)=θ*h^2) : ¬θ.Prime := by
  obtain ⟨p,q,pp,qp,ne,_,_,_,_,pθ,qθ⟩ := two_three_mod_four hk bk six bm eq
  intro pt
  exact ne (((Nat.prime_dvd_prime_iff_eq pp pt).mp pθ).trans ((Nat.prime_dvd_prime_iff_eq qp pt).mp qθ).symm)

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.two_three_mod_four
#print axioms Sun28.TwistPrimes.no_prime_output
