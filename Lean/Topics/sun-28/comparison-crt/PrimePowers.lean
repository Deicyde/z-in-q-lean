import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.ModEq

namespace Sun28.ComparisonCRT
open scoped BigOperators

/-- A congruence modulo a positive natural is determined by its prime-power parts. -/
theorem assemble {m : ℕ} (hm : m ≠ 0) {x y : ℤ}
    (uniform : ∀ p ∈ m.primeFactors, x ≡ y [ZMOD (p:ℤ)^(m.factorization p)]) :
    x ≡ y [ZMOD (m:ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  by_cases z : y-x=0
  · rw [z]; exact dvd_zero _
  have nz : (y-x).natAbs≠0 := Int.natAbs_ne_zero.mpr z
  have h : m ∣ (y-x).natAbs := (Nat.factorization_prime_le_iff_dvd hm nz).1 (by
    intro p hp
    by_cases d : p∣m
    · have div := (uniform p (Nat.mem_primeFactors.mpr ⟨hp,d,hm⟩)).dvd
      apply (hp.pow_dvd_iff_le_factorization nz).1
      simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr div
    · rw [Nat.factorization_eq_zero_of_not_dvd d]; exact Nat.zero_le _)
  exact Int.natAbs_dvd_natAbs.mp (by simpa using h)

/-- The CRT at distinct prime powers gives one class, with every signed translate allowed. -/
theorem prime_progression (S : Finset ℕ) (exponent residue : ℕ→ℕ)
    (primes : ∀ p ∈ S, Nat.Prime p) :
    ∃ offset : ℤ, let period := ∏ p ∈ S, p^(exponent p)
      0<period ∧ ∀ k : ℤ, ∀ p ∈ S,
        offset+(period:ℤ)*k ≡ (residue p:ℤ) [ZMOD (p:ℤ)^(exponent p)] := by
  classical
  let s := fun p : ℕ => p^(exponent p)
  have nz (p : ℕ) (mem : p∈S) : s p≠0 := pow_ne_zero _ (primes p mem).ne_zero
  have cp : Set.Pairwise (↑S) (fun p q => Nat.Coprime (s p) (s q)) := by
    intro p hp q hq ne
    have pp := primes p hp
    have qq := primes q hq
    have h : Nat.Coprime p q := pp.coprime_iff_not_dvd.mpr (fun d=>ne ((Nat.prime_dvd_prime_iff_eq pp qq).mp d))
    exact (h.pow_left _).pow_right _
  let x := Nat.chineseRemainderOfFinset residue s S nz cp
  refine ⟨(x:ℕ),Finset.prod_pos (fun p hp=>pow_pos (primes p hp).pos _),?_⟩
  intro k p mem
  let N := ∏ j ∈ S,s j
  have d : s p∣N := Finset.dvd_prod_of_mem s mem
  have dv : ((s p:ℕ):ℤ)∣(N:ℤ) := Int.natCast_dvd_natCast.mpr d
  have jump : (x:ℕ)+(N:ℤ)*k ≡ (x:ℕ) [ZMOD (N:ℤ)] := Int.modEq_add_fac_self
  have res := Int.natCast_modEq_iff.mpr (x.prop p mem)
  simpa only [s,N,Nat.cast_pow] using (jump.of_dvd dv).trans res

end Sun28.ComparisonCRT
#print axioms Sun28.ComparisonCRT.assemble
#print axioms Sun28.ComparisonCRT.prime_progression
