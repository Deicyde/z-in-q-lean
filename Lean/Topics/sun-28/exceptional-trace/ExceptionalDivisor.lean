import ExceptionalTrace

/-! One prescribed natural divisibility suffices for all three scales and all nine primes. -/
namespace Sun28.Exceptional
open Sun28.FixedPreparation

def requiredExponent (A : Fin 3 → ℚ) (p : ℕ) (j : Fin 3) : ℕ :=
  3+106*(padicValRat p (A j)).natAbs

def requiredDivisor (A : Fin 3 → ℚ) : ℕ :=
  ∏ p∈primes, p^(Finset.univ.sup (requiredExponent A p))

theorem divisor_positive (A : Fin 3 → ℚ) : 0<requiredDivisor A := by
  have prime : ∀ p∈primes,Nat.Prime p := by decide
  exact Finset.prod_pos (fun p hp=>pow_pos (prime p hp).pos _)

theorem large_of_dvd (A : Fin 3 → ℚ) {w : ℕ} (wn : w≠0) (divisor : requiredDivisor A∣w)
    {p : ℕ} (fixed : p∈primes) (j : Fin 3) :
    6+211*|padicValRat p (A j)|≤padicValRat p ((w:ℚ)^2) := by
  have prime : ∀ p∈primes,Nat.Prime p := by decide
  let _ := Fact.mk (prime p fixed)
  have high : requiredExponent A p j≤Finset.univ.sup (requiredExponent A p) :=
    Finset.le_sup (Finset.mem_univ j)
  have pw : p^(requiredExponent A p j)∣w :=
    (pow_dvd_pow p high).trans ((Finset.dvd_prod_of_mem (fun q => q^(Finset.univ.sup (requiredExponent A q))) fixed).trans divisor)
  have v:=(padicValNat_dvd_iff_le wn).mp pw
  change 3+106*(padicValRat p (A j)).natAbs ≤padicValNat p w at v
  have hh : (3:ℤ)+106*|(padicValRat p (A j))|≤(padicValNat p w:ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast v
  rw [padicValRat.pow,padicValRat.of_nat]
  push_cast
  linarith [abs_nonneg (padicValRat p (A j))]

#print axioms divisor_positive
#print axioms large_of_dvd
end Sun28.Exceptional
