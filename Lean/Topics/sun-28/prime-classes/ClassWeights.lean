import PrimeClassRays
import HybridCount

namespace Sun28.PrimeClasses
open Finset Sun28.FinitePattern Sun28.PrimeLower Sun28.ContactFactors ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

def primeLog (K L : ℕ) (n : ℤ) : ℝ :=
  if 0≤n ∧ rationalPrime K L n.toNat then Real.log (n.toNat : ℝ) else 0

def crossing (A : Fin 3→ℚ) (K L : ℕ) (x : ℕ×ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → K<q → q≤L →
    if q%4=3 then ¬((x.1:ZMod q)=1 ∧ (x.2:ZMod q)=0)
    else (∀ i : ↥(shifts A), ¬(q:ℤ)∣signedOrder (form A x i).toNat true) ∨
         (∀ i : ↥(shifts A), ¬(q:ℤ)∣signedOrder (form A x i).toNat false)

def rationalWeight (A : Fin 3→ℚ) (K L : ℕ) (x : ℕ×ℕ) : ℝ :=
  if crossing A K L x then ∏ i : ↥(shifts A),primeLog K K (form A x i) else 0

def rationalMass (A : Fin 3→ℚ) (d K L N W : ℕ) : ℝ :=
  ∑ x∈((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun x : ℕ×ℕ => d∣x.2)),rationalWeight A K L x

theorem prime_log_eq (K L : ℕ) (n : ℤ) : primeLog K L n=primeWeight K L n := by
  simp only [primeLog,primeWeight,common_prime_iff]

theorem crossing_iff {A : Fin 3→ℚ} {K L : ℕ} {x : ℕ×ℕ}
    (base : ∀ i : ↥(shifts A),commonPrime K K (form A x i).toNat) :
    crossing A K L x ↔ extraTest A K L x := by
  constructor
  · intro poly
    choose z n h16 h7 _ using fun i => (base i).2
    refine ⟨z,fun i => ⟨n i,h16 i,h7 i⟩,?_⟩
    intro q pp above below
    have X := poly q pp above below
    by_cases inert : q%4=3
    · simpa [inert] using X
    simp only [inert,ite_false] at X ⊢
    simpa only [order_dvd_iff (base _).1 (n _) (h16 _) (h7 _)] using X
  · rintro ⟨z,ray,h⟩ q pp lower upper
    have X := h q pp lower upper
    by_cases inert : q%4=3
    · simpa [inert] using X
    simp only [inert,ite_false] at X ⊢
    simpa only [order_dvd_iff (base _).1 (ray _).1 (ray _).2.1 (ray _).2.2] using X

theorem rational_weight_eq (A : Fin 3→ℚ) (K L : ℕ) (x : ℕ×ℕ) :
    rationalWeight A K L x=hybridWeight A K L x := by
  unfold rationalWeight hybridWeight
  simp only [prime_log_eq]
  by_cases allbase : ∀ i : ↥(shifts A),commonPrime K K (form A x i).toNat
  · rw [crossing_iff allbase]
    rfl
  · push Not at allbase
    obtain ⟨i,bad⟩ := allbase
    have zero : primeWeight K K (form A x i)=0 := by simp [primeWeight,bad]
    have prod : patternWeight A K K x=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) zero
    change (if crossing A K L x then patternWeight A K K x else 0)=_
    simp [prod]

theorem rational_mass_eq (A : Fin 3→ℚ) (d K L N W : ℕ) :
    rationalMass A d K L N W=hybridMass A d K L N W := by
  simp only [rationalMass,hybridMass,rational_weight_eq]

end
end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.prime_log_eq
#print axioms Sun28.PrimeClasses.crossing_iff
#print axioms Sun28.PrimeClasses.rational_weight_eq
#print axioms Sun28.PrimeClasses.rational_mass_eq
