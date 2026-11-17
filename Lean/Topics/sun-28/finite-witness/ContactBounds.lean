import ExceptionalWalk

/-! A single lower bound separates the selected rational primes from the
entire earlier set of scalar primes, including prime divisors of the input. -/
namespace Sun28.FiniteWitness
open Sun28.ContactFactors
def selectionBound (T : Finset ℕ) : ℕ := max 65 (T.sup id)

theorem separated_values {A : Fin 3→ℚ} {u v : ℕ} (h : PrimeValues A u v) (T : Finset ℕ)
    (large : ∀ d∈shifts A,(selectionBound T:ℝ)<(h.value d:ℝ)) :
    (∀ d∈shifts A,65<h.value d) ∧ (∀ d∈shifts A,h.value d∉T) := by
  have bound (d : ℚ) (hd : d∈shifts A) : selectionBound T<h.value d := by exact_mod_cast large d hd
  refine ⟨fun d hd => (le_max_left ..).trans_lt (bound d hd),?_⟩
  intro d hd member
  have le : h.value d≤T.sup id := Finset.le_sup (f:=id) member
  exact (bound d hd).not_ge (le.trans (le_max_right ..))
end Sun28.FiniteWitness
#print axioms Sun28.FiniteWitness.separated_values
