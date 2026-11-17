import CutoffProduct
import ShiftTuple

namespace Sun28.MixedSieve
open Sun28.ContactFactors

/-- The coefficients of the actual integer quadratic prime pattern, reduced modulo p. -/
noncomputable def coefficients (A : Fin 3→ℚ) (p : ℕ) (r : ↥(shifts A)) : ZMod p :=
  (offset (dilation A) r.val : ℤ)

noncomputable def markedLoss (A : Fin 3→ℚ) (p : ℕ) : ℝ := by
  classical
  exact if h : p.Prime then
    let _ : Fact p.Prime := ⟨h⟩
    relativeLoss (coefficients A p)
  else 0

theorem marked_bound (A : Fin 3→ℚ) (p : ℕ) (large : 2810≤p) :
    markedLoss A p ≤ 1404/((p:ℝ)-1)^2 := by
  classical
  by_cases prime : p.Prime
  · let _ : Fact p.Prime:=⟨prime⟩
    have hk : Fintype.card ↥(shifts A) ≤13 := by
      simpa using Sun28.GaussianSelection.shifts_card_le A
    have bound := thirteen (p:=p) (show 26≤p by omega) hk (coefficients A p)
    simpa [markedLoss,prime] using bound
  · simp [markedLoss,prime]
    positivity

theorem marked_large_sum (A : Fin 3→ℚ) (S : Finset ℕ) (large : ∀ p∈S,2810≤p) :
    (∑ p∈S,markedLoss A p) ≤ 1/2 :=
  uniform_sum S _ large fun p hp => marked_bound A p (large p hp)

theorem marked_large_factors (A : Fin 3→ℚ) (S : Finset ℕ) (large : ∀ p∈S,2810≤p) :
    1/2 ≤ ∏ p∈S,(1-markedLoss A p) := by
  classical
  apply uniform_product S _ large
  · intro p _
    by_cases prime : p.Prime
    · let _ : Fact p.Prime:=⟨prime⟩
      simpa [markedLoss,prime] using relative_nonneg (coefficients A p)
    · simp [markedLoss,prime]
  · exact fun p hp => marked_bound A p (large p hp)

/-- The numerator in the local norm model is the reduction of Sun's prime value. -/
theorem prime_value_residue {A : Fin 3→ℚ} {u v : ℕ}
    (values : PrimeValues A u v) (r : ↥(shifts A)) (p : ℕ) [Fact p.Prime] :
    norms (coefficients A p) (u:ZMod p) (v:ZMod p) r=(values.value r.val:ZMod p) := by
  have e:=congrArg (fun a : ℤ => (a:ZMod p)) (values.equation r.val r.property)
  simpa only [Int.cast_natCast,Int.cast_add,Int.cast_mul,Int.cast_pow,norms,coefficients] using e.symm

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.marked_bound
#print axioms Sun28.MixedSieve.marked_large_sum
#print axioms Sun28.MixedSieve.marked_large_factors
#print axioms Sun28.MixedSieve.prime_value_residue
