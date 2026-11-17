import FixedData
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The explicit local order bound for the fixed anchor. -/
namespace Sun28.FixedPreparation

private theorem two_factors {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hs : i ≤ 576) (ht : j ≤ 576) (hne : i ≠ j) : i * j ∣ Nat.factorial 576 := by
  let s : Finset ℕ := {i-1,j-1}
  have sub : s ⊆ Finset.range 576 := by
    intro x hx
    simp only [s,Finset.mem_insert,Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  have dvd := Finset.prod_dvd_prod_of_subset s (Finset.range 576) (fun j => j+1) sub
  rw [Finset.prod_range_add_one_eq_factorial] at dvd
  have dist : i-1 ≠ j-1 := by omega
  simpa [s,dist,Nat.sub_add_cancel hi,Nat.sub_add_cancel hj] using dvd

theorem factorial_local_order {q n : ℕ} (q0 : 0<q) (q23 : q≤23) (n0 : 0<n)
    (n576 : n≤576) : q*n∣anchor.natAbs := by
  change q*n∣Nat.factorial 576
  by_cases ne : q=n
  · have div : q*n ∣ (2*q)*n := ⟨2,by ring⟩
    exact div.trans (two_factors (by omega) n0 (by omega) n576 (by omega))
  · exact two_factors q0 n0 (by omega) n576 ne

/-- A point count of twice the residue-field size suffices at every good place. -/
theorem factorial_even_group {q t : ℕ} (q0 : 1 ≤ q) (q23 : q ≤ 23)
    (t0 : 1 ≤ t) (t529 : t ≤ 529) : q*(2*t) ∣ anchor.natAbs := by
  change q*(2*t) ∣ Nat.factorial 576
  by_cases eq : 2*q=t
  · have d : q*(2*t) ∣ (4*q)*t := ⟨2,by ring⟩
    exact d.trans (two_factors (by omega) t0 (by omega) (by omega) (by omega))
  · rw [show q*(2*t)=(2*q)*t by ring]
    exact two_factors (by omega) t0 (by omega) (by omega) eq

theorem anchor_64 : (64:ℤ) ∣ anchor := by
  change (64:ℤ)∣((Nat.factorial 576:ℕ):ℤ)
  exact_mod_cast Nat.dvd_factorial (by decide : 0<64) (by decide : 64≤576)

/-- The factorial kills every finite reduction group of Hasse size at these primes,
retaining a further factor of q for one step in the formal filtration. -/
theorem anchor_reduction {G : Type*} [AddGroup G] [Fintype G] (g : G) {q : ℕ}
    (q0 : 0<q) (q23 : q≤23) (size : Fintype.card G ≤ (q+1)^2) :
    ∃ k : ℕ, anchor.natAbs=q*Fintype.card G*k ∧ (Fintype.card G) • g=0 := by
  obtain ⟨k,h⟩ := factorial_local_order q0 q23 (Fintype.card_pos)
    (size.trans (show (q+1)^2≤576 from (Nat.pow_le_pow_left (by omega : q+1≤24) 2)))
  exact ⟨k,h,by simp⟩

end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.factorial_local_order
#print axioms Sun28.FixedPreparation.factorial_even_group
#print axioms Sun28.FixedPreparation.anchor_64
#print axioms Sun28.FixedPreparation.anchor_reduction
