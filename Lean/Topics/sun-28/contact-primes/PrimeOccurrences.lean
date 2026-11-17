import ShiftDenominators

namespace Sun28.ContactFactors
open Sun28.Ordinary
noncomputable section

/-- A selected rational prime for each distinct cleared shift. Repeated
occurrences of a shift have one prime in all three detectors. -/
structure PrimeValues (A : Fin 3→ℚ) (u v : ℕ) where
  value : ℚ → ℕ
  prime : ∀ r∈shifts A, (value r).Prime
  equation : ∀ r∈shifts A, (value r:ℤ)=(u:ℤ)+offset (dilation A) r*(v:ℤ)^2

variable {A : Fin 3→ℚ} {u v : ℕ}

theorem PrimeValues.rational_equation (h : PrimeValues A u v) {r : ℚ} (hr : r∈shifts A) :
    (h.value r:ℚ)=(u:ℚ)+r*((dilation A*v:ℕ):ℚ)^2 := by
  have e := congrArg (fun x : ℤ => (x:ℚ)) (h.equation r hr)
  push_cast at e ⊢
  rw [offset_eq hr] at e
  linear_combination e

theorem PrimeValues.injective_on (h : PrimeValues A u v) (vp : 0<v) {r s : ℚ}
    (hr : r∈shifts A) (hs : s∈shifts A) (eqn : h.value r=h.value s) : r=s := by
  have e := congrArg (fun n : ℕ => (n:ℚ)) eqn
  rw [h.rational_equation hr,h.rational_equation hs] at e
  exact mul_right_cancel₀ (pow_ne_zero 2 (by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'))
    (add_left_cancel e)

theorem PrimeValues.prime_not_dvd_parameter (h : PrimeValues A u v) (one : A 0=1)
    (vp : 0<v) {r : ℚ} (hr : r∈shifts A) : ¬ h.value r∣v := by
  intro dv
  let p:=h.value r
  have pp : p.Prime:=h.prime r hr
  have cd : (p:ℤ)∣(v:ℤ)^2:=dvd_pow ((Int.natCast_dvd_natCast.mpr dv)) two_ne_zero
  have du : (p:ℤ)∣(u:ℤ) := by
    have d : (p:ℤ)∣(u:ℤ)+offset (dilation A) r*(v:ℤ)^2 := h.equation r hr ▸ dvd_refl _
    exact (dvd_add_left (dvd_mul_of_dvd_right cd _)).mp d
  have others (s : ℚ) (hs : s∈shifts A) : h.value s=p := by
    have d : (p:ℤ)∣(h.value s:ℤ) := by
      rw [h.equation s hs]
      exact dvd_add du (dvd_mul_of_dvd_right cd _)
    exact ((Nat.prime_dvd_prime_iff_eq pp (h.prime s hs)).mp (Int.natCast_dvd_natCast.mp d)).symm
  have incl : shifts A⊆{r} := by
    intro s hs
    exact Finset.mem_singleton.mpr (h.injective_on vp hs hr (others s hs))
  have bound:=Finset.card_le_card incl
  rw [Finset.card_singleton] at bound
  have large:=enough_shifts A one
  omega

theorem PrimeValues.unit_at_denominator (h : PrimeValues A u v) (one : A 0=1)
    (vp : 0<v) {r : ℚ} (hr : r∈shifts A) (off : ¬h.value r∣dilation A) :
    ¬h.value r∣dilation A*v :=
  fun d => ((h.prime r hr).dvd_mul.mp d).elim off (h.prime_not_dvd_parameter one vp hr)

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.PrimeValues.rational_equation
#print axioms Sun28.ContactFactors.PrimeValues.injective_on
#print axioms Sun28.ContactFactors.PrimeValues.prime_not_dvd_parameter
#print axioms Sun28.ContactFactors.PrimeValues.unit_at_denominator
