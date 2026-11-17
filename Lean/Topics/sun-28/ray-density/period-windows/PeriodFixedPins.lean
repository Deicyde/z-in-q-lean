import PeriodSharedPrime
import ActualOrders

namespace Sun28.PeriodWindows
open Sun28.QualitativeRows Sun28.ContactFactors Sun28.ScalarPlaces Sun28.FixedPreparation

noncomputable def guard (r : ℤ) (L : ℕ) : ℕ :=
  max L (max (kernelMod r) ((supportPlaces r).sup id))

theorem small_gcd {m b : ℕ} (bp : 0 < b) (mp : 0 < m) (two : padicValNat 2 b≤6)
    (away : ∀ q, q.Prime → q≠2 → q∣m → ¬q∣b) : m.gcd b ∣ 2^6 := by
  apply (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _ mp).ne' (by decide : (2^6:ℕ)≠0)).mp
  intro q
  by_cases h : q=2
  · subst q
    rw [Nat.factorization_gcd mp.ne' bp.ne', Finsupp.inf_apply]
    exact (min_le_right ..).trans (by
      rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
      exact two.trans_eq (padicValNat.prime_pow (p:=2) 6).symm)
  by_cases prime : q.Prime
  · have nod : ¬q∣m.gcd b := fun d=> away q prime h
        (d.trans (Nat.gcd_dvd_left ..)) (d.trans (Nat.gcd_dvd_right ..))
    simp [Nat.factorization_eq_zero_of_not_dvd nod]
  · simp [Nat.factorization_eq_zero_of_not_prime _ prime]

theorem sixtyfour_dvd_anchor : 2^6 ∣ Nat.factorial 576 :=
  Nat.dvd_factorial (by decide) (by decide)

theorem all_pins {r : ℤ} {L b : ℕ} (bp : 0 < b) (two : padicValNat 2 b≤6)
    (free : ∀ q, q.Prime → q≠2 → q≤guard r L → ¬q∣b) :
    ∀ j (t : Bool), fixedRes r j ≡ (if t then Nat.factorial 576 else 0)
      [MOD (fixedMod r j).gcd b] := by
  intro j t
  have div {g a : ℕ} (first : g∣a) (second : g∣Nat.factorial 576) :
      a ≡ (if t then Nat.factorial 576 else 0) [MOD g] := by
    have z := Nat.modEq_zero_iff_dvd.mpr first
    cases t
    · exact z
    · exact z.trans (Nat.modEq_zero_iff_dvd.mpr second).symm
  cases j with
  | none =>
    exact div (dvd_zero _) ((small_gcd bp (kernel_positive r) two (fun q hp hq dm =>
      free q hp hq ((Nat.le_of_dvd (kernel_positive r) dm).trans
        ((le_max_left ..).trans (le_max_right ..))))).trans sixtyfour_dvd_anchor)
  | some p =>
    have pp:=support_prime p.property
    have bound : p.val≤guard r L := (Finset.le_sup (f:=id) p.property).trans
      ((le_max_right ..).trans (le_max_right ..))
    by_cases dy : p.val=2
    · let a:=comparisonDepth r p.val
      have dep : 6≤a:=by dsimp [a,comparisonDepth];omega
      have gd : (p.val^(a+1)).gcd b ∣ 2^6 := small_gcd bp (pow_pos pp.pos _) two (by
        intro q qp qn dvd
        have same:= (Nat.prime_dvd_prime_iff_eq qp pp).mp (qp.dvd_of_dvd_pow dvd)
        exact (qn (same.trans dy)).elim)
      apply div (gd.trans (by change 2^6 ∣ p.val^a; rw [dy];exact pow_dvd_pow 2 dep)) (gd.trans sixtyfour_dvd_anchor)
    · have co := (pp.coprime_iff_not_dvd.mpr (free _ pp dy bound)).pow_left (comparisonDepth r p.val+1)
      change _ ≡ _ [MOD (p.val^(comparisonDepth r p.val+1)).gcd b]
      rw [co.gcd_eq_one]
      exact Nat.modEq_one

theorem excess_past_cutoff {r : ℤ} {L b q : ℕ} (two : padicValNat 2 b≤6)
    (free : ∀ q, q.Prime → q≠2 → q≤guard r L → ¬q∣b)
    (bad : excess (Nat.factorial 576) b q) : guard r L < q := by
  by_contra! le
  obtain ⟨hp,h⟩:=bad
  by_cases dy : q=2
  · subst q
    have hf := (Nat.factorization_le_iff_dvd (by decide : (2^6:ℕ)≠0)
      (Nat.factorial_ne_zero 576)).mpr sixtyfour_dvd_anchor (2:ℕ)
    simp only [Nat.factorization_def _ Nat.prime_two, padicValNat.prime_pow] at h hf
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd (free _ hp dy le)] at h
    omega

end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.small_gcd
#print axioms Sun28.PeriodWindows.all_pins
#print axioms Sun28.PeriodWindows.excess_past_cutoff
