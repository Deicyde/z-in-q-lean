import PrimePowers
import Mathlib.Data.Nat.Factorization.LCM

namespace Sun28.QualitativeRows.CRT

/-- A finite system can contain overlapping, positive moduli. -/
theorem solve {ι : Type*} (s : Finset ι) (m r : ι → ℕ)
    (pos : ∀ i ∈ s, 0 < m i)
    (compat : ∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD (m i).gcd (m j)]) :
    ∃ h : ℤ, ∃ step : ℕ, 0 < step ∧ ∀ k : ℤ, ∀ i ∈ s,
      h + (step : ℤ)*k ≡ (r i : ℤ) [ZMOD (m i : ℤ)] := by
  classical
  by_cases empty : s = ∅
  · subst s
    exact ⟨0, 1, by decide, by simp⟩
  have sn := Finset.nonempty_iff_ne_empty.mpr empty
  have winner (p : ℕ) : ∃ i ∈ s, ∀ j ∈ s, (m j).factorization p ≤ (m i).factorization p :=
    s.exists_max_image (fun j => (m j).factorization p) sn
  choose w member best using winner
  let S := s.biUnion (fun i => (m i).primeFactors)
  let e := fun p => (m (w p)).factorization p
  obtain ⟨h, stepPos, all⟩ := Sun28.ComparisonCRT.prime_progression S e (fun p => r (w p))
    (fun p hp => by
      obtain ⟨i, _, mem⟩ := Finset.mem_biUnion.mp hp
      exact Nat.prime_of_mem_primeFactors mem)
  refine ⟨h, _, stepPos, ?_⟩
  intro k i hi
  apply Sun28.ComparisonCRT.assemble (pos i hi).ne'
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have mem : p ∈ S := Finset.mem_biUnion.mpr ⟨i,hi,hp⟩
  have enough := best p i hi
  have di : p^(m i).factorization p ∣ m i := Nat.ordProj_dvd _ _
  have dw : p^(m i).factorization p ∣ m (w p) :=
    (pow_dvd_pow p enough).trans (Nat.ordProj_dvd _ _)
  have rel := (compat (w p) (member p) i hi).of_dvd (Nat.dvd_gcd dw di)
  have eq : (r (w p) : ℤ) ≡ (r i : ℤ) [ZMOD (p:ℤ)^((m i).factorization p)] := by
    simpa only [Nat.cast_pow] using Int.natCast_modEq_iff.mpr rel
  exact ((all k p mem).of_dvd (pow_dvd_pow (p:ℤ) enough)).trans eq

/-- Compatibility at the pairwise gcds is an exact, finite test. -/
theorem exists_iff {ι : Type*} (s : Finset ι) (m r : ι → ℕ)
    (pos : ∀ i ∈ s, 0 < m i) :
    (∃ h : ℤ, ∀ i ∈ s, h ≡ (r i : ℤ) [ZMOD (m i : ℤ)]) ↔
    ∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD (m i).gcd (m j)] := by
  constructor
  · rintro ⟨h, good⟩ i hi j hj
    have left := (good i hi).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (m i) (m j)))
    have right := (good j hj).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (m i) (m j)))
    exact Int.natCast_modEq_iff.mp (left.symm.trans right)
  · intro compat
    obtain ⟨h, _, _, all⟩ := solve s m r pos compat
    exact ⟨h, by simpa using all 0⟩

end Sun28.QualitativeRows.CRT

#print axioms Sun28.QualitativeRows.CRT.solve
#print axioms Sun28.QualitativeRows.CRT.exists_iff
