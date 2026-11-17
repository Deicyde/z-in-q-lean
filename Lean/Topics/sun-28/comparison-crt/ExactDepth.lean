import ComparisonProgression

namespace Sun28.ComparisonCRT

/-- The normalized local residue forces the exact additive valuation for signed h. -/
theorem exact_order {p depth : ℕ} (prime : p.Prime) {h : ℤ}
    (res : h ≡ (p:ℤ)^depth [ZMOD (p:ℤ)^(depth+1)]) :
    h≠0 ∧ padicValInt p h=depth := by
  have low : (p:ℤ)^depth∣h :=
    Int.modEq_zero_iff_dvd.mp ((res.of_dvd (pow_dvd_pow (p:ℤ) (Nat.le_succ depth))).trans
      (Int.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have high : ¬ (p:ℤ)^(depth+1)∣h := by
    intro d
    have back := res.symm.trans (Int.modEq_zero_iff_dvd.mpr d)
    have v := Int.natAbs_dvd_natAbs.mpr (Int.modEq_zero_iff_dvd.mp back)
    simp only [Int.natAbs_pow,Int.natAbs_natCast] at v
    have bad := (Nat.pow_dvd_pow_iff_le_right prime.one_lt).mp v
    omega
  have nz : h≠0 := by rintro rfl; exact high (dvd_zero _)
  have hn := Int.natAbs_ne_zero.mpr nz
  have lo : depth≤h.natAbs.factorization p := (prime.pow_dvd_iff_le_factorization hn).mp
    (by simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr low)
  have hi : ¬depth+1≤h.natAbs.factorization p := by
    intro large
    have d := (prime.pow_dvd_iff_le_factorization hn).mpr large
    exact high (Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_pow,Int.natAbs_natCast] using d))
  rw [Nat.factorization_def _ prime] at lo hi
  exact ⟨nz,by unfold padicValInt; omega⟩

theorem Congruences.exact_depth {plus minus κ anchor : ℕ} {T : Finset ℕ} {a : ℕ→ℕ} {h : ℤ}
    (conditions : Congruences plus minus κ anchor T a h) {p : ℕ} (hp : p.Prime) (mem : p∈T) :
    h≠0 ∧ padicValInt p h=a p := exact_order hp (conditions.localResidue p mem)

end Sun28.ComparisonCRT
#print axioms Sun28.ComparisonCRT.exact_order
#print axioms Sun28.ComparisonCRT.Congruences.exact_depth
