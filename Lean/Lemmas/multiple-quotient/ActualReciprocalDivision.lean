import BinaryDivisionPolynomials
import KummerLaw

/-! Binary multiplication of the abscissa on `y² = x³ - D x` in the chart `(1 : q)`. -/

namespace ReciprocalDivision

open EllipticOrbit.Law

variable {K : Type*} [Field K] [DecidableEq K] {D q : K}

private theorem double_rep_normalized {M : (curve D).Point} {p : K × K}
    (h : Rep M p.1 (q * p.2)) :
    Rep (M + M) (double (D * q ^ 2) p).1 (q * (double (D * q ^ 2) p).2) := by
  convert double_rep M h using 1 <;> dsimp [double, dblNum, dblDen] <;> ring

/-- Differential addition cancels one copy of the single fixed seed parameter `q`.
    The inputs, their sum, and their difference can be read in projective coordinates. -/
private theorem middle_rep_normalized {M N : (curve D).Point} {p r : K × K}
    (hq : q ≠ 0) (hp : Rep M p.1 (q * p.2)) (hr : Rep N r.1 (q * r.2))
    (hd : Rep (M - N) 1 q) :
    Rep (M + N) (middle (D * q ^ 2) p r).1 (q * (middle (D * q ^ 2) p r).2) := by
  obtain ⟨c, hc, htop, _, hbottom⟩ := symmetric_rep M N hp hr (canonical_rep (M + N)) hd
  refine ⟨c, hc, ?_, ?_⟩
  · dsimp only [middle]
    linear_combination htop
  · dsimp only [middle]
    apply mul_left_cancel₀ hq
    linear_combination hbottom

private theorem two_steps (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q)
    {n : ℕ} {p r : K × K}
    (hp : Rep (n • P) p.1 (q * p.2)) (hr : Rep ((n + 1) • P) r.1 (q * r.2)) :
    Rep ((2 * n) • P) (double (D * q ^ 2) p).1 (q * (double (D * q ^ 2) p).2) ∧
    Rep ((2 * n + 1) • P) (middle (D * q ^ 2) p r).1 (q * (middle (D * q ^ 2) p r).2) ∧
    Rep ((2 * n + 2) • P) (double (D * q ^ 2) r).1 (q * (double (D * q ^ 2) r).2) := by
  have hd : n • P - (n + 1) • P = -P := by rw [add_nsmul, one_nsmul]; abel
  have hs : n • P + (n + 1) • P = (2 * n + 1) • P := by
    rw [← add_nsmul, show n + (n + 1) = 2 * n + 1 by omega]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_smul, two_nsmul] using double_rep_normalized hp
  · rw [← hs]
    exact middle_rep_normalized hq hp hr (hd ▸ rep_neg.mpr seed)
  · rw [show 2 * n + 2 = 2 * (n + 1) by omega]
    simpa only [mul_smul, two_nsmul] using double_rep_normalized hr

/-- Both entries computed by the binary ladder represent the two actual adjacent multiples. -/
theorem adjacent_rep (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q) (s : Bits) :
    let t := adjacent (D * q ^ 2) s
    Rep (s.index • P) t.1.1 (q * t.1.2) ∧ Rep ((s.index + 1) • P) t.2.1 (q * t.2.2) := by
  induction s with
  | zero =>
    simp only [Bits.index, adjacent, zero_nsmul, Nat.zero_add, one_nsmul, mul_zero, mul_one]
    exact ⟨rep_zero.mpr ⟨one_ne_zero, rfl⟩, seed⟩
  | bit0 s ih =>
    obtain ⟨even, middle, _⟩ := two_steps P hq seed ih.1 ih.2
    exact ⟨even, middle⟩
  | bit1 s ih =>
    obtain ⟨_, middle, even⟩ := two_steps P hq seed ih.1 ih.2
    exact ⟨middle, even⟩

/-- Natural multiplication on Mathlib's actual affine group, with homogeneous output. -/
theorem quotient_rep_nat (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q) (n : ℕ) :
    Rep (n • P) (quotientPair (D * q ^ 2) n).1 (q * (quotientPair (D * q ^ 2) n).2) := by
  simpa only [quotientPair, index_bits] using (adjacent_rep P hq seed (bits n)).1

/-- Signed multiplication has the same abscissa as multiplication by the absolute value. -/
theorem quotient_rep (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q) (n : ℤ) :
    Rep (n • P) (quotientPair (D * q ^ 2) n.natAbs).1
      (q * (quotientPair (D * q ^ 2) n.natAbs).2) := by
  cases n with
  | ofNat n => simpa using quotient_rep_nat P hq seed n
  | negSucc n => simpa [rep_neg] using quotient_rep_nat P hq seed (n + 1)

omit [DecidableEq K] in
private theorem rep_cross {P : (curve D).Point} {a b c d : K}
    (h : Rep P a b) (k : Rep P c d) : a * d = b * c := by
  obtain ⟨s, _, rfl, rfl⟩ := h
  obtain ⟨t, _, rfl, rfl⟩ := k
  ring

/-- If `y` is the reciprocal abscissa of `[n]P`, then `y A = q B`. This also
    applies at infinity, where `y = 0`. -/
theorem reciprocal_equation (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q)
    (n : ℤ) {y : K} (hy : Rep (n • P) 1 y) :
    y * (quotientPair (D * q ^ 2) n.natAbs).1 = q * (quotientPair (D * q ^ 2) n.natAbs).2 := by
  simpa only [mul_one, mul_comm _ y] using rep_cross (quotient_rep P hq seed n) hy

/-- Reciprocal abscissa, using the field's total division at an abscissa with zero top. -/
def reciprocal (P : (curve D).Point) : K := (abscissa P).2 / (abscissa P).1

omit [DecidableEq K] in
theorem rep_reciprocal_of_top_ne (P : (curve D).Point) (h : (abscissa P).1 ≠ 0) :
    Rep P 1 (reciprocal P) := by
  refine ⟨(abscissa P).1⁻¹, inv_ne_zero h, (inv_mul_cancel₀ h).symm, ?_⟩
  rw [reciprocal, div_eq_mul_inv, mul_comm]

omit [DecidableEq K] in
theorem rep_reciprocal (P : (curve D).Point) (h : reciprocal P ≠ 0) : Rep P 1 (reciprocal P) := by
  apply rep_reciprocal_of_top_ne
  intro e
  exact h (by simp [reciprocal, e])

/-- The intrinsic function `reciprocal` supplies both chart coordinates in the cleared
    multiplication equation. The top hypothesis ensures the result is in this chart. -/
theorem total_reciprocal_equation (P : (curve D).Point) (hq : reciprocal P ≠ 0) (n : ℤ)
    (htop : (quotientPair (D * reciprocal P ^ 2) n.natAbs).1 ≠ 0) :
    reciprocal (n • P) * (quotientPair (D * reciprocal P ^ 2) n.natAbs).1 =
      reciprocal P * (quotientPair (D * reciprocal P ^ 2) n.natAbs).2 := by
  have seed := rep_reciprocal P hq
  obtain ⟨s, _, hs, _⟩ := quotient_rep P hq seed n
  apply reciprocal_equation P hq seed
  apply rep_reciprocal_of_top_ne
  intro e
  exact htop (by rw [hs, e, mul_zero])

/-- A zero denominator detects precisely the multiples that are the point at infinity. -/
theorem bottom_zero_iff (P : (curve D).Point) (hq : q ≠ 0) (seed : Rep P 1 q) (n : ℤ) :
    (quotientPair (D * q ^ 2) n.natAbs).2 = 0 ↔ n • P = 0 := by
  have h := quotient_rep P hq seed n
  generalize n • P = M at h ⊢
  cases M with
  | zero => exact iff_of_true (by simpa [hq] using (rep_zero.mp h).2) rfl
  | @some x y nonsing =>
    have nz := (rep_some nonsing |>.mp h).1
    constructor
    · intro e
      exact (nz (by rw [e, mul_zero])).elim
    · intro e
      cases e

end ReciprocalDivision
