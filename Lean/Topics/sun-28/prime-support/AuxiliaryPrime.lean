import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.ChineseRemainder

namespace Sun28.AuxiliaryPrimes
open scoped BigOperators
noncomputable section

/-- A finite list of unit classes at distinct support primes can be imposed
alongside the type of the auxiliary prime modulo twelve. -/
theorem prime_in_classes (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (a : ℕ → ℕ) (ha : ∀ p ∈ S, (a p).Coprime p) {r : ℕ} (hr : r.Coprime 12) (bound : ℕ) :
    ∃ q > bound, q.Prime ∧ q ≡ r [MOD 12] ∧ ∀ p ∈ S, q ≡ a p [MOD p] := by
  classical
  let P := ∏ p ∈ S, p
  have pair : Set.Pairwise (↑S) (fun p q : ℕ => p.Coprime q) := by
    intro p hp q hq ne
    exact (hs p hp).1.coprime_iff_not_dvd.mpr
      (fun d => ne ((Nat.prime_dvd_prime_iff_eq (hs p hp).1 (hs q hq).1).mp d))
  let x := Nat.chineseRemainderOfFinset a id S (fun p hp => (hs p hp).1.ne_zero) pair
  have c : Nat.Coprime 12 P := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    have h := hs p hp
    apply Nat.Coprime.symm
    apply h.1.coprime_iff_not_dvd.mpr
    intro d
    rw [show (12:ℕ)=2*(2*3) by decide] at d
    rcases h.1.dvd_mul.mp d with d|d
    · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) d
    · rcases h.1.dvd_mul.mp d with d|d
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) d
      · exact (Nat.not_dvd_of_pos_of_lt (by decide) h.2) d
  let z := Nat.chineseRemainder c r x.val
  have zp (p : ℕ) (hp : p∈S) : z.val ≡ a p [MOD p] :=
    (z.prop.2.of_dvd (Finset.dvd_prod_of_mem id hp)).trans (x.prop p hp)
  have zr : z.val.Coprime 12 := z.prop.1.gcd_eq.trans hr
  have zP : z.val.Coprime P := by
    apply Nat.coprime_prod_right_iff.mpr
    exact fun p hp => (zp p hp).gcd_eq.trans (ha p hp)
  have posP : 0 < P := Finset.prod_pos (fun p hp => (hs p hp).1.pos)
  obtain ⟨q, big, prime, same⟩ := Nat.forall_exists_prime_gt_and_modEq bound
    (mul_ne_zero (by decide : (12:ℕ)≠0) posP.ne') (zr.mul_right zP)
  exact ⟨q,big,prime,(same.of_dvd (dvd_mul_right _ _)).trans z.prop.1,
    fun p hp => (same.of_dvd (dvd_trans (Finset.dvd_prod_of_mem id hp)
      (dvd_mul_left P 12))).trans (zp p hp)⟩

private theorem representative {p : ℕ} (prime : p.Prime) (odd : p≠2) (b : Bool) :
    ∃ x : ℕ, x.Coprime p ∧ jacobiSym x p = (if b then -1 else 1) := by
  classical
  let _ : Fact p.Prime := ⟨prime⟩
  cases b with
  | false => exact ⟨1,by simp,by simp⟩
  | true =>
    obtain ⟨z,hz⟩ := FiniteField.exists_nonsquare (F:=ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have nz : z ≠ 0 := by
      intro he
      exact hz (he ▸ IsSquare.zero)
    have cp : z.val.Coprime p := prime.coprime_iff_not_dvd.mpr
      (by intro d; exact nz (by simpa using (ZMod.natCast_eq_zero_iff z.val p).mpr d)) |>.symm
    refine ⟨z.val,cp,ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr ?_⟩
    simpa using hz

/-- Each support symbol is an independent bit. The representative is chosen
before the Dirichlet prime, which may exceed any prescribed bound. -/
theorem prime_with_symbols (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ 3<p)
    (bits : ℕ → Bool) {r : ℕ} (hr : r.Coprime 12) (bound : ℕ) :
    ∃ q > bound, q.Prime ∧ q ≡ r [MOD 12] ∧
      ∀ p ∈ S, jacobiSym q p = (if bits p then -1 else 1) := by
  classical
  have choose_at (p : ℕ) (hp : p∈S) := representative (hs p hp).1
    (by have := (hs p hp).2; omega) (bits p)
  let a := fun p => if h : p∈S then (choose_at p h).choose else 1
  have spec (p : ℕ) (hp : p∈S) : (a p).Coprime p ∧
      jacobiSym (a p) p = (if bits p then -1 else 1) := by
    simpa only [a,dite_eq_left hp] using (choose_at p hp).choose_spec
  obtain ⟨q,hq,pr,ht,d⟩ := prime_in_classes S hs a (fun p hp => (spec p hp).1) hr bound
  refine ⟨q,hq,pr,ht,fun p hp => ?_⟩
  calc
    jacobiSym q p = jacobiSym (q % p : ℕ) p := by
      simpa only [Int.natCast_mod] using jacobiSym.mod_left (q:ℤ) p
    _ = jacobiSym ((a p) % p : ℕ) p := by rw [show q % p = a p % p from d p hp]
    _ = jacobiSym (a p) p := by
      simpa only [Int.natCast_mod] using (jacobiSym.mod_left (a p:ℤ) p).symm
    _ = _ := (spec p hp).2

end
end Sun28.AuxiliaryPrimes
#print axioms Sun28.AuxiliaryPrimes.prime_in_classes
#print axioms Sun28.AuxiliaryPrimes.prime_with_symbols
