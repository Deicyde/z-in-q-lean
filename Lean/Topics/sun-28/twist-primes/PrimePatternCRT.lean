import SimplePrimeRoots
import Mathlib.Data.Nat.ChineseRemainder

namespace Sun28.TwistPrimes

/-- Prescribe order one in the first factor at all primes in S while assigning
the index the residues zero modulo 6D and one modulo β. -/
theorem prescribed_index {β D : ℕ} (hb : 0<β) (hd : 0<D)
    (b6 : β.Coprime 6) (bd : β.Coprime D)
    (S : Finset ℕ) (split : ∀ p ∈ S, SplitRoot β p) (avoid : ∀ p ∈ S, ¬p∣D) :
    ∃ k : ℕ, β<k^2 ∧ 6∣k ∧ D∣k ∧ β.Coprime k ∧ ∀ p ∈ S, SimpleRoot β p k := by
  classical
  let A := 6*D
  let s := fun p : ℕ => p^2
  let a := fun p : ℕ => if mem : p∈S then Classical.choose (simple_root (split p mem)) else 0
  have spec (p : ℕ) (mem : p∈S) : SimpleRoot β p (a p) := by
    simpa only [a,dite_eq_left mem] using Classical.choose_spec (simple_root (split p mem))
  have pair : Set.Pairwise (↑S) (fun p q => Nat.Coprime (s p) (s q)) := by
    intro p hp q hq ne
    have prime := (split p hp).1
    have cp : p.Coprime q := prime.coprime_iff_not_dvd.mpr
      (fun d=>ne ((Nat.prime_dvd_prime_iff_eq prime (split q hq).1).mp d))
    exact (cp.pow_left _).pow_right _
  let x := Nat.chineseRemainderOfFinset a s S
    (fun p m => pow_ne_zero 2 (split p m).1.ne_zero) pair
  let P := ∏ j ∈ S,s j
  have prodpos : 0<P := Finset.prod_pos (fun p m=>pow_pos (split p m).1.pos 2)
  have co : (A*β).Coprime P := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p mem
    have z := split p mem
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply z.1.coprime_iff_not_dvd.mpr
    intro div
    rcases z.1.dvd_mul.mp div with dA | db
    · rcases z.1.dvd_mul.mp dA with d6 | dD
      · exact z.2.1 (dvd_mul_of_dvd_left d6 _)
      · exact avoid p mem dD
    · exact z.2.1 (dvd_mul_of_dvd_right db 6)
  let first := Nat.chineseRemainder (b6.mul_right bd).symm 0 1
  let z := Nat.chineseRemainder co first.val x.val
  let E := (A*β)*P
  let k := z.val+(β+1)*E
  have posE : 0<E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hd) hb) prodpos
  have lower : β<k := by
    have h := Nat.mul_le_mul_left (β+1) (show 1≤E by omega)
    dsimp only [k]
    omega
  have mov : k ≡ z.val [MOD E] := Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl _)
  have full : k ≡ first.val [MOD (A*β)] := (mov.of_dvd (dvd_mul_right _ _)).trans z.prop.1
  have dA : A∣k := Nat.modEq_zero_iff_dvd.mp
    ((full.of_dvd (dvd_mul_right _ _)).trans first.prop.1)
  have be : k ≡ 1 [MOD β] := (full.of_dvd (dvd_mul_left _ _)).trans first.prop.2
  have cp : k.Coprime β := by simpa [Nat.Coprime] using be.gcd_eq
  refine ⟨k,by nlinarith,dvd_trans (dvd_mul_right _ _) dA,dvd_trans (dvd_mul_left _ _) dA,cp.symm,?_⟩
  intro p m
  have d : s p∣P := Finset.dvd_prod_of_mem s m
  have fullP : k ≡ x.val [MOD P] := (mov.of_dvd (dvd_mul_left _ _)).trans z.prop.2
  have sel : k^2 ≡ (a p)^2 [MOD p^2] := ((fullP.of_dvd d).trans (x.prop p m)).pow 2
  obtain ⟨shallow,deep⟩ := spec p m
  exact ⟨(sel.of_dvd (dvd_pow_self p (by decide : 2≠0))).trans shallow,
    fun h => deep (sel.symm.trans h)⟩

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.prescribed_index
