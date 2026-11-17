import PrimePowers
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Sun28.ComparisonCRT
noncomputable section

structure Congruences (Lplus Lminus κ anchor : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) (h : ℤ) : Prop where
  plus : h ≡ 0 [ZMOD (Lplus:ℤ)]
  minus : h ≡ (anchor:ℤ) [ZMOD (Lminus:ℤ)]
  preparation : h ≡ 0 [ZMOD (κ:ℤ)]
  localResidue : ∀ p ∈ T, h ≡ (p:ℤ)^(a p) [ZMOD (p:ℤ)^(a p+1)]

private def exponent (plus minus κ : ℕ) (a : ℕ→ℕ) (p : ℕ) :=
  max (a p+1) (max (plus.factorization p) (max (minus.factorization p) (κ.factorization p)))

/-- The exponent product requires a local depth only at the designated primes. -/
private def schedule (plus minus κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) (p : ℕ) :=
  exponent plus minus κ (fun q=>if q∈T then a q else 0) p

private def residue (minus anchor : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) (p : ℕ) :=
  if p ∈ T then p^(a p) else if p∣minus then anchor else 0

/-- CRTa and CRTb together. The odd-prime hypotheses concern divisibility of
the two reduction orders. No pairwise consistency of the desired residues is assumed. -/
theorem comparison_progression (plus minus κ anchor : ℕ) (T : Finset ℕ) (a : ℕ→ℕ)
    (hp : 0<plus) (hm : 0<minus) (hk : 0<κ)
    (prime : ∀ p∈T, Nat.Prime p) (two : 2∈T)
    (gcd : plus.gcd minus=4) (v2p : padicValNat 2 plus=2) (v2m : padicValNat 2 minus=6)
    (localAvoid : ∀ p∈T, p≠2 → ¬p∣plus*minus)
    (kAvoid : ∀ p∈κ.primeFactors, p≠2 → ¬p∣minus)
    (depth : ∀ p∈T,padicValNat p κ≤a p) (dyadic : 6≤a 2) (anchor64 : 64∣anchor) :
    ∃ (h₀ : ℤ) (period : ℕ), 0<period ∧ ∀ k : ℤ,
      Congruences plus minus κ anchor T a (h₀+(period:ℤ)*k) := by
  classical
  let S := T ∪ (plus.primeFactors ∪ (minus.primeFactors ∪ κ.primeFactors))
  let e := schedule plus minus κ T a
  let r := residue minus anchor T a
  have allPrime (p : ℕ) (d : p∈S) : Nat.Prime p := by
    rcases Finset.mem_union.mp d with mem|d
    · exact prime p mem
    rcases Finset.mem_union.mp d with mem|d
    · exact Nat.prime_of_mem_primeFactors mem
    rcases Finset.mem_union.mp d with mem|mem <;> exact Nat.prime_of_mem_primeFactors mem
  have ep (p : ℕ) : plus.factorization p≤e p := by dsimp [e,schedule,exponent];omega
  have em (p : ℕ) : minus.factorization p≤e p := by dsimp [e,schedule,exponent];omega
  have ek (p : ℕ) : κ.factorization p≤e p := by dsimp [e,schedule,exponent];omega
  have ea (p : ℕ) (mem : p∈T) : a p+1≤e p := by simp only [e,schedule,exponent,ite_eq_left mem];omega
  obtain ⟨h₀,pos,all⟩:=prime_progression S e r allPrime
  refine ⟨h₀,_,pos,?_⟩
  intro k
  let h := h₀+((∏ p∈S,p^(e p):ℕ):ℤ)*k
  have useR (p j : ℕ) (mem : p∈S) (le : j≤e p) : h ≡ (r p:ℤ) [ZMOD (p:ℤ)^j] :=
    (all k p mem).of_dvd (pow_dvd_pow _ le)
  have useT (p j : ℕ) (mem : p∈T) (le : j≤e p) : h ≡ (p:ℤ)^(a p) [ZMOD (p:ℤ)^j] := by
    simpa only [r,residue,ite_eq_left mem,Nat.cast_pow] using useR p j (Finset.mem_union_left _ mem) le
  have zeroT (p j : ℕ) (mem : p∈T) (le : j≤a p) : h ≡ 0 [ZMOD (p:ℤ)^j] := by
    have e₀ := useT p j mem (le.trans ((Nat.le_succ _).trans (ea p mem)))
    exact e₀.trans (Int.modEq_zero_iff_dvd.mpr (pow_dvd_pow _ le))
  refine ⟨assemble hp.ne' ?_,assemble hm.ne' ?_,assemble hk.ne' ?_,fun p mem=>useT p _ mem (ea p mem)⟩
  · intro p mem
    have pp := Nat.prime_of_mem_primeFactors mem
    have div := Nat.dvd_of_mem_primeFactors mem
    by_cases is2 : p=2
    · subst p
      rw [Nat.factorization_def _ Nat.prime_two,v2p]
      exact zeroT 2 2 two (by omega)
    have noT : p∉T := fun t=>(localAvoid p t is2) (dvd_mul_of_dvd_left div _)
    have noM : ¬p∣minus := by
      intro dm
      have d4 := Nat.dvd_gcd div dm
      rw [gcd,show 4=(2:ℕ)^2 by decide] at d4
      exact is2 ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp (pp.dvd_of_dvd_pow d4))
    have incl : p∈S := Finset.mem_union_right _ (Finset.mem_union_left _ mem)
    simpa only [r,residue,ite_eq_right noT,ite_eq_right noM,Nat.cast_zero] using useR p _ incl (ep p)
  · intro p mem
    have div := Nat.dvd_of_mem_primeFactors mem
    by_cases is2 : p=2
    · subst p
      rw [Nat.factorization_def _ Nat.prime_two,v2m]
      have anchor : (anchor:ℤ) ≡ 0 [ZMOD (2:ℤ)^6] :=
        Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast (show 2^6 ∣ anchor from anchor64))
      exact (zeroT 2 6 two dyadic).trans anchor.symm
    have noT : p∉T := fun t=>(localAvoid p t is2) (dvd_mul_of_dvd_right div _)
    have incl : p∈S := Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ mem))
    simpa only [r,residue,ite_eq_right noT,ite_eq_left div] using useR p _ incl (em p)
  · intro p mem
    by_cases pat : p∈T
    · exact zeroT p _ pat ((Nat.factorization_def κ (prime p pat)) ▸ depth p pat)
    have odd : p≠2 := fun eq=>pat (eq ▸ two)
    have noM := kAvoid p mem odd
    have incl : p∈S := Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ mem))
    simpa only [r,residue,ite_eq_right pat,ite_eq_right noM,Nat.cast_zero] using useR p _ incl (ek p)

end
end Sun28.ComparisonCRT
#print axioms Sun28.ComparisonCRT.comparison_progression
