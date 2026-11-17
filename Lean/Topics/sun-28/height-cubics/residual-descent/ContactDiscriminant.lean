import InertialRoots
import Divisibility

/-! The actual field discriminant has exactly the two squareclasses' prime support at odd primes. -/
namespace Sun28.FiveDescent.ResidueField
open NumberField IntermediateField Sun28.Ordinary
noncomputable section

theorem odd_discr_iff {d e : ℤ} {r w : Omega} (sd : Squarefree d) (se : Squarefree e)
    (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega)) {p : ℕ} (pr : p.Prime) (odd : p≠2) :
    (p:ℤ)∣NumberField.discr (coords r w) ↔ p∣d.natAbs ∨ p∣e.natAbs := by
  constructor
  · intro h
    by_contra! n
    have nd : ¬(p:ℤ)∣d := fun v => n.1 (by simpa using Int.natAbs_dvd_natAbs.mpr v)
    have ne : ¬(p:ℤ)∣e := fun v => n.2 (by simpa using Int.natAbs_dvd_natAbs.mpr v)
    exact prime_not_dvd_discr hr hw pr odd nd ne h
  · have a : (AdjoinPair.gen₁ ℚ r w)^2=(d:coords r w) := Subtype.ext hr
    have b : (AdjoinPair.gen₂ ℚ r w)^2=(e:coords r w) := Subtype.ext hw
    exact fun v => v.elim (prime_dvd_discr sd a pr) (prime_dvd_discr se b pr)

/-- The prime divisors of the actual field discriminant outside exactly Glazer's cutoff. -/
def fieldPrimes (z v : Omega) : Finset ℕ :=
  (NumberField.discr (coords z v)).natAbs.primeFactors \ oldCutoff

theorem fieldPrimes_eq {d e : ℤ} {r w : Omega} (sd : Squarefree d) (se : Squarefree e)
    (hr : r^2=(d:Omega)) (hw : w^2=(e:Omega)) : fieldPrimes r w=twistPrimes d e := by
  let disc := NumberField.discr (coords r w)
  have dn : disc.natAbs≠0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero _)
  ext p
  simp only [fieldPrimes,twistPrimes,Finset.mem_sdiff]
  apply and_congr_left
  intro out
  have odd : p≠2 := fun eq => out (eq ▸ Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by decide : 2<76177),Nat.prime_two⟩)
  change p∈disc.natAbs.primeFactors ↔ p∈d.natAbs.primeFactors ∪ e.natAbs.primeFactors
  rw [Finset.mem_union]
  constructor
  · intro h
    have pr := Nat.prime_of_mem_primeFactors h
    have di : (p:ℤ)∣disc := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors h)
    exact ((odd_discr_iff sd se hr hw pr odd).mp di).imp
      (fun v=>Nat.mem_primeFactors.mpr ⟨pr,v,Int.natAbs_ne_zero.mpr sd.ne_zero⟩)
      (fun v=>Nat.mem_primeFactors.mpr ⟨pr,v,Int.natAbs_ne_zero.mpr se.ne_zero⟩)
  · intro h
    have pr : p.Prime := h.elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
    have di := (odd_discr_iff sd se hr hw pr odd).mpr
      (h.imp Nat.dvd_of_mem_primeFactors Nat.dvd_of_mem_primeFactors)
    exact Nat.mem_primeFactors.mpr ⟨pr,by simpa using Int.natAbs_dvd_natAbs.mpr di,dn⟩

theorem marked_field_primes {A B : ℤ} (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    {r w : Omega} (hr:r^2=(D A B:Omega)) (hw:w^2=(E A B:Omega)) :
    oldContactPrimes oldCutoff A B=fieldPrimes r w := by
  obtain ⟨sd,se,_⟩ := forward off
  exact (FiveDescent.support_exact cop off).trans (fieldPrimes_eq sd se hr hw).symm

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.odd_discr_iff
#print axioms Sun28.FiveDescent.ResidueField.fieldPrimes_eq
#print axioms Sun28.FiveDescent.ResidueField.marked_field_primes
