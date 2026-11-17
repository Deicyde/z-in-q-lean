import BonferroniRows

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

/-- Both signs are tested on every place, including the inert places. -/
def signedHit (A : Fin 3→ℚ) (p : ℕ) (z : ℕ×ℕ) : Prop :=
  ∃ i j : ↥(shifts A), splitEvent A p i j z

/-- Ordinary primeness and the two base rays leave a positive logarithmic weight. -/
theorem form_of_live {A : Fin 3→ℚ} {K : ℕ} {z : ℕ×ℕ}
    (live : patternWeight A K K z≠0) (i : ↥(shifts A)) :
    0≤form A z i ∧ commonPrime K K (form A z i).toNat := by
  by_contra h
  exact live (Finset.prod_eq_zero (f:=fun j : ↥(shifts A)=>primeWeight K K (form A z j))
    (Finset.mem_univ i) (ite_eq_right h))

private theorem form_eq {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Record A d H Y) (i : ↥(shifts A)) :
    (form A (pair a) i).toNat=a.values.value i := by
  have h : form A (pair a) i=(a.values.value i : ℤ) := (a.values.equation i i.property).symm
  rw [h,Int.toNat_natCast]

theorem signed_record {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Record A d H Y) {p κ : ℕ}
    [Fact p.Prime] (odd:p≠2) {T : Finset ℕ} (out:p∉T) (aux:p∉κ.primeFactors) :
    ¬signedHit A p (pair a) ↔ atPrime a.gaussian T κ p := by
  rw [atPrime_iff_fibre a T κ p odd out aux, fibre_obstructed_iff]
  unfold signedHit splitEvent
  simp_rw [form_eq a]
  have div (i : ↥(shifts A)) (s : Bool) :
      p∣adjacentNorm (a.gaussian i) s ↔ (p:ℤ)∣signedOrder (a.values.value i) s :=
    order_dvd_iff (a.values.prime i i.property) (a.rays.norm i) (a.rays.ray16 i) (a.rays.ray7 i) s p
  simp_rw [div]

/-- Outside the fixed determinant primes, the previous rational inert class contains
all actual obstructed rows. The implication holds for every oriented prime tuple. -/
theorem accepted_hit {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Record A d H Y)
    {p : ℕ} [Fact p.Prime] (pos:0<d) (large:exceptionalBound A d<p) :
    signedHit A p (pair a) → obstruction A p (pair a) := by
  intro hit
  by_cases inert : p%4=3
  · have no : ¬atPrime a.gaussian ∅ 1 p := by
      intro good
      exact ((signed_record a (by omega) (by simp) (by simp)).mpr good) hit
    have forced : (a.u:ZMod p)=1 ∧ (a.v:ZMod p)=0 := by
      by_contra clear
      exact no (inert_atPrime a pos large inert (by simp) (by simp) clear)
    simpa [obstruction,inert,inertEvent,pair] using forced
  · simpa [obstruction,inert,signedHit] using hit

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.form_of_live
#print axioms Sun28.CommonRows.signed_record
#print axioms Sun28.CommonRows.accepted_hit