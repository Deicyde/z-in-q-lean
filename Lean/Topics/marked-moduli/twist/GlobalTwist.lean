import RationalClusters
import Mathlib.Data.Nat.Squarefree

/-! The single squarefree integer used to twist the rational sextic. -/
namespace ZInQBlueprint.GlobalTwist
open IsDiscreteValuationRing ZInQBlueprint.ResidueExtension ZInQBlueprint.ResidualFactors
open ZInQBlueprint.PadicParameters
open scoped BigOperators

/-- The signed homogeneous contact integer of the canonical reduced numerator and denominator. -/
def contactInteger (u : ℚ) : ℤ := contactProduct u.num (u.den : ℤ)

/-- The primes selected by the article. For a marked input the finite set is empty. -/
def support (u : ℚ) : Finset ℕ :=
  let n := (contactInteger u).natAbs
  n.primeFactors.filter fun p => 17 ≤ p ∧ n.factorization p % 4 = 2

def delta (u : ℚ) : ℕ := ∏ p ∈ support u, p

theorem mem_support (u : ℚ) (p : ℕ) :
    p ∈ support u ↔ 17 ≤ p ∧ (contactInteger u).natAbs.factorization p % 4 = 2 := by
  simp only [support, Finset.mem_filter]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro hz
  simp [hz] at h

private theorem prime_of_mem {u : ℚ} {q : ℕ} (h : q ∈ support u) : q.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1

theorem delta_pos (u : ℚ) : 0 < delta u :=
  Finset.prod_pos fun _ h => (prime_of_mem h).pos

theorem exponent (u : ℚ) (p : ℕ) :
    (delta u).factorization p = if p ∈ support u then 1 else 0 := by
  unfold delta
  rw [Nat.factorization_prod_apply (fun q h => (prime_of_mem h).ne_zero)]
  calc
    _ = ∑ q ∈ support u, if q=p then 1 else 0 := by
      refine Finset.sum_congr rfl fun q hq => ?_
      simp only [(prime_of_mem hq).factorization,Finsupp.single_apply]
    _ = _ := Finset.sum_ite_eq' _ _ (fun _ => 1)

theorem delta_squarefree (u : ℚ) : Squarefree (delta u) := by
  apply Nat.squarefree_of_factorization_le_one (delta_pos u).ne'
  intro p
  rw [exponent]
  split <;> decide

theorem primeFactors_delta (u : ℚ) : (delta u).primeFactors = support u := by
  ext p
  rw [← Nat.support_factorization,Finsupp.mem_support_iff,exponent]
  split <;> simp_all

/-- The selected squarefree integer divides the absolute homogeneous contact integer. -/
theorem delta_dvd_contact (u : ℚ) : delta u ∣ (contactInteger u).natAbs :=
  (Finset.prod_dvd_prod_of_subset _ _ (fun q : ℕ => q) (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd _)

theorem marked (u : ℚ) (h : contactInteger u=0) : delta u=1 := by
  simp [delta,support,h]

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p

theorem contact_cast (u : ℚ) : (contactInteger u : ℤ_[p]) = RationalClusters.F p u := by
  simp [contactInteger,RationalClusters.F,contactProduct]

private theorem unit_of_nondvd {n : ℕ} (h : ¬p ∣ n) : IsUnit (n : ℤ_[p]) := by
  have hmod : PadicInt.toZMod (n : ℤ_[p]) ≠ 0 := by
    rw [map_natCast, Ne,CharP.cast_eq_zero_iff (ZMod p) p]
    exact h
  rw [Ne, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hmod
  exact not_not.mp hmod

/-- In the normalized DVR valuation the exponent of a nonzero integer is its prime multiplicity. -/
theorem nat_valuation (n : ℕ) (hn : n ≠ 0) :
    addVal ℤ_[p] (n : ℤ_[p]) = (n.factorization p : ℕ∞) := by
  let m := n.factorization p
  let q := n / p^m
  have hu : IsUnit (q : ℤ_[p]) := unit_of_nondvd p (Nat.not_dvd_ordCompl Fact.out hn)
  apply addVal_def _ hu.unit PadicInt.irreducible_p
  rw [hu.unit_spec,mul_comm]
  exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self n p).symm

theorem contact_valuation (u : ℚ) (hn : contactInteger u ≠ 0) :
    addVal ℤ_[p] (RationalClusters.F p u) = ((contactInteger u).natAbs.factorization p : ℕ∞) := by
  rw [← contact_cast]
  let z := contactInteger u
  have h := nat_valuation p z.natAbs (by simpa [z] using hn)
  change addVal ℤ_[p] (z : ℤ_[p]) = _
  rcases Int.natAbs_eq z with hpos | hneg
  · have hz : (z : ℤ_[p]) = (z.natAbs : ℤ_[p]) := by
      simpa only [Int.cast_natCast] using congrArg (fun a : ℤ => (a : ℤ_[p])) hpos
    rw [hz]
    exact h
  · have hz : (z : ℤ_[p]) = -(z.natAbs : ℤ_[p]) := by
      simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun a : ℤ => (a : ℤ_[p])) hneg
    rw [hz,AddValuation.map_neg]
    exact h

/-- Both normalized valuations and factorizations refer to the same positive integer. -/
structure LocalTwist (u : ℚ) (n : ℕ) : Prop where
  padic_val : addVal ℤ_[p] (delta u : ℤ_[p]) = (n : ℕ∞)
  witt_val : addVal W (delta u : W) = (n : ℕ∞)
  padic_factor : ∃ e : ℤ_[p]ˣ, (delta u : ℤ_[p])=(p:ℤ_[p])^n*(e:ℤ_[p])
  witt_factor : ∃ e : Wˣ, (delta u : W)=(p:W)^n*(e:W)

private theorem local_of_exponent (u : ℚ) {n : ℕ} (h : (delta u).factorization p = n) :
    LocalTwist p u n := by
  let q := delta u / p^(delta u).factorization p
  have hq : IsUnit (q : ℤ_[p]) :=
    unit_of_nondvd p (Nat.not_dvd_ordCompl Fact.out (delta_pos u).ne')
  have hd : (delta u : ℤ_[p])=(p:ℤ_[p])^n*(hq.unit : ℤ_[p]) := by
    rw [hq.unit_spec,← h]
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self (delta u) p).symm
  let e : Wˣ := Units.map (fromPadics p).toMonoidHom hq.unit
  have hw : (delta u : W)=(p:W)^n*(e:W) := by
    change (delta u : W) = (p:W)^n * fromPadics p (hq.unit:ℤ_[p])
    simpa only [map_natCast,map_mul,map_pow] using
      congrArg (fromPadics p) hd
  exact ⟨nat_valuation p (delta u) (delta_pos u).ne' |>.trans (by rw [h]),
    addVal_def _ e (uniformizer p) _ (by rw [mul_comm]; exact hw),⟨hq.unit,hd⟩,⟨e,hw⟩⟩

theorem at_prime (u : ℚ) : LocalTwist p u (if p ∈ support u then 1 else 0) :=
  local_of_exponent p u (exponent u p)

theorem dvd_iff_mem (u : ℚ) : p ∣ delta u ↔ p ∈ support u := by
  rw [← primeFactors_delta, Nat.mem_primeFactors]
  simp [Fact.out, (delta_pos u).ne']

theorem support_at_depth (u : ℚ) (m : ℕ)
    (hv : addVal ℤ_[p] (RationalClusters.F p u) = (m : ℕ∞)) :
    p ∈ support u ↔ 17 ≤ p ∧ m%4=2 := by
  have hz : contactInteger u ≠ 0 := by
    intro h
    rw [← contact_cast, h, Int.cast_zero, addVal_zero] at hv
    simp at hv
  have he := ENat.natCast_inj.mp ((contact_valuation p u hz).symm.trans hv)
  rw [mem_support,he]

theorem at_depth (u : ℚ) (m : ℕ)
    (hv : addVal ℤ_[p] (RationalClusters.F p u) = (m : ℕ∞)) :
    LocalTwist p u (if 17 ≤ p ∧ m%4=2 then 1 else 0) := by
  simpa only [support_at_depth p u m hv] using at_prime p u

theorem even_contact (u : ℚ) (hp : 17 ≤ p) (k : ℕ)
    (hv : addVal ℤ_[p] (RationalClusters.F p u) = ((2*k : ℕ) : ℕ∞)) :
    LocalTwist p u (k%2) := by
  have h := at_depth p u (2*k) hv
  have he : (if 17 ≤ p ∧ (2*k)%4=2 then 1 else 0) = k%2 := by split <;> omega
  rwa [he] at h

theorem odd_contact (u : ℚ) (k : ℕ)
    (hv : addVal ℤ_[p] (RationalClusters.F p u) = ((2*k+1 : ℕ) : ℕ∞)) :
    LocalTwist p u 0 := by
  have hn : ¬ (2*k+1)%4=2 := by omega
  simpa [hn] using at_depth p u (2*k+1) hv

theorem ordinary (u : ℚ) (hv : addVal ℤ_[p] (RationalClusters.F p u)=0) :
    LocalTwist p u 0 := by
  simpa using at_depth p u 0 hv

theorem pole (u : ℚ) (hp : 11 ≤ p) (g : ℕ) (hg : 0 < g)
    (hv : addVal ℤ_[p] (RationalClusters.G p u) = (g : ℕ∞)) : LocalTwist p u 0 := by
  have hf := (pole_data hp (u.num:ℤ_[p]) (u.den:ℤ_[p]) (rational_primitive u) g hg hv).2.1
  exact ordinary p u (addVal_eq_zero_iff.mpr hf)

theorem below_cutoff (u : ℚ) (hp : p < 17) : LocalTwist p u 0 := by
  apply local_of_exponent
  simp [exponent, mem_support, Nat.not_le.mpr hp]

end ZInQBlueprint.GlobalTwist
#print axioms ZInQBlueprint.GlobalTwist.mem_support
#print axioms ZInQBlueprint.GlobalTwist.delta_pos
#print axioms ZInQBlueprint.GlobalTwist.exponent
#print axioms ZInQBlueprint.GlobalTwist.delta_squarefree
#print axioms ZInQBlueprint.GlobalTwist.primeFactors_delta
#print axioms ZInQBlueprint.GlobalTwist.delta_dvd_contact
#print axioms ZInQBlueprint.GlobalTwist.marked
#print axioms ZInQBlueprint.GlobalTwist.contact_cast
#print axioms ZInQBlueprint.GlobalTwist.nat_valuation
#print axioms ZInQBlueprint.GlobalTwist.contact_valuation
#print axioms ZInQBlueprint.GlobalTwist.at_prime
#print axioms ZInQBlueprint.GlobalTwist.dvd_iff_mem
#print axioms ZInQBlueprint.GlobalTwist.support_at_depth
#print axioms ZInQBlueprint.GlobalTwist.at_depth
#print axioms ZInQBlueprint.GlobalTwist.even_contact
#print axioms ZInQBlueprint.GlobalTwist.odd_contact
#print axioms ZInQBlueprint.GlobalTwist.ordinary
#print axioms ZInQBlueprint.GlobalTwist.pole
#print axioms ZInQBlueprint.GlobalTwist.below_cutoff
