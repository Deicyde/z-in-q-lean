import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-! All six marks simultaneously have private even prime factors at an arbitrarily large input. -/
namespace ZInQBlueprint.ContactDescent
open Finset

def mark : Fin 6 → ℕ := ![0,15,20,24,30,60]

theorem mark_bound (i : Fin 6) : mark i ≤ 60 := by fin_cases i <;> decide

theorem mark_injective : Function.Injective mark := by decide

/-- Specify one large prime for each mark and make all six contacts exactly two. -/
theorem six_congruences (p : Fin 6 → ℕ) (pp : ∀ i, (p i).Prime)
    (inj : Function.Injective p) (hp : ∀ i, 60 < p i) (H : ℕ) :
    ∃ u : ℕ, H < u ∧ ∀ i,
      (u+mark i).factorization (p i) = 2 ∧
      ∀ j : Fin 6, j ≠ i → ¬ p i ∣ u+mark j := by
  let m := fun i => (p i)^3
  let a := fun i => (p i)^2 - mark i
  have hm (i) : m i ≠ 0 := pow_ne_zero _ (pp i).ne_zero
  have co : Set.Pairwise (univ : Finset (Fin 6)) (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact (((Nat.coprime_primes (pp i) (pp j)).mpr (inj.ne hij)).pow_left _).pow_right _
  obtain ⟨u0,hu⟩ := Nat.chineseRemainderOfFinset a m univ (fun i _ => hm i) co
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (hm i))
  let u := u0 + (H+1)*M
  have hU : H < u := by dsimp [u]; nlinarith
  refine ⟨u,hU,?_⟩
  intro i
  have hmM : m i ∣ M := Finset.dvd_prod_of_mem m (mem_univ i)
  have hu1 : u ≡ u0 [MOD m i] := by
    unfold u
    have e := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hmM (H+1))
    simpa using e.add_left u0
  have h0 : mark i ≤ p i ^2 := by nlinarith [mark_bound i,hp i]
  have h : (u+mark i) ≡ (p i)^2 [MOD (p i)^3] := by
    simpa [a,Nat.sub_add_cancel h0] using (hu1.trans (hu i (mem_univ i))).add_right (mark i)
  have hd2 := (h.dvd_iff (pow_dvd_pow (p i) (show 2 ≤ 3 by decide))).mpr (dvd_refl ((p i)^2))
  have hd3 : ¬ (p i)^3 ∣ (u+mark i) := by
    intro h3
    have hh := (h.dvd_iff (dvd_refl _)).mp h3
    have lt : (p i)^2 < (p i)^3 := pow_lt_pow_right₀ (pp i).one_lt (by decide)
    exact (not_le_of_gt lt) (Nat.le_of_dvd (pow_pos (pp i).pos _) hh)
  have hn : u+mark i ≠ 0 := by omega
  have h2 := ((pp i).pow_dvd_iff_le_factorization hn).mp hd2
  have h3 := mt ((pp i).pow_dvd_iff_le_factorization hn).mpr hd3
  refine ⟨by omega,?_⟩
  intro j hji hj
  have hi : p i ∣ u+mark i := (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hd2
  have eqm : mark i ≡ mark j [MOD p i] := by
    apply Nat.ModEq.add_left_cancel' u
    exact (Nat.modEq_zero_iff_dvd.mpr hi).trans (Nat.modEq_zero_iff_dvd.mpr hj).symm
  have hi' := (mark_bound i).trans_lt (hp i)
  have hj' := (mark_bound j).trans_lt (hp i)
  change mark i % p i = mark j % p i at eqm
  rw [Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] at eqm
  exact hji (mark_injective eqm.symm)

/-- Both the forbidden primes and the common input can be chosen above any cutoff.
Every one of these six primes lies outside the odd contact support. -/
theorem arbitrarily_large_private_contacts (bound H : ℕ) :
    ∃ (p : Fin 6 → ℕ) (u : ℕ), Function.Injective p ∧ H < u ∧
      ∀ i, (p i).Prime ∧ max 60 bound < p i ∧
        (u+mark i).factorization (p i)=2 ∧
        ∀ j : Fin 6, j ≠ i → ¬ p i ∣ u+mark j := by
  let k := max 60 bound + 1
  let p := fun i : Fin 6 => Nat.nth Nat.Prime (k+i.val)
  have hs := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp (i) : (p i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hi : Function.Injective p := by
    intro i j h
    have e := hs.injective h
    exact Fin.ext (Nat.add_left_cancel e)
  have hb (i : Fin 6) : max 60 bound < p i := by
    change max 60 bound < Nat.nth Nat.Prime (k+i.val)
    exact (by dsimp [k]; omega : max 60 bound < k+i.val+2).trans_le (Nat.add_two_le_nth_prime _)
  obtain ⟨u,hu,hc⟩ := six_congruences p hp hi (fun i => (le_max_left ..).trans_lt (hb i)) H
  exact ⟨p,u,hi,hu,fun i => ⟨hp i,hb i,hc i⟩⟩

end ZInQBlueprint.ContactDescent
#print axioms ZInQBlueprint.ContactDescent.six_congruences
#print axioms ZInQBlueprint.ContactDescent.arbitrarily_large_private_contacts
